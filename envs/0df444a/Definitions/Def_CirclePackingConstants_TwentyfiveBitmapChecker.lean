-- Prove2me | Definitions.Def_CirclePackingConstants_TwentyfiveBitmapChecker
-- name    : CirclePackingConstants_TwentyfiveBitmapChecker
-- status  : Definition
-- author  : @kylelyk
-- created : 2026-11-27T06:01:13.611297+00:00
-- url     : https://prove2.me/theorems/da206c3b-8d03-4c66-add2-cb4d032853e7
-- title:
--   Bitmap region-elimination checker for infeasible cell patterns of 25 points, with soundness
-- statement:
--   A reflective checker for the infeasibility of cell patterns $(a,b)$ in the sense of `CirclePackingConstants_TwentyfiveNogoods`, together with its soundness proof. It is the exact-arithmetic analogue of the "active area" reduction of Nurmela and Östergård.
--
--   **Regions.** Each cell of side $1/5$ is divided into $32\times32$ lattice squares of side $1/160$. A pattern gets one *slot* per required point: the point of a single cell, or the lower-half point and the upper-half point of a double cell (two points of one cell more than $1/4$ apart differ by more than $3/20$ in the second coordinate, so one lies in each half). The *region* of a slot is the set of lattice squares that may still contain its point, stored as a bitmap inside one natural number.
--
--   **Elimination step.** Two lattice squares with offsets $(\Delta u,\Delta v)$ are *far* if
--
--   $$(|\Delta u|+1)^2+(|\Delta v|+1)^2>40^2 ,$$
--
--   which is necessary for them to contain two points at distance greater than $1/4=40/160$. A step names a source slot and a target slot of different points in cells at most two apart, and deletes from the target region every square that is far from no square of the source region. One step is a single multiplication of the source bitmap by a table of far offsets.
--
--   **Certificates.** A certificate (`Cert`) is a binary tree: after a prescribed sequence of steps either some region is empty (`dead`), or one region is split into two parts and both parts are refuted by subtrees (`split`).
--
--   **Soundness.** The main statements are
--
--   $$\texttt{refuted}\ a\ b\ ns\ pos\ c=\texttt{true}\ \Longrightarrow\ \texttt{Infeasible}\ a\ b\qquad(b\subseteq a),$$
--
--   and `batch_sound`: if `batchOK lo G = true` for a list `G` of certificates, then the entries of the library `nogoods` with indices $lo,\dots,lo+|G|-1$ are infeasible.
--
--   The checker is evaluated by the Lean kernel (`decide +kernel`) in the proofs of `twentyfive_nogood_batch1`–`twentyfive_nogood_batch6`.
--
--   **Formalization Note** The state packs all regions into one natural number, slot $k$ in bits $32768k,\dots,32768(k+1)-1$; square $(u,v)$ of a region is bit $11(u+94v)$, so that the product with the table of far offsets has one $11$-bit field per target square that counts the far source squares. The soundness theorems are part of the file because every batch proof needs them; they use only the standard axioms.
-- source:
--   Original computer-generated decomposition of CirclePackingConstants.twentyfive_missing_cell_halfbox_bound (the occupancy step, §1 of G. Wengerodt, Die dichteste Packung von 25 Kreisen in einem Quadrat, Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 30 (1987) 3–15, https://annalesm.elte.hu/annales30-1987/Annales_1987_T-XXX.pdf). Method after K. J. Nurmela, P. R. J. Östergård, More optimal packings of equal circles in a square, Discrete Comput. Geom. 22 (1999) 439–457, https://doi.org/10.1007/PL00009472, §2.2–2.4 (tile combinations and region elimination), carried out here with exact integer arithmetic. The statement is not quoted from either paper.

import Definitions.Def_CirclePackingConstants_TwentyfiveNogoods

/-!
# Bitmap region-elimination checker for the 25-point nogood patterns

Each cell of side `1/5` is divided into `32 × 32` lattice squares (160 per unit length; two points are more
than `1/4` apart only if their lattice squares are "far": `(|Δu| + 1)^2 + (|Δv| + 1)^2 > 1600`).
A pattern `(a, b)` gets one *slot* per point: the point of a single cell, or the lower-half and the
upper-half point of a double cell. The region of a slot is a bitmap of the lattice squares where its point
may still lie: square `(u, v)` is alive iff bit `11 * (u + 94 * v)` is set. A state packs the regions of all
slots into one natural number, slot `k` in bits `32768 k .. 32768 (k + 1) - 1`.

A propagation step multiplies the region of a source slot by a table of far offsets and deletes from the
target slot every square that is far from no alive source square. A certificate (`Cert`) is a binary tree:
run some steps, then either some slot is empty (`dead`) or the region of a slot is split in two (`split`).
`refuted a b ns pos c = true` implies `Twentyfive.Infeasible a b` (`refuted_sound`), and `batchOK lo G = true`
implies that the library entries `lo .. lo + G.length - 1` are infeasible (`batch_sound`).
-/

noncomputable section

namespace CirclePackingConstants
namespace Twentyfive
namespace Bitmap


/-- Evaluate `x` to a literal before passing it on. -/
def force {α : Type} (x : Nat) (k : Nat → α) : α := Nat.rec (k 0) (fun p _ => k (Nat.succ p)) x

/-- `ones k = 1 + 2048 + ... + 2048^(k-1)`. -/
def ones (k : Nat) : Nat := Nat.div (Nat.sub (Nat.pow 2048 k) 1) 2047
/-- Lowest bit of the first field of each of the rows `0 .. k-1` (row stride 94 fields). -/
def rowOnes (k : Nat) : Nat := Nat.div (Nat.sub (Nat.pow 2048 (Nat.mul 94 k)) 1) (Nat.sub (Nat.pow 2048 94) 1)
def FULL : Nat := Nat.mul (rowOnes 32) (ones 32)
def LOWER : Nat := Nat.mul (rowOnes 16) (ones 32)
def UPPER : Nat := Nat.sub FULL LOWER
def MADD : Nat := Nat.mul 1023 (ones 8836)

/-- Largest `r` with `r^2 + d^2 ≤ 1600`, for `d = 0 .. 40`, in 6-bit fields. -/
def RTAB : Nat := 0x20c3d14d559865a6dc75e7e08218a28e39249659669a69a79e79e79e79e8
def rad (d : Nat) : Nat := Nat.land (Nat.shiftRight RTAB (Nat.mul 6 d)) 63

/-- Row `b` of the far table for offset `(ex, ey)`: fields `a < 63` with
`(|a + 32 ex - 95| + 1)^2 + (|b + 32 ey - 95| + 1)^2 > 1600`. -/
def tabRow (ex ey b : Nat) : Nat :=
  -- dy + 1 = |b + 32 ey - 95| + 1
  let d := Nat.succ (Nat.add (Nat.sub (Nat.add b (Nat.mul 32 ey)) 95) (Nat.sub 95 (Nat.add b (Nat.mul 32 ey))))
  cond (Nat.ble 41 d) (ones 63)
    -- near columns: |a + 32 ex - 95| + 1 ≤ rad d, i.e. 96 - rad d ≤ a + 32 ex ≤ 94 + rad d
    (let lo := Nat.sub (Nat.sub 96 (rad d)) (Nat.mul 32 ex)
     let hi := Nat.min 63 (Nat.sub (Nat.add 95 (rad d)) (Nat.mul 32 ex))
     Nat.sub (ones 63) (Nat.sub (ones hi) (ones (Nat.min lo hi))))

def tabAcc (ex ey : Nat) : Nat → Nat → Nat
  | 0, acc => acc
  | b+1, acc => tabAcc ex ey b (Nat.add (Nat.mul acc (Nat.pow 2048 94)) (tabRow ex ey b))

def mkTab (ex ey : Nat) : Nat := tabAcc ex ey 63 0
def T00 : Nat := mkTab 0 0
def T01 : Nat := mkTab 0 1
def T02 : Nat := mkTab 0 2
def T03 : Nat := mkTab 0 3
def T04 : Nat := mkTab 0 4
def T10 : Nat := mkTab 1 0
def T11 : Nat := mkTab 1 1
def T12 : Nat := mkTab 1 2
def T13 : Nat := mkTab 1 3
def T14 : Nat := mkTab 1 4
def T20 : Nat := mkTab 2 0
def T21 : Nat := mkTab 2 1
def T22 : Nat := mkTab 2 2
def T23 : Nat := mkTab 2 3
def T24 : Nat := mkTab 2 4
def T30 : Nat := mkTab 3 0
def T31 : Nat := mkTab 3 1
def T32 : Nat := mkTab 3 2
def T33 : Nat := mkTab 3 3
def T34 : Nat := mkTab 3 4
def T40 : Nat := mkTab 4 0
def T41 : Nat := mkTab 4 1
def T42 : Nat := mkTab 4 2
def T43 : Nat := mkTab 4 3
def T44 : Nat := mkTab 4 4
def tab (ex ey : Nat) : Nat := Nat.rec (Nat.rec T00 (fun i _ => Nat.rec T01 (fun i _ => Nat.rec T02 (fun i _ => Nat.rec T03 (fun _ _ => T04) i) i) i) ey) (fun i _ => Nat.rec (Nat.rec T10 (fun i _ => Nat.rec T11 (fun i _ => Nat.rec T12 (fun i _ => Nat.rec T13 (fun _ _ => T14) i) i) i) ey) (fun i _ => Nat.rec (Nat.rec T20 (fun i _ => Nat.rec T21 (fun i _ => Nat.rec T22 (fun i _ => Nat.rec T23 (fun _ _ => T24) i) i) i) ey) (fun i _ => Nat.rec (Nat.rec T30 (fun i _ => Nat.rec T31 (fun i _ => Nat.rec T32 (fun i _ => Nat.rec T33 (fun _ _ => T34) i) i) i) ey) (fun _ _ => (Nat.rec T40 (fun i _ => Nat.rec T41 (fun i _ => Nat.rec T42 (fun i _ => Nat.rec T43 (fun _ _ => T44) i) i) i) ey)) i) i) i) ex

/-- Slot width in bits: slot `k` of a packed state occupies bits `32768 k .. 32768 (k+1) - 1`. -/
def R : Nat := Nat.pow 2 32768

/-- Slot descriptor `k` of the packed list `pos` (8 bits each): `128 low + 64 layer + 8 i + j`. -/
def slotE (pos k : Nat) : Nat := Nat.mod (Nat.shiftRight pos (Nat.mul 8 k)) 256

def kill (S kt flag tb src tgt : Nat) : Nat :=
  Nat.sub S (Nat.shiftLeft (Nat.mul (Nat.mul flag (Nat.sub 1 (Nat.sub 1 src)))
    (Nat.sub tgt (Nat.land tgt (Nat.shiftRight (Nat.add (Nat.mul tb src) MADD) 32405)))) (Nat.mul 32768 kt))
/-- `es`, `et`: descriptors mod 128 of source and target slot; `t = 5 ex + ey`. The flag is 1 iff the target
cell is the source cell shifted by `(ex - 2, ey - 2)` and the two slots denote different points. -/
def stepF (S kt t es et src : Nat) : Nat :=
  kill S kt
    (Nat.mul
      (Nat.sub 1 (Nat.add
        (Nat.sub (Nat.add (Nat.add (Nat.mod es 64) t) (Nat.mul 3 (Nat.div t 5))) (Nat.add (Nat.mod et 64) 18))
        (Nat.sub (Nat.add (Nat.mod et 64) 18) (Nat.add (Nat.add (Nat.mod es 64) t) (Nat.mul 3 (Nat.div t 5))))))
      (Nat.sub 1 (Nat.sub 1 (Nat.add (Nat.sub es et) (Nat.sub et es)))))
    (tab (Nat.div t 5) (Nat.mod t 5)) src (Nat.mod (Nat.shiftRight S (Nat.mul 32768 kt)) R)
def stepE (S pos ks kt t : Nat) : Nat :=
  stepF S kt t (Nat.mod (Nat.shiftRight pos (Nat.mul 8 ks)) 128) (Nat.mod (Nat.shiftRight pos (Nat.mul 8 kt)) 128)
    (Nat.mod (Nat.shiftRight S (Nat.mul 32768 ks)) R)
/-- One step; digit `d = (32 ks + kt) 25 + t`. -/
def stepD (S pos d : Nat) : Nat := stepE S pos (Nat.div d 800) (Nat.mod (Nat.div d 25) 32) (Nat.mod d 25)

/-- Run `n` steps; step number `s` (from 0) uses the 15-bit digit number `n - 1 - s` of `code`. -/
def runCode (n S pos code : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun S => S)
    (fun m ih S => ih (stepD S pos (Nat.mod (Nat.shiftRight code (Nat.mul 15 m)) 32768))) n S

/-- Squares of a region with column `< m` (`ax = 0`) or row `< m` (`ax = 1`). -/
def lowPart (r ax m : Nat) : Nat :=
  cond (Nat.beq ax 0) (Nat.land r (Nat.mul (rowOnes 32) (ones m)))
    (Nat.mod r (Nat.pow 2048 (Nat.mul 94 m)))

/-- Refutation tree. `dead n code k`: after `n` steps slot `k` is empty.
`split n code k ax m lo hi`: after `n` steps split the region of slot `k` at `m` along axis `ax`. -/
inductive Cert where
  | dead : Nat → Nat → Nat → Cert
  | split : Nat → Nat → Nat → Nat → Nat → Cert → Cert → Cert

def chk (ns pos : Nat) : Cert → Nat → Bool
  | .dead n code k, S =>
      and (Nat.blt k ns) (Nat.beq (Nat.mod (Nat.shiftRight (runCode n S pos code) (Nat.mul 32768 k)) R) 0)
  | .split n code k ax m lo hi, S =>
      force (runCode n S pos code) (fun S1 => force (Nat.mod (Nat.shiftRight S1 (Nat.mul 32768 k)) R) (fun r =>
        force (lowPart r ax m) (fun lp =>
          and (chk ns pos lo (Nat.sub S1 (Nat.shiftLeft (Nat.sub r lp) (Nat.mul 32768 k))))
              (chk ns pos hi (Nat.sub S1 (Nat.shiftLeft lp (Nat.mul 32768 k)))))))

/-- Initial region of a slot with descriptor `e`: whole cell, lower half or upper half. -/
def initReg (e : Nat) : Nat :=
  Nat.rec FULL (fun q _ => Nat.rec UPPER (fun q _ => Nat.rec LOWER (fun _ _ => UPPER) q) q) (Nat.div e 64)
def initS (pos ns : Nat) : Nat :=
  Nat.rec 0 (fun k acc => Nat.add acc (Nat.shiftLeft (initReg (slotE pos k)) (Nat.mul 32768 k))) ns
/-- The slot descriptor names a cell of the board whose point exists in the pattern `(a, b)`. -/
def slotOK (a b e : Nat) : Bool :=
  and (and (Nat.ble (Nat.mod (Nat.div e 8) 8) 4) (Nat.ble (Nat.mod e 8) 4))
    (Nat.testBit (cond (Nat.beq (Nat.div e 64) 0) a b) (Nat.add (Nat.mul 5 (Nat.mod (Nat.div e 8) 8)) (Nat.mod e 8)))
def slotsOK (a b pos ns : Nat) : Bool :=
  Nat.rec true (fun k ih => and ih (slotOK a b (slotE pos k))) ns

/-- The pattern `(a, b)` is refuted by the slot list `(ns, pos)` and the tree `c`. -/
def refuted (a b ns pos : Nat) (c : Cert) : Bool := and (slotsOK a b pos ns) (chk ns pos c (initS pos ns))

/-- Every pattern `(a, b)` of `L` has `b ⊆ a` and is refuted by the certificate at the same position of `G`. -/
def refutedAll : List (Nat × Nat) → List (Nat × Nat × Cert) → Bool
  | _, [] => true
  | [], _ :: _ => false
  | x :: xs, g :: gs =>
      and (and (Nat.beq (Nat.land x.1 x.2) x.2) (refuted x.1 x.2 g.1 g.2.1 g.2.2)) (refutedAll xs gs)

/-- The library entries `lo, lo + 1, ...` are refuted by the certificates of `G`, in this order. -/
def batchOK (lo : Nat) (G : List (Nat × Nat × Cert)) : Bool := refutedAll (nogoods.drop lo) G

/-! ## Soundness -/

open Finset

theorem force_eq {α : Type} (x : Nat) (k : Nat → α) : force x k = k x := by
  cases x <;> rfl

theorem nmul (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem beq_land {a b : ℕ} (h : Nat.beq (Nat.land a b) a = true) : a &&& b = a :=
  Nat.eq_of_beq_eq_true h

theorem blt_pow {a c n : ℕ} (h : Nat.blt a (Nat.pow c n) = true) : a < c ^ n :=
  Nat.le_of_ble_eq_true h

/-! ### Base 2048 digits -/

theorem sum_shift (f : ℕ → ℕ) (m : ℕ) :
    ∑ e ∈ range (m + 1), f e * 2048 ^ e = f 0 + 2048 * ∑ e ∈ range m, f (e + 1) * 2048 ^ e := by
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring

theorem digit_sum (s : ℕ) : ∀ (f : ℕ → ℕ) (m : ℕ), (∀ e, f e < 2048) → s < m →
    (∑ e ∈ range m, f e * 2048 ^ e) / 2048 ^ s % 2048 = f s := by
  induction s with
  | zero =>
    intro f m hf hs
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [sum_shift, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0)]
  | succ s ih =>
    intro f m hf hs
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [sum_shift, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by norm_num),
      Nat.div_eq_of_lt (hf 0), zero_add]
    exact ih (fun e => f (e + 1)) m (fun e => hf _) (by omega)

theorem base_expand (m : ℕ) : ∀ n : ℕ, n < 2048 ^ m →
    n = ∑ e ∈ range m, (n / 2048 ^ e % 2048) * 2048 ^ e := by
  induction m with
  | zero => intro n h; simpa using h
  | succ m ih =>
    intro n h
    rw [sum_shift]
    have h2 : n / 2048 < 2048 ^ m := by
      apply Nat.div_lt_of_lt_mul; rwa [pow_succ'] at h
    have h3 := ih (n / 2048) h2
    have h4 : ∑ e ∈ range m, (n / 2048 ^ (e + 1) % 2048) * 2048 ^ e = n / 2048 := by
      conv_rhs => rw [h3]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [pow_succ', Nat.div_div_eq_div_mul]
    rw [h4, pow_zero, Nat.div_one]
    omega

theorem ones_eq (k : ℕ) : ones k = ∑ e ∈ range k, 1 * 2048 ^ e := by
  simp only [one_mul]
  exact (Nat.geomSum_eq (by norm_num) k).symm

theorem madd_gen (n : ℕ) : 1023 * ones n =
    ∑ e ∈ range (n + 1), (if e < n then 1023 else 0) * 2048 ^ e := by
  rw [ones_eq, Finset.mul_sum, Finset.sum_range_succ, if_neg (lt_irrefl _), zero_mul, add_zero]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [if_pos (Finset.mem_range.1 he), one_mul]

theorem MADD_eq : MADD = ∑ e ∈ range 8837, (if e < 8836 then 1023 else 0) * 2048 ^ e := by
  have h : MADD = 1023 * ones 8836 := by unfold MADD; rw [nmul]
  exact h.trans (madd_gen 8836)

theorem pow2048 (e : ℕ) : 2048 ^ e = 2 ^ (11 * e) := by
  rw [pow_mul]; norm_num

theorem and_digit (a b e : ℕ) :
    (a &&& b) / 2048 ^ e % 2048 = (a / 2048 ^ e % 2048) &&& (b / 2048 ^ e % 2048) := by
  rw [pow2048, show (2048 : ℕ) = 2 ^ 11 by norm_num]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  cases decide (i < 11) <;> simp

theorem digit_of_clean (M e : ℕ) (hM : M &&& ones 8836 = M) (he : e < 8836) :
    M / 2048 ^ e % 2048 = if M.testBit (11 * e) = true then 1 else 0 := by
  have h1 : ones 8836 / 2048 ^ e % 2048 = 1 := by
    rw [ones_eq]; exact digit_sum e (fun _ => 1) 8836 (fun _ => by norm_num) he
  have h2 := and_digit M (ones 8836) e
  rw [hM, h1, Nat.and_one_is_mod] at h2
  have h3 : M.testBit (11 * e) = decide (M / 2 ^ (11 * e) % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq
  rw [h3, ← pow2048]
  have h4 : M / 2048 ^ e % 2048 % 2 = M / 2048 ^ e % 2 := Nat.mod_mod_of_dvd _ (by norm_num)
  split_ifs with h <;> simp at h <;> omega

theorem prod_expand (x μ : ℕ → ℕ) (mK mP : ℕ) :
    (∑ i ∈ range mK, x i * 2048 ^ i) * (∑ j ∈ range mP, μ j * 2048 ^ j) =
      ∑ e ∈ range (mK + mP),
        (∑ q ∈ (range mK ×ˢ range mP) with q.1 + q.2 = e, x q.1 * μ q.2) * 2048 ^ e := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product',
    ← Finset.sum_fiberwise_of_maps_to (g := fun q : ℕ × ℕ => q.1 + q.2) (t := range (mK + mP))]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← (Finset.mem_filter.1 hq).2]; ring
  · intro q hq
    simp only [Finset.mem_product, Finset.mem_range] at hq ⊢
    omega

theorem coef_ge (x μ : ℕ → ℕ) (mK mP k t : ℕ) (hk : k < mK) (ht : t < mP) :
    x k * μ t ≤ ∑ q ∈ (range mK ×ˢ range mP) with q.1 + q.2 = k + t, x q.1 * μ q.2 := by
  have hmem : (k, t) ∈ (range mK ×ˢ range mP).filter (fun q : ℕ × ℕ => q.1 + q.2 = k + t) := by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨hk, ht⟩, rfl⟩
  exact Finset.single_le_sum (f := fun q : ℕ × ℕ => x q.1 * μ q.2) (fun _ _ => Nat.zero_le _) hmem

/-- A coefficient of the product counts pairs whose second index is a nonzero field of `μ`; these fields
lie in a `32 × 32` block. -/
theorem coef_le (x μ : ℕ → ℕ) (hx : ∀ i, x i ≤ 1) (hμ : ∀ i, μ i ≤ 1)
    (hμ0 : ∀ j, μ j ≠ 0 → j % 94 < 32 ∧ j / 94 < 32) (mK mP e : ℕ) :
    ∑ q ∈ (range mK ×ˢ range mP) with q.1 + q.2 = e, x q.1 * μ q.2 ≤ 1024 := by
  calc ∑ q ∈ (range mK ×ˢ range mP) with q.1 + q.2 = e, x q.1 * μ q.2
      ≤ ∑ q ∈ (range mK ×ˢ range mP) with q.1 + q.2 = e, (if μ q.2 ≠ 0 then 1 else 0) := by
        refine Finset.sum_le_sum fun q _ => ?_
        split_ifs with h
        · calc x q.1 * μ q.2 ≤ 1 * 1 := Nat.mul_le_mul (hx _) (hμ _)
            _ = 1 := rfl
        · rw [not_not] at h; rw [h, mul_zero]
    _ = (((range mK ×ˢ range mP).filter (fun q => q.1 + q.2 = e)).filter
          (fun q => μ q.2 ≠ 0)).card := by
        rw [Finset.card_filter]
    _ ≤ (range 32 ×ˢ range 32).card := by
        refine Finset.card_le_card_of_injOn (fun q => (q.2 % 94, q.2 / 94)) ?_ ?_
        · intro q hq
          have hq' := (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).2
          have := hμ0 _ hq'
          simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
          exact this
        · intro q hq q' hq' h
          have h1 := (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hq)).1).2
          have h2 := (Finset.mem_filter.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hq')).1).2
          have h3 : q.2 % 94 = q'.2 % 94 := congrArg Prod.fst h
          have h4 : q.2 / 94 = q'.2 / 94 := congrArg Prod.snd h
          ext <;> omega
    _ = 1024 := by simp

theorem lt_of_testBit (X k m : ℕ) (hX : X < 2048 ^ m) (hk : X.testBit (11 * k) = true) : k < m := by
  by_contra h
  have h1 : X < 2 ^ (11 * k) := by
    refine lt_of_lt_of_le hX ?_
    rw [pow2048]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.testBit_lt_two_pow h1] at hk
  exact absurd hk (by simp)

/-! ### Table facts checked by the kernel -/

def allLt (n : Nat) (f : Nat → Bool) : Bool := Nat.rec true (fun i ih => and (f i) ih) n

theorem allLt_iff (n : ℕ) (f : ℕ → Bool) : allLt n f = true ↔ ∀ i, i < n → f i = true := by
  induction n with
  | zero => simp [allLt]
  | succ n ih =>
    have e : allLt (n + 1) f = (f n && allLt n f) := rfl
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h2 i h
      · rw [h]; exact h1
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

def sumLt (n : Nat) (g : Nat → Nat) : Nat := Nat.rec 0 (fun i ih => Nat.add (g i) ih) n

theorem sumLt_zero (n : ℕ) (g : ℕ → ℕ) (h : sumLt n g = 0) : ∀ i, i < n → g i = 0 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    have e : sumLt (n + 1) g = g n + sumLt n g := rfl
    rw [e] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h1 | h1
    · exact ih (by omega) i h1
    · rw [h1]; omega

/-- `|x - 95|` on natural numbers. -/
def ad95 (x : Nat) : Nat := Nat.add (Nat.sub x 95) (Nat.sub 95 x)

/-- `(|a + 32 ex - 95| + 1)^2 + (|b + 32 ey - 95| + 1)^2`: squares with offsets `a = x - u + 31`,
`b = y - v + 31` in cells with offset `(ex - 2, ey - 2)` are *far* if this exceeds 1600. -/
def dist2 (ex ey a b : Nat) : Nat :=
  Nat.add (Nat.pow (Nat.succ (ad95 (Nat.add a (Nat.mul 32 ex)))) 2)
    (Nat.pow (Nat.succ (ad95 (Nat.add b (Nat.mul 32 ey)))) 2)

/-- The table is a clean bitmap and has no field `(a, b)` that is far but not set (their number is summed);
`dy2` is the row part of `dist2` and `Tb` is row `b` of the table. -/
def tabCheck1 (ex ey : Nat) : Bool :=
  force (tab ex ey) fun T =>
    and (and (Nat.beq (Nat.land T (ones 8836)) T) (Nat.blt T (Nat.pow 2048 5891)))
      (Nat.beq (sumLt 63 fun b =>
        force (Nat.pow (Nat.succ (Nat.add (Nat.sub (Nat.add b (Nat.mul 32 ey)) 95)
            (Nat.sub 95 (Nat.add b (Nat.mul 32 ey))))) 2) fun dy2 =>
          force (Nat.land (Nat.shiftRight T (Nat.mul 1034 b)) (Nat.sub (Nat.pow 2 693) 1)) fun Tb =>
            sumLt 63 fun a =>
              Nat.mul (Nat.sub 1 (Nat.sub 1601 (Nat.add (Nat.pow (Nat.succ (Nat.add
                  (Nat.sub (Nat.add a (Nat.mul 32 ex)) 95) (Nat.sub 95 (Nat.add a (Nat.mul 32 ex))))) 2)
                  dy2)))
                (Nat.sub 1 (Nat.land 1 (Nat.shiftRight Tb (Nat.mul 11 a))))) 0)

def tabCheck : Bool := allLt 5 fun ex => allLt 5 fun ey => tabCheck1 ex ey

theorem tabCheck_ok : tabCheck = true := by decide +kernel

theorem bit_spec (T i : ℕ) (h : Nat.sub 1 (Nat.land 1 (Nat.shiftRight T i)) = 0) :
    T.testBit i = true := by
  have e : Nat.sub 1 (Nat.land 1 (Nat.shiftRight T i)) = 1 - (1 &&& (T >>> i)) := rfl
  rw [e, Nat.one_and_eq_mod_two] at h
  rw [Nat.testBit_eq_decide_div_mod_eq, ← Nat.shiftRight_eq_div_pow, decide_eq_true_eq]
  omega

set_option exponentiation.threshold 40000 in
theorem tab_spec (ex ey : ℕ) (hex : ex < 5) (hey : ey < 5) :
    tab ex ey &&& ones 8836 = tab ex ey ∧ tab ex ey < 2048 ^ 5891 ∧
      ∀ a b, a < 63 → b < 63 → 1600 < dist2 ex ey a b →
        (tab ex ey).testBit (11 * (a + 94 * b)) = true := by
  have h := tabCheck_ok
  unfold tabCheck at h
  rw [allLt_iff] at h
  have h1 := h ex hex
  rw [allLt_iff] at h1
  have h2 := h1 ey hey
  unfold tabCheck1 at h2
  rw [force_eq, Bool.and_eq_true, Bool.and_eq_true] at h2
  obtain ⟨⟨h3, h4⟩, h5⟩ := h2
  refine ⟨beq_land h3, blt_pow (a := tab ex ey) (c := 2048) (n := 5891) h4, ?_⟩
  intro a b ha hb hf
  have h6 := sumLt_zero _ _ (Nat.eq_of_beq_eq_true h5) b hb
  rw [force_eq, force_eq] at h6
  have h7 := sumLt_zero _ _ h6 a ha
  have e : (1 - (1601 - dist2 ex ey a b)) * Nat.sub 1 (Nat.land 1 (Nat.shiftRight
      (Nat.land (Nat.shiftRight (tab ex ey) (Nat.mul 1034 b)) (Nat.sub (Nat.pow 2 693) 1))
      (Nat.mul 11 a))) = 0 := h7
  rw [show 1 - (1601 - dist2 ex ey a b) = 1 by omega, one_mul] at e
  have h8 := bit_spec _ _ e
  have e2 : Nat.land (Nat.shiftRight (tab ex ey) (Nat.mul 1034 b)) (Nat.sub (Nat.pow 2 693) 1) =
      (tab ex ey >>> (1034 * b)) &&& Nat.sub (Nat.pow 2 693) 1 := rfl
  rw [e2, Nat.testBit_and, Bool.and_eq_true, Nat.testBit_shiftRight] at h8
  rw [show 11 * (a + 94 * b) = 1034 * b + 11 * a by omega]
  exact h8.1

def fullCheck : Bool :=
  force FULL fun F =>
    and (and (Nat.beq (Nat.land F (ones 8836)) F) (Nat.blt F (Nat.pow 2048 2946)))
      (and (allLt 2946 fun e => or (not (Nat.testBit F (Nat.mul 11 e)))
            (and (Nat.blt (Nat.mod e 94) 32) (Nat.blt (Nat.div e 94) 32)))
        (allLt 32 fun u => allLt 32 fun v => Nat.testBit F (Nat.mul 11 (Nat.add u (Nat.mul 94 v)))))

theorem fullCheck_ok : fullCheck = true := by decide +kernel

def halfCheck : Bool :=
  and (and (Nat.beq (Nat.land LOWER FULL) LOWER) (Nat.beq (Nat.land UPPER FULL) UPPER))
    (allLt 32 fun u => allLt 16 fun v =>
      and (Nat.testBit LOWER (Nat.mul 11 (Nat.add u (Nat.mul 94 v))))
        (Nat.testBit UPPER (Nat.mul 11 (Nat.add u (Nat.mul 94 (Nat.add v 16))))))

theorem halfCheck_ok : halfCheck = true := by decide +kernel

set_option exponentiation.threshold 40000 in
theorem FULL_spec : FULL &&& ones 8836 = FULL ∧ FULL < 2048 ^ 2946 ∧
    (∀ e, e < 2946 → FULL.testBit (11 * e) = true → e % 94 < 32 ∧ e / 94 < 32) ∧
    ∀ u v, u < 32 → v < 32 → FULL.testBit (11 * (u + 94 * v)) = true := by
  have h := fullCheck_ok
  unfold fullCheck at h
  rw [force_eq, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨beq_land h1, blt_pow (a := FULL) (c := 2048) (n := 2946) h2, ?_, ?_⟩
  · intro e he hb
    rw [allLt_iff] at h3
    have h5 := h3 e he
    have hb' : Nat.testBit FULL (Nat.mul 11 e) = true := hb
    rw [hb'] at h5
    have h6 : (Nat.blt (Nat.mod e 94) 32 && Nat.blt (Nat.div e 94) 32) = true := h5
    rw [Bool.and_eq_true] at h6
    exact ⟨Nat.le_of_ble_eq_true h6.1, Nat.le_of_ble_eq_true h6.2⟩
  · intro u v hu hv
    rw [allLt_iff] at h4
    have h5 := h4 u hu
    rw [allLt_iff] at h5
    exact h5 v hv

theorem FULL_dig (e : ℕ) (h : FULL.testBit (11 * e) = true) : e % 94 < 32 ∧ e / 94 < 32 :=
  FULL_spec.2.2.1 e (lt_of_testBit FULL e 2946 FULL_spec.2.1 h) h

theorem half_spec : LOWER &&& FULL = LOWER ∧ UPPER &&& FULL = UPPER ∧
    (∀ u v, u < 32 → v < 16 → LOWER.testBit (11 * (u + 94 * v)) = true) ∧
    ∀ u v, u < 32 → 16 ≤ v → v < 32 → UPPER.testBit (11 * (u + 94 * v)) = true := by
  have h := halfCheck_ok
  unfold halfCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h4 : ∀ u v, u < 32 → v < 16 → LOWER.testBit (11 * (u + 94 * v)) = true ∧
      UPPER.testBit (11 * (u + 94 * (v + 16))) = true := by
    intro u v hu hv
    rw [allLt_iff] at h3
    have h5 := h3 u hu
    rw [allLt_iff] at h5
    have h6 := h5 v hv
    rw [Bool.and_eq_true] at h6
    exact h6
  refine ⟨beq_land h1, beq_land h2, fun u v hu hv => (h4 u v hu hv).1, ?_⟩
  intro u v hu hv1 hv2
  have := (h4 u (v - 16) hu (by omega)).2
  rwa [Nat.sub_add_cancel hv1] at this

/-! ### The product step -/

/-- If `X` has field `k` set and `M ⊆ FULL` has field `t` set, the field `k + t` of the product is
nonzero, so its flag bit survives the shift. -/
theorem survive (X M k t e : ℕ) (hX : X &&& ones 8836 = X) (hXlt : X < 2048 ^ 5891)
    (hM : M &&& FULL = M) (hk : X.testBit (11 * k) = true) (ht : M.testBit (11 * t) = true)
    (hkt : k + t = e + 2945) : ((X * M + MADD) >>> 32405).testBit (11 * e) = true := by
  have hMc : M &&& ones 8836 = M := by
    rw [← hM, Nat.and_assoc, FULL_spec.1]
  have hMlt : M < 2048 ^ 2946 := by
    rw [← hM]; exact lt_of_le_of_lt Nat.and_le_right FULL_spec.2.1
  have hbit : ∀ i, M.testBit i = true → FULL.testBit i = true := by
    intro i hi
    rw [← hM, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.2
  have hk' := lt_of_testBit X k _ hXlt hk
  have ht' := lt_of_testBit M t _ hMlt ht
  set x : ℕ → ℕ := fun i => if X.testBit (11 * i) = true then 1 else 0 with hx
  set μ : ℕ → ℕ := fun i => if M.testBit (11 * i) = true then 1 else 0 with hμ
  have hXe : X = ∑ i ∈ range 5891, x i * 2048 ^ i := by
    conv_lhs => rw [base_expand 5891 X hXlt]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [digit_of_clean X i hX (by have := Finset.mem_range.1 hi; omega)]
  have hMe : M = ∑ i ∈ range 2946, μ i * 2048 ^ i := by
    conv_lhs => rw [base_expand 2946 M hMlt]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [digit_of_clean M i hMc (by have := Finset.mem_range.1 hi; omega)]
  set c : ℕ → ℕ := fun e => ∑ q ∈ (range 5891 ×ˢ range 2946) with q.1 + q.2 = e, x q.1 * μ q.2
    with hc
  have hprod : X * M = ∑ e ∈ range 8837, c e * 2048 ^ e := by
    conv_lhs => rw [hXe, hMe]
    exact prod_expand x μ 5891 2946
  have hx1 : ∀ i, x i ≤ 1 := fun i => by simp only [hx]; split_ifs <;> simp
  have hμ1 : ∀ i, μ i ≤ 1 := fun i => by simp only [hμ]; split_ifs <;> simp
  have hμ0 : ∀ j, μ j ≠ 0 → j % 94 < 32 ∧ j / 94 < 32 := by
    intro j hj
    apply FULL_dig
    apply hbit
    by_contra hb
    exact hj (by simp only [hμ]; rw [if_neg hb])
  have hcle : ∀ e, c e ≤ 1024 := fun e => coef_le x μ hx1 hμ1 hμ0 5891 2946 e
  have hc1 : 1 ≤ c (k + t) := by
    have hxk : x k = 1 := by simp [hx, hk]
    have hμt : μ t = 1 := by simp [hμ, ht]
    have h1 := coef_ge x μ 5891 2946 k t hk' ht'
    rw [hxk, hμt] at h1
    exact h1
  have hY : X * M + MADD = ∑ e ∈ range 8837, (c e + if e < 8836 then 1023 else 0) * 2048 ^ e := by
    rw [hprod, MADD_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have hdig : (X * M + MADD) / 2048 ^ (k + t) % 2048 = c (k + t) + 1023 := by
    rw [hY, digit_sum (k + t) (fun e => c e + if e < 8836 then 1023 else 0) 8837
      (fun e => by have := hcle e; split_ifs <;> omega) (by omega)]
    rw [if_pos (by omega)]
  rw [Nat.testBit_shiftRight, Nat.testBit_eq_decide_div_mod_eq]
  have he : 32405 + 11 * e = 11 * (k + t) + 10 := by omega
  rw [he, pow_add, ← pow2048, ← Nat.div_div_eq_div_mul]
  have := hcle (k + t)
  simp only [decide_eq_true_eq]
  generalize (X * M + MADD) / 2048 ^ (k + t) = z at hdig
  omega

/-! ### Packed slots -/

theorem slot_mod (M X j : ℕ) : X / M ^ j % M = X % (M ^ j * M) / M ^ j :=
  (Nat.mod_mul_right_div_self _ _ _).symm

theorem slot_hi (M S n j : ℕ) (hM : 0 < M) (hS : S < M ^ n) (hj : n ≤ j) : S / M ^ j % M = 0 := by
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hS (Nat.pow_le_pow_right hM hj)), Nat.zero_mod]

theorem slot_sub (M S D k j : ℕ) (hM : 0 < M) (hD : D ≤ S / M ^ k % M) :
    (S - D * M ^ k) / M ^ j % M = if j = k then S / M ^ k % M - D else S / M ^ j % M := by
  have hP : 0 < M ^ k := Nat.pow_pos hM
  have hDT : D ≤ S / M ^ k := le_trans hD (Nat.mod_le _ _)
  have hDS : D * M ^ k ≤ S := le_trans (Nat.mul_le_mul_right _ hDT) (Nat.div_mul_le_self _ _)
  have h1 : (S - D * M ^ k) / M ^ k = S / M ^ k - D := by
    rw [mul_comm]; exact Nat.sub_mul_div _ _ _
  have h2 : (S / M ^ k - D) / M = S / M ^ k / M ∧ (S / M ^ k - D) % M = S / M ^ k % M - D := by
    generalize S / M ^ k = T at hD hDT
    have hlt : T % M - D < M := lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ hM)
    have e : T - D = (T % M - D) + M * (T / M) := by
      have := Nat.mod_add_div T M
      generalize M * (T / M) = w at this ⊢
      generalize T % M = z at this hD ⊢
      omega
    rw [e]
    constructor
    · rw [Nat.add_mul_div_left _ _ hM, Nat.div_eq_of_lt hlt, zero_add]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rcases lt_trichotomy j k with h | h | h
  · rw [if_neg (by omega), slot_mod, slot_mod M S]
    congr 1
    obtain ⟨i, rfl⟩ : ∃ i, k = j + 1 + i := ⟨k - j - 1, by omega⟩
    have e : D * M ^ (j + 1 + i) = (M ^ j * M) * (D * M ^ i) := by
      rw [pow_add, pow_succ]; ring
    rw [e] at hDS ⊢
    exact Nat.sub_mul_mod hDS
  · subst h; rw [if_pos rfl, h1]; exact h2.2
  · rw [if_neg (by omega)]
    obtain ⟨i, rfl⟩ : ∃ i, j = k + 1 + i := ⟨j - k - 1, by omega⟩
    have e : M ^ (k + 1 + i) = M ^ k * (M * M ^ i) := by
      rw [pow_add, pow_succ]; ring
    rw [e]
    simp only [← Nat.div_div_eq_div_mul]
    rw [h1, h2.1]

theorem slot_add (M A r n : ℕ) (hM : 0 < M) (hA : A < M ^ n) (hr : r < M) :
    A + r * M ^ n < M ^ (n + 1) ∧ (A + r * M ^ n) / M ^ n % M = r ∧
      ∀ j, j < n → (A + r * M ^ n) / M ^ j % M = A / M ^ j % M := by
  refine ⟨?_, ?_, ?_⟩
  · calc A + r * M ^ n < M ^ n + r * M ^ n := by omega
      _ = (r + 1) * M ^ n := by ring
      _ ≤ M * M ^ n := Nat.mul_le_mul_right _ hr
      _ = M ^ (n + 1) := by ring
  · rw [Nat.add_mul_div_right _ _ (Nat.pow_pos hM), Nat.div_eq_of_lt hA, zero_add,
      Nat.mod_eq_of_lt hr]
  · intro j hj
    rw [slot_mod, slot_mod M A]
    congr 1
    obtain ⟨i, rfl⟩ : ∃ i, n = j + 1 + i := ⟨n - j - 1, by omega⟩
    have e : r * M ^ (j + 1 + i) = (M ^ j * M) * (r * M ^ i) := by
      rw [pow_add, pow_succ]; ring
    rw [e, Nat.add_mul_mod_self_left]

/-! ### Slots of a packed state -/

theorem npow (a b : ℕ) : Nat.pow a b = a ^ b := rfl

set_option exponentiation.threshold 40000 in
theorem R_eq : R = 2 ^ 32768 := by unfold R; exact npow 2 32768

theorem npow_pos (a b : ℕ) (h : 0 < a) : 0 < Nat.pow a b := Nat.pow_pos h

set_option exponentiation.threshold 40000 in
theorem R_pos : 0 < R := by unfold R; exact npow_pos 2 32768 (by norm_num)

theorem pow_le_aux (m n : ℕ) (h : 11 * m ≤ n) : 2048 ^ m ≤ 2 ^ n := by
  rw [pow2048]; exact Nat.pow_le_pow_right (by norm_num) h

/-- Region of slot `k` of the packed state `S`. -/
def slot (S k : ℕ) : ℕ := S / R ^ k % R

theorem pow_R (k : ℕ) : 2 ^ (32768 * k) = R ^ k := by rw [R_eq, pow_mul]

theorem slot_eq (S k : ℕ) : Nat.mod (Nat.shiftRight S (Nat.mul 32768 k)) R = slot S k := by
  have e : Nat.mod (Nat.shiftRight S (Nat.mul 32768 k)) R = (S >>> (32768 * k)) % R := rfl
  rw [e, Nat.shiftRight_eq_div_pow, pow_R]; rfl

theorem shl_eq (D k : ℕ) : Nat.shiftLeft D (Nat.mul 32768 k) = D * R ^ k := by
  have e : Nat.shiftLeft D (Nat.mul 32768 k) = D <<< (32768 * k) := rfl
  rw [e, Nat.shiftLeft_eq, pow_R]

theorem slot_upd (S D k j : ℕ) (hD : D ≤ slot S k) :
    slot (S - D * R ^ k) j = if j = k then slot S k - D else slot S j :=
  slot_sub R S D k j R_pos hD

theorem and_eq_iff (a b : ℕ) : a &&& b = a ↔ ∀ i, a.testBit i = true → b.testBit i = true := by
  constructor
  · intro h i hi
    rw [← h, Nat.testBit_and, Bool.and_eq_true] at hi
    exact hi.2
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := h i
    rw [Nat.testBit_and]
    revert this
    cases a.testBit i <;> cases b.testBit i <;> simp

theorem add_eq_or (a : ℕ) : ∀ b, a &&& b = 0 → a + b = a ||| b := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b h
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · subst h0; rw [Nat.zero_add, Nat.zero_or]
    have h2 := ih (a / 2) (Nat.div_lt_self h0 (by norm_num)) (b / 2)
      (by rw [← Nat.and_div_two, h])
    have h3 : ¬ (a % 2 = 1 ∧ b % 2 = 1) := by
      rw [← Nat.and_mod_two_eq_one, h]; norm_num
    have h4 : (a ||| b) / 2 = a / 2 ||| b / 2 := Nat.or_div_two
    have h5 := @Nat.or_mod_two_eq_one a b
    omega

theorem sub_submask (r lp : ℕ) (h : lp &&& r = lp) : r - lp = r ^^^ lp := by
  have hb := (and_eq_iff lp r).1 h
  have h0 : lp &&& (r ^^^ lp) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    have := hb i
    rw [Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit]
    revert this
    cases lp.testBit i <;> cases r.testBit i <;> simp
  have h1 : lp ||| (r ^^^ lp) = r := by
    apply Nat.eq_of_testBit_eq
    intro i
    have := hb i
    rw [Nat.testBit_or, Nat.testBit_xor]
    revert this
    cases lp.testBit i <;> cases r.testBit i <;> simp
  have h2 : lp + (r ^^^ lp) = r := by rw [add_eq_or _ _ h0, h1]
  omega

theorem xor_submask (r lp F : ℕ) (h : lp &&& r = lp) (hr : r &&& F = r) :
    (r ^^^ lp) &&& F = r ^^^ lp := by
  rw [and_eq_iff] at h hr ⊢
  intro i
  have h1 := h i
  have h2 := hr i
  rw [Nat.testBit_xor]
  revert h1 h2
  cases lp.testBit i <;> cases r.testBit i <;> cases F.testBit i <;> simp

theorem lowPart_sub (r ax m : ℕ) : lowPart r ax m &&& r = lowPart r ax m := by
  rw [and_eq_iff]
  intro i
  unfold lowPart
  cases Nat.beq ax 0
  · have e : cond false (Nat.land r (Nat.mul (rowOnes 32) (ones m)))
        (Nat.mod r (Nat.pow 2048 (Nat.mul 94 m))) = r % 2 ^ (11 * (94 * m)) := by
      rw [← pow2048]; rfl
    rw [e, Nat.testBit_mod_two_pow, Bool.and_eq_true]
    exact fun h => h.2
  · have e : cond true (Nat.land r (Nat.mul (rowOnes 32) (ones m)))
        (Nat.mod r (Nat.pow 2048 (Nat.mul 94 m))) = r &&& Nat.mul (rowOnes 32) (ones m) := rfl
    rw [e, Nat.testBit_and, Bool.and_eq_true]
    exact fun h => h.1

/-! ### One step -/

theorem kill_eq (S kt flag tb src tgt : ℕ) : kill S kt flag tb src tgt =
    S - (flag * (1 - (1 - src)) * (tgt - (tgt &&& ((tb * src + MADD) >>> 32405)))) * R ^ kt := by
  unfold kill; rw [shl_eq]; rfl

theorem kill_cases (S kt f1 f2 tb src tgt : ℕ) (h1 : f1 ≤ 1) (h2 : f2 ≤ 1) :
    kill S kt (f1 * f2) tb src tgt = S ∨ (f1 = 1 ∧ f2 = 1 ∧ src ≠ 0 ∧
      kill S kt (f1 * f2) tb src tgt =
        S - (tgt - (tgt &&& ((tb * src + MADD) >>> 32405))) * R ^ kt) := by
  rw [kill_eq]
  rcases Nat.eq_zero_or_pos src with h | h
  · left; subst h
    rw [Nat.sub_zero, Nat.sub_self, mul_zero, zero_mul, zero_mul, Nat.sub_zero]
  have h3 : 1 - (1 - src) = 1 := by omega
  rw [h3, mul_one]
  rcases Nat.eq_zero_or_pos f1 with h4 | h4
  · left; rw [h4, zero_mul, zero_mul, zero_mul, Nat.sub_zero]
  rcases Nat.eq_zero_or_pos f2 with h5 | h5
  · left; rw [h5, mul_zero, zero_mul, zero_mul, Nat.sub_zero]
  have h6 : f1 = 1 := by omega
  have h7 : f2 = 1 := by omega
  right
  refine ⟨h6, h7, by omega, ?_⟩
  rw [h6, h7, one_mul, one_mul]

theorem flag1 (A B : ℕ) (h : 1 - ((A - B) + (B - A)) = 1) : A = B := by omega

theorem flag2 (a b : ℕ) (h : 1 - (1 - ((a - b) + (b - a))) = 1) : a ≠ b := by omega

theorem stepF_cases (S kt t es et src : ℕ) :
    stepF S kt t es et src = S ∨
      (es % 64 + t + 3 * (t / 5) = et % 64 + 18 ∧ es ≠ et ∧ src ≠ 0 ∧
        stepF S kt t es et src = S - (slot S kt -
          (slot S kt &&& ((tab (t / 5) (t % 5) * src + MADD) >>> 32405))) * R ^ kt) := by
  have e : stepF S kt t es et src = kill S kt
      ((1 - ((es % 64 + t + 3 * (t / 5) - (et % 64 + 18)) +
          ((et % 64 + 18) - (es % 64 + t + 3 * (t / 5))))) *
        (1 - (1 - ((es - et) + (et - es)))))
      (tab (t / 5) (t % 5)) src (slot S kt) := by
    unfold stepF; rw [slot_eq]; rfl
  rw [e]
  rcases kill_cases S kt _ _ (tab (t / 5) (t % 5)) src (slot S kt) (Nat.sub_le _ _)
    (Nat.sub_le _ _) with h | ⟨h1, h2, h3, h4⟩
  · left; exact h
  · right; exact ⟨flag1 _ _ h1, flag2 _ _ h2, h3, h4⟩

theorem sl128 (pos k : ℕ) : Nat.mod (Nat.shiftRight pos (Nat.mul 8 k)) 128 = slotE pos k % 128 := by
  have e : slotE pos k = Nat.shiftRight pos (Nat.mul 8 k) % 256 := rfl
  rw [e, Nat.mod_mod_of_dvd _ (by norm_num : 128 ∣ 256)]; rfl

theorem stepD_eq (S pos d : ℕ) : stepD S pos d =
    stepF S (d / 25 % 32) (d % 25) (slotE pos (d / 800) % 128) (slotE pos (d / 25 % 32) % 128)
      (slot S (d / 800)) := by
  unfold stepD stepE; rw [slot_eq, sl128, sl128]; rfl

/-! ### Geometry -/

open CirclePackingConstants

/-- The point scaled by 160 lies in the lattice square `(u, v)` of cell `(i, j)`. -/
def InSq (P : Point) (i j u v : ℕ) : Prop :=
  32 * (i : ℝ) + u ≤ 160 * P.1 ∧ 160 * P.1 ≤ 32 * (i : ℝ) + u + 1 ∧
  32 * (j : ℝ) + v ≤ 160 * P.2 ∧ 160 * P.2 ≤ 32 * (j : ℝ) + v + 1

theorem ad95_le (x : ℕ) : x ≤ 95 + ad95 x ∧ 95 ≤ x + ad95 x := by
  show x ≤ 95 + ((x - 95) + (95 - x)) ∧ 95 ≤ x + ((x - 95) + (95 - x))
  omega

/-- Points in squares that are not far are at distance at most `1/4`. Source cell `(si, sj)`, square
`(u, v)`; target cell `(ti, tj) = (si + ex - 2, sj + ey - 2)`, square `(x, y)`. -/
theorem close_of_not_far (ex ey si sj ti tj u v x y : ℕ) (hex : si + ex = ti + 2)
    (hey : sj + ey = tj + 2) (hu : u < 32) (hv : v < 32)
    (hfar : ¬ 1600 < dist2 ex ey (x + 31 - u) (y + 31 - v)) (Ps Pt : Point)
    (hs : InSq Ps si sj u v) (ht : InSq Pt ti tj x y) : sqDist Ps Pt ≤ 1 / 16 := by
  have h1 := ad95_le (x + 31 - u + 32 * ex)
  have h2 := ad95_le (y + 31 - v + 32 * ey)
  have e : dist2 ex ey (x + 31 - u) (y + 31 - v) =
      (ad95 (x + 31 - u + 32 * ex) + 1) ^ 2 + (ad95 (y + 31 - v + 32 * ey) + 1) ^ 2 := rfl
  rw [e] at hfar
  generalize ad95 (x + 31 - u + 32 * ex) = n1 at h1 hfar
  generalize ad95 (y + 31 - v + 32 * ey) = n2 at h2 hfar
  have e1 : x + 32 * ex ≤ 64 + u + n1 := by omega
  have e2 : 64 + u ≤ x + 32 * ex + n1 := by omega
  have e3 : y + 32 * ey ≤ 64 + v + n2 := by omega
  have e4 : 64 + v ≤ y + 32 * ey + n2 := by omega
  have e1r : (x : ℝ) + 32 * ex ≤ 64 + u + n1 := by exact_mod_cast e1
  have e2r : (64 : ℝ) + u ≤ x + 32 * ex + n1 := by exact_mod_cast e2
  have e3r : (y : ℝ) + 32 * ey ≤ 64 + v + n2 := by exact_mod_cast e3
  have e4r : (64 : ℝ) + v ≤ y + 32 * ey + n2 := by exact_mod_cast e4
  have hexr : (si : ℝ) + ex = ti + 2 := by exact_mod_cast hex
  have heyr : (sj : ℝ) + ey = tj + 2 := by exact_mod_cast hey
  have hsumr : ((n1 : ℝ) + 1) ^ 2 + ((n2 : ℝ) + 1) ^ 2 ≤ 1600 := by
    exact_mod_cast not_lt.1 hfar
  obtain ⟨q1, q2, q3, q4⟩ := hs
  obtain ⟨p1, p2, p3, p4⟩ := ht
  have hx : (160 * Ps.1 - 160 * Pt.1) ^ 2 ≤ ((n1 : ℝ) + 1) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have hy : (160 * Ps.2 - 160 * Pt.2) ^ 2 ≤ ((n2 : ℝ) + 1) ^ 2 :=
    sq_le_sq' (by linarith) (by linarith)
  have hring : (160 * Ps.1 - 160 * Pt.1) ^ 2 + (160 * Ps.2 - 160 * Pt.2) ^ 2 =
      25600 * sqDist Ps Pt := by unfold sqDist; ring
  linarith

theorem exists_sq (lo hi : ℕ) (hlh : lo < hi) (y : ℝ) (h0 : (lo : ℝ) ≤ y) (h1 : y ≤ hi) :
    ∃ v : ℕ, lo ≤ v ∧ v < hi ∧ (v : ℝ) ≤ y ∧ y ≤ v + 1 := by
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg lo) h0
  by_cases h : y < hi
  · exact ⟨⌊y⌋₊, Nat.le_floor h0, (Nat.floor_lt hy0).2 h, Nat.floor_le hy0,
      (Nat.lt_floor_add_one y).le⟩
  · have hy : y = hi := le_antisymm h1 (not_lt.1 h)
    refine ⟨hi - 1, by omega, by omega, ?_, ?_⟩
    · rw [hy]; exact_mod_cast Nat.sub_le hi 1
    · rw [hy]
      have : hi ≤ hi - 1 + 1 := by omega
      exact_mod_cast this

/-! ### Invariant -/

/-- The point of the slot with descriptor `e`. -/
def ptOf (q : ℕ → ℕ → Point) (e : ℕ) : Point := q (5 * (e / 8 % 8) + e % 8) (e / 64 % 2)

/-- `P` lies in an alive square of the region `r` of a slot with descriptor `e`. -/
def Holds (P : Point) (e r : ℕ) : Prop :=
  ∃ u v, u < 32 ∧ v < 32 ∧ r.testBit (11 * (u + 94 * v)) = true ∧ InSq P (e / 8 % 8) (e % 8) u v

/-- Slots `≥ ns` are empty; the region of every slot `< ns` is a set of lattice squares of the cell, one of
which contains the point of the slot. -/
def Inv (q : ℕ → ℕ → Point) (ns pos S : ℕ) : Prop :=
  S < R ^ ns ∧ ∀ k, k < ns → slot S k &&& FULL = slot S k ∧
    Holds (ptOf q (slotE pos k)) (slotE pos k) (slot S k)

/-- The slots name cells of the board, and slots with different descriptors mod 128 hold points more than
`1/4` apart. -/
def Good (q : ℕ → ℕ → Point) (ns pos : ℕ) : Prop :=
  ∀ k, k < ns → slotE pos k / 8 % 8 ≤ 4 ∧ slotE pos k % 8 ≤ 4 ∧
    ∀ k', k' < ns → slotE pos k % 128 ≠ slotE pos k' % 128 →
      1 / 16 < sqDist (ptOf q (slotE pos k)) (ptOf q (slotE pos k'))

theorem inv_upd {q : ℕ → ℕ → Point} {ns pos S : ℕ} (hI : Inv q ns pos S) (k D : ℕ)
    (hD : D ≤ slot S k)
    (h : k < ns → (slot S k - D) &&& FULL = slot S k - D ∧
      Holds (ptOf q (slotE pos k)) (slotE pos k) (slot S k - D)) :
    Inv q ns pos (S - D * R ^ k) := by
  refine ⟨lt_of_le_of_lt (Nat.sub_le _ _) hI.1, fun j hj => ?_⟩
  rw [slot_upd S D k j hD]
  split_ifs with hjk
  · subst hjk; exact h hj
  · exact hI.2 j hj

theorem d64 (e : ℕ) : e % 128 % 64 = 8 * (e / 8 % 8) + e % 8 := by omega

theorem d128 (e : ℕ) : e % 128 = 64 * (e / 64 % 2) + (8 * (e / 8 % 8) + e % 8) := by omega

theorem cell_rel (si sj ti tj t : ℕ) (hsj : sj ≤ 4) (htj : tj ≤ 4)
    (h : 8 * si + sj + t + 3 * (t / 5) = 8 * ti + tj + 18) :
    si + t / 5 = ti + 2 ∧ sj + t % 5 = tj + 2 := by omega

theorem idx_facts (x y u v : ℕ) (hx : x < 32) (hy : y < 32) (hu : u < 32) (hv : v < 32) :
    x + 31 - u < 63 ∧ y + 31 - v < 63 ∧
      (x + 31 - u) + 94 * (y + 31 - v) + (u + 94 * v) = x + 94 * y + 2945 := by omega

/-- A target square containing the target point keeps its flag bit: the source point lies in an alive
source square, which is far from the target square because the two points are more than `1/4` apart. -/
theorem step_bit (ex ey : ℕ) (hex : ex < 5) (hey : ey < 5) (src x y u v si sj ti tj : ℕ)
    (Ps Pt : Point) (hsub : src &&& FULL = src) (hx : x < 32) (hy : y < 32) (hu : u < 32)
    (hv : v < 32) (hals : src.testBit (11 * (u + 94 * v)) = true) (hsqs : InSq Ps si sj u v)
    (hsq : InSq Pt ti tj x y) (h1 : si + ex = ti + 2) (h2 : sj + ey = tj + 2)
    (hsep : 1 / 16 < sqDist Ps Pt) :
    ((tab ex ey * src + MADD) >>> 32405).testBit (11 * (x + 94 * y)) = true := by
  obtain ⟨hX, hXlt, htab⟩ := tab_spec ex ey hex hey
  obtain ⟨i1, i2, i3⟩ := idx_facts x y u v hx hy hu hv
  by_contra hD
  have hfar : ¬ 1600 < dist2 ex ey (x + 31 - u) (y + 31 - v) := fun hf =>
    hD (survive _ _ ((x + 31 - u) + 94 * (y + 31 - v)) (u + 94 * v) (x + 94 * y) hX hXlt
      hsub (htab _ _ i1 i2 hf) hals i3)
  have hc := close_of_not_far ex ey si sj ti tj u v x y h1 h2 hu hv hfar Ps Pt hsqs hsq
  linarith

theorem step_inv {q : ℕ → ℕ → Point} {ns pos : ℕ} (hG : Good q ns pos) (S d : ℕ)
    (hI : Inv q ns pos S) : Inv q ns pos (stepD S pos d) := by
  rw [stepD_eq]
  have ht : d % 25 < 5 * 5 := Nat.mod_lt _ (by norm_num)
  generalize d % 25 = t at ht ⊢
  generalize d / 800 = ks
  generalize d / 25 % 32 = kt
  rcases stepF_cases S kt t (slotE pos ks % 128) (slotE pos kt % 128) (slot S ks) with
    h | ⟨h1, h2, h3, h4⟩
  · rw [h]; exact hI
  rw [h4]
  have hks : ks < ns := by
    by_contra hc
    exact h3 (slot_hi R S ns ks R_pos hI.1 (not_lt.1 hc))
  apply inv_upd hI kt _ (Nat.sub_le _ _)
  intro hkt
  rw [Nat.sub_sub_self Nat.and_le_left]
  obtain ⟨hsub, x, y, hx, hy, hal, hsq⟩ := hI.2 kt hkt
  obtain ⟨hsubs, u, v, hu, hv, hals, hsqs⟩ := hI.2 ks hks
  obtain ⟨gs1, gs2, gs3⟩ := hG ks hks
  obtain ⟨gt1, gt2, _⟩ := hG kt hkt
  refine ⟨by rw [Nat.and_right_comm, hsub], x, y, hx, hy, ?_, hsq⟩
  rw [Nat.testBit_and, hal, Bool.true_and]
  rw [d64, d64] at h1
  obtain ⟨r1, r2⟩ := cell_rel _ _ _ _ t gs2 gt2 h1
  exact step_bit (t / 5) (t % 5) (Nat.div_lt_of_lt_mul ht) (Nat.mod_lt _ (by norm_num)) _ x y u v
    _ _ _ _ _ _ hsubs hx hy hu hv hals hsqs hsq r1 r2 (gs3 kt hkt h2)

theorem runCode_succ (n S pos code : ℕ) : runCode (n + 1) S pos code =
    runCode n (stepD S pos (Nat.mod (Nat.shiftRight code (Nat.mul 15 n)) 32768)) pos code := rfl

theorem runCode_inv {q : ℕ → ℕ → Point} {ns pos : ℕ} (hG : Good q ns pos) (code n : ℕ) :
    ∀ S, Inv q ns pos S → Inv q ns pos (runCode n S pos code) := by
  induction n with
  | zero => intro S h; exact h
  | succ n ih => intro S h; rw [runCode_succ]; exact ih _ (step_inv hG S _ h)

/-! ### Refutation trees -/

theorem chk_dead (ns pos n code k S : ℕ) : chk ns pos (.dead n code k) S =
    (Nat.blt k ns && Nat.beq (slot (runCode n S pos code) k) 0) := by
  rw [chk, slot_eq]

theorem chk_split (ns pos n code k ax m : ℕ) (lo hi : Cert) (S : ℕ) :
    chk ns pos (.split n code k ax m lo hi) S =
      (chk ns pos lo (runCode n S pos code - (slot (runCode n S pos code) k -
          lowPart (slot (runCode n S pos code) k) ax m) * R ^ k) &&
        chk ns pos hi (runCode n S pos code -
          lowPart (slot (runCode n S pos code) k) ax m * R ^ k)) := by
  rw [chk, force_eq, force_eq, force_eq, slot_eq, shl_eq, shl_eq]; rfl

theorem chk_sound {q : ℕ → ℕ → Point} {ns pos : ℕ} (hG : Good q ns pos) :
    ∀ (c : Cert) (S : ℕ), Inv q ns pos S → chk ns pos c S = true → False := by
  intro c
  induction c with
  | dead n code k =>
    intro S hI h
    rw [chk_dead, Bool.and_eq_true] at h
    have hk : k < ns := Nat.le_of_ble_eq_true h.1
    have hz := Nat.eq_of_beq_eq_true h.2
    obtain ⟨_, u, v, _, _, hal, _⟩ := (runCode_inv hG code n S hI).2 k hk
    rw [hz, Nat.zero_testBit] at hal
    exact absurd hal (by simp)
  | split n code k ax m lo hi ihlo ihhi =>
    intro S hI h
    rw [chk_split, Bool.and_eq_true] at h
    have hI1 := runCode_inv hG code n S hI
    generalize runCode n S pos code = S1 at h hI1
    have hl := lowPart_sub (slot S1 k) ax m
    generalize lowPart (slot S1 k) ax m = lp at h hl
    have hle : lp ≤ slot S1 k := by rw [← hl]; exact Nat.and_le_right
    by_cases hk : k < ns
    · obtain ⟨hsub, u, v, hu, hv, hal, hsq⟩ := hI1.2 k hk
      by_cases hb : lp.testBit (11 * (u + 94 * v)) = true
      · refine ihlo _ (inv_upd hI1 k _ (Nat.sub_le _ _) fun _ => ?_) h.1
        rw [Nat.sub_sub_self hle]
        exact ⟨by rw [← hl, Nat.and_assoc, hsub], u, v, hu, hv, hb, hsq⟩
      · refine ihhi _ (inv_upd hI1 k _ hle fun _ => ?_) h.2
        rw [sub_submask _ _ hl]
        refine ⟨xor_submask _ _ _ hl hsub, u, v, hu, hv, ?_, hsq⟩
        rw [Bool.not_eq_true] at hb
        rw [Nat.testBit_xor, hal, hb]; rfl
    · exact ihlo _ (inv_upd hI1 k _ (Nat.sub_le _ _) fun h' => absurd h' hk) h.1

/-! ### Initial state -/

theorem initReg_cases (e : ℕ) : (e / 64 = 0 ∧ initReg e = FULL) ∨ (e / 64 = 2 ∧ initReg e = LOWER) ∨
    (e / 64 ≠ 0 ∧ e / 64 ≠ 2 ∧ initReg e = UPPER) := by
  unfold initReg
  have e' : Nat.div e 64 = e / 64 := rfl
  rw [e']
  generalize e / 64 = w
  rcases w with _ | _ | _ | w
  · left; exact ⟨rfl, rfl⟩
  · right; right; exact ⟨by omega, by omega, rfl⟩
  · right; left; exact ⟨rfl, rfl⟩
  · right; right; exact ⟨by omega, by omega, rfl⟩

theorem initReg_sub (e : ℕ) : initReg e &&& FULL = initReg e := by
  rcases initReg_cases e with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> rw [h]
  · exact Nat.and_self _
  · exact half_spec.1
  · exact half_spec.2.1

theorem initReg_lt (e : ℕ) : initReg e < R := by
  have h1 : initReg e ≤ FULL := by rw [← initReg_sub e]; exact Nat.and_le_right
  have h2 : (2048 : ℕ) ^ 2946 ≤ R := by
    rw [R_eq]; exact pow_le_aux 2946 32768 (by norm_num)
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le FULL_spec.2.1 h2)

theorem initS_succ (pos n : ℕ) :
    initS pos (n + 1) = initS pos n + initReg (slotE pos n) * R ^ n := by
  have e : initS pos (n + 1) =
      Nat.add (initS pos n) (Nat.shiftLeft (initReg (slotE pos n)) (Nat.mul 32768 n)) := rfl
  rw [e, shl_eq]; rfl

theorem initS_spec (pos : ℕ) : ∀ n, initS pos n < R ^ n ∧
    ∀ k, k < n → slot (initS pos n) k = initReg (slotE pos k) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, fun k hk => absurd hk (by omega)⟩
    show 0 < R ^ 0
    rw [pow_zero]; exact Nat.one_pos
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ :=
      slot_add R (initS pos n) (initReg (slotE pos n)) n R_pos ih.1 (initReg_lt _)
    rw [initS_succ]
    refine ⟨h1, fun k hk => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
    · exact (h3 k h).trans (ih.2 k h)
    · rw [h]; exact h2

theorem slotE_lt (pos k : ℕ) : slotE pos k < 256 := Nat.mod_lt _ (by norm_num)

theorem slotOK_spec (a b e : ℕ) (h : slotOK a b e = true) : e / 8 % 8 ≤ 4 ∧ e % 8 ≤ 4 ∧
    (if e / 64 = 0 then a else b).testBit (5 * (e / 8 % 8) + e % 8) = true := by
  unfold slotOK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2, ?_⟩
  by_cases h0 : e / 64 = 0
  · rw [if_pos h0]
    have hb : Nat.beq (Nat.div e 64) 0 = true := by
      rw [show Nat.div e 64 = 0 from h0]; rfl
    rw [hb] at h3; exact h3
  · rw [if_neg h0]
    have hb : Nat.beq (Nat.div e 64) 0 = false := by
      cases hb : Nat.beq (Nat.div e 64) 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h0
    rw [hb] at h3; exact h3

theorem slotsOK_spec (a b pos : ℕ) : ∀ ns, slotsOK a b pos ns = true →
    ∀ k, k < ns → slotOK a b (slotE pos k) = true := by
  intro ns
  induction ns with
  | zero => intro _ k hk; omega
  | succ n ih =>
    intro h k hk
    have e : slotsOK a b pos (n + 1) = (slotsOK a b pos n && slotOK a b (slotE pos n)) := rfl
    rw [e, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h1 | h1
    · exact ih h.1 k h1
    · rw [h1]; exact h.2

/-! ### Normalized configurations -/

/-- A configuration of the pattern `(a, b)` in which the layer-0 point of every double cell lies in the
lower half of the cell and the layer-1 point in the upper half. -/
def NQ (a b : ℕ) (q : ℕ → ℕ → Point) : Prop :=
  (∀ c l, c < 25 → l < 2 → (layMask a b l).testBit c = true → InCellR (q c l) c) ∧
  (∀ c l c' l', c < 25 → l < 2 → c' < 25 → l' < 2 → (c, l) ≠ (c', l') →
      (layMask a b l).testBit c = true → (layMask a b l').testBit c' = true →
      (1 : ℝ) / 16 < sqDist (q c l) (q c' l')) ∧
  ∀ c, c < 25 → b.testBit c = true →
    (q c 0).2 ≤ ((c % 5 : ℕ) : ℝ) / 5 + 1 / 10 ∧ ((c % 5 : ℕ) : ℝ) / 5 + 1 / 10 ≤ (q c 1).2

theorem half_sep (A B : Point) (x0 y0 : ℝ) (hA1 : x0 ≤ A.1) (hA2 : A.1 ≤ x0 + 1 / 5)
    (hA3 : y0 ≤ A.2) (hB1 : x0 ≤ B.1) (hB2 : B.1 ≤ x0 + 1 / 5) (hB4 : B.2 ≤ y0 + 1 / 5)
    (hs : 1 / 16 < sqDist A B) (hle : A.2 ≤ B.2) : A.2 ≤ y0 + 1 / 10 ∧ y0 + 1 / 10 ≤ B.2 := by
  unfold sqDist at hs
  have hx : (A.1 - B.1) ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hd : 3 / 20 < B.2 - A.2 := by
    by_contra h
    have hy : (A.2 - B.2) ^ 2 ≤ (3 / 20 : ℝ) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    norm_num at hx hy
    linarith
  constructor <;> linarith

theorem sqDist_comm (A B : Point) : sqDist A B = sqDist B A := by unfold sqDist; ring

/-- The double cells whose two points are in the wrong order. -/
def swp (b : ℕ) (p : ℕ → ℕ → Point) (c : ℕ) : Prop :=
  b.testBit c = true ∧ c < 25 ∧ (p c 1).2 < (p c 0).2

open Classical in
/-- Layer permutation of cell `c`. -/
def sig (b : ℕ) (p : ℕ → ℕ → Point) (c l : ℕ) : ℕ := if swp b p c then 1 - l else l

theorem sig_lt (b : ℕ) (p : ℕ → ℕ → Point) (c l : ℕ) (hl : l < 2) : sig b p c l < 2 := by
  unfold sig; split_ifs <;> omega

theorem sig_inj (b : ℕ) (p : ℕ → ℕ → Point) (c l l' : ℕ) (hl : l < 2) (hl' : l' < 2)
    (h : sig b p c l = sig b p c l') : l = l' := by
  unfold sig at h; split_ifs at h <;> omega

theorem sig_mask (a b : ℕ) (hab : ∀ i, b.testBit i = true → a.testBit i = true)
    (p : ℕ → ℕ → Point) (c l : ℕ) (h : (layMask a b l).testBit c = true) :
    (layMask a b (sig b p c l)).testBit c = true := by
  unfold sig
  split_ifs with hs
  · unfold layMask
    split_ifs
    · exact hab c hs.1
    · exact hs.1
  · exact h

theorem exists_NQ (a b : ℕ) (hab : ∀ i, b.testBit i = true → a.testBit i = true)
    (p : ℕ → ℕ → Point)
    (hp1 : ∀ c l, c < 25 → l < 2 → (layMask a b l).testBit c = true → InCellR (p c l) c)
    (hp2 : ∀ c l c' l', c < 25 → l < 2 → c' < 25 → l' < 2 → (c, l) ≠ (c', l') →
      (layMask a b l).testBit c = true → (layMask a b l').testBit c' = true →
      (1 : ℝ) / 16 < sqDist (p c l) (p c' l')) : ∃ q, NQ a b q := by
  refine ⟨fun c l => p c (sig b p c l), ?_, ?_, ?_⟩
  · intro c l hc hl hm
    exact hp1 c _ hc (sig_lt b p c l hl) (sig_mask a b hab p c l hm)
  · intro c l c' l' hc hl hc' hl' hne hm hm'
    refine hp2 c _ c' _ hc (sig_lt b p c l hl) hc' (sig_lt b p c' l' hl') ?_
      (sig_mask a b hab p c l hm) (sig_mask a b hab p c' l' hm')
    intro heq
    have h1 : c = c' := congrArg Prod.fst heq
    subst h1
    have h2 : sig b p c l = sig b p c l' := congrArg Prod.snd heq
    exact hne (by rw [sig_inj b p c l l' hl hl' h2])
  · intro c hc hb
    have ha := hab c hb
    obtain ⟨a1, a2, a3, a4⟩ := hp1 c 0 hc (by norm_num) ha
    obtain ⟨b1, b2, b3, b4⟩ := hp1 c 1 hc (by norm_num) hb
    have hs := hp2 c 0 c 1 hc (by norm_num) hc (by norm_num) (by simp) ha hb
    by_cases hsw : (p c 1).2 < (p c 0).2
    · have h0 : sig b p c 0 = 1 := by unfold sig; rw [if_pos ⟨hb, hc, hsw⟩]
      have h1 : sig b p c 1 = 0 := by unfold sig; rw [if_pos ⟨hb, hc, hsw⟩]
      show (p c (sig b p c 0)).2 ≤ _ ∧ _ ≤ (p c (sig b p c 1)).2
      rw [h0, h1]
      rw [sqDist_comm] at hs
      exact half_sep (p c 1) (p c 0) _ _ b1 (by linarith) b3 a1 (by linarith) (by linarith) hs
        hsw.le
    · have h0 : sig b p c 0 = 0 := by
        unfold sig; rw [if_neg (fun h => hsw h.2.2)]
      have h1 : sig b p c 1 = 1 := by
        unfold sig; rw [if_neg (fun h => hsw h.2.2)]
      show (p c (sig b p c 0)).2 ≤ _ ∧ _ ≤ (p c (sig b p c 1)).2
      rw [h0, h1]
      exact half_sep (p c 0) (p c 1) _ _ a1 (by linarith) a3 b1 (by linarith) (by linarith) hs
        (not_lt.1 hsw)

theorem slot_mask (a b : ℕ) (hab : ∀ i, b.testBit i = true → a.testBit i = true) (e : ℕ)
    (h : (if e / 64 = 0 then a else b).testBit (5 * (e / 8 % 8) + e % 8) = true) :
    (layMask a b (e / 64 % 2)).testBit (5 * (e / 8 % 8) + e % 8) = true := by
  unfold layMask
  by_cases h0 : e / 64 = 0
  · rw [if_pos h0] at h
    rw [if_pos (by omega)]; exact h
  · rw [if_neg h0] at h
    split_ifs
    · exact hab _ h
    · exact h

theorem c_lt (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) : 5 * i + j < 25 := by omega

theorem c_div (i j : ℕ) (hj : j ≤ 4) : (5 * i + j) / 5 = i := by omega

theorem c_mod (i j : ℕ) (hj : j ≤ 4) : (5 * i + j) % 5 = j := by omega

theorem desc_eq (i j l i' j' l' : ℕ) (hj : j ≤ 4) (hj' : j' ≤ 4) (h1 : 5 * i + j = 5 * i' + j')
    (h2 : l = l') : 64 * l + (8 * i + j) = 64 * l' + (8 * i' + j') := by omega

theorem good_of {a b : ℕ} (hab : ∀ i, b.testBit i = true → a.testBit i = true)
    {q : ℕ → ℕ → Point} (hq : NQ a b q) {ns pos : ℕ}
    (hs : ∀ k, k < ns → slotOK a b (slotE pos k) = true) : Good q ns pos := by
  intro k hk
  obtain ⟨s1, s2, s3⟩ := slotOK_spec a b _ (hs k hk)
  refine ⟨s1, s2, fun k' hk' hne => ?_⟩
  obtain ⟨t1, t2, t3⟩ := slotOK_spec a b _ (hs k' hk')
  rw [d128, d128] at hne
  refine hq.2.1 _ _ _ _ (c_lt _ _ s1 s2) (Nat.mod_lt _ (by norm_num)) (c_lt _ _ t1 t2)
    (Nat.mod_lt _ (by norm_num)) ?_ (slot_mask a b hab _ s3) (slot_mask a b hab _ t3)
  intro heq
  exact hne (desc_eq _ _ _ _ _ _ s2 t2 (congrArg Prod.fst heq) (congrArg Prod.snd heq))

theorem w_odd (w : ℕ) (h0 : w ≠ 0) (h2 : w ≠ 2) (hw : w < 4) : w % 2 = 1 := by omega

theorem init_holds {a b : ℕ} (hab : ∀ i, b.testBit i = true → a.testBit i = true)
    {q : ℕ → ℕ → Point} (hq : NQ a b q) (e : ℕ) (he : e < 256) (hs : slotOK a b e = true) :
    Holds (ptOf q e) e (initReg e) := by
  obtain ⟨s1, s2, s3⟩ := slotOK_spec a b _ hs
  have hm := slot_mask a b hab e s3
  have hc5 : (5 * (e / 8 % 8) + e % 8) / 5 = e / 8 % 8 := c_div _ _ s2
  have hc5' : (5 * (e / 8 % 8) + e % 8) % 5 = e % 8 := c_mod _ _ s2
  have hc25 : 5 * (e / 8 % 8) + e % 8 < 25 := c_lt _ _ s1 s2
  have hcell := hq.1 _ _ hc25 (Nat.mod_lt _ (by norm_num)) hm
  unfold InCellR at hcell
  rw [hc5, hc5'] at hcell
  obtain ⟨c1, c2, c3, c4⟩ := hcell
  have hP : ptOf q e = q (5 * (e / 8 % 8) + e % 8) (e / 64 % 2) := rfl
  rw [← hP] at c1 c2 c3 c4
  obtain ⟨u, -, hu, u1, u2⟩ := exists_sq 0 32 (by norm_num) (160 * (ptOf q e).1 - 32 * (e / 8 % 8 : ℕ))
    (by rw [Nat.cast_zero]; linarith) (by rw [Nat.cast_ofNat]; linarith)
  have key : ∀ lo hi : ℕ, lo < hi → hi ≤ 32 →
      (lo : ℝ) ≤ 160 * (ptOf q e).2 - 32 * (e % 8 : ℕ) →
      160 * (ptOf q e).2 - 32 * (e % 8 : ℕ) ≤ hi →
      (∀ v, lo ≤ v → v < hi → (initReg e).testBit (11 * (u + 94 * v)) = true) →
      Holds (ptOf q e) e (initReg e) := by
    intro lo hi hlh hhi y1 y2 hbit
    obtain ⟨v, hv1, hv2, v1, v2⟩ := exists_sq lo hi hlh _ y1 y2
    exact ⟨u, v, hu, lt_of_lt_of_le hv2 hhi, hbit v hv1 hv2, by linarith, by linarith, by linarith, by linarith⟩
  rcases initReg_cases e with ⟨h0, hr⟩ | ⟨h0, hr⟩ | ⟨h0, h2, hr⟩
  · refine key 0 32 (by norm_num) (by norm_num) (by rw [Nat.cast_zero]; linarith)
      (by rw [Nat.cast_ofNat]; linarith) fun v _ hv => ?_
    rw [hr]; exact FULL_spec.2.2.2 u v hu hv
  · rw [if_neg (by rw [h0]; norm_num)] at s3
    have hl : e / 64 % 2 = 0 := by rw [h0]
    have hlow := (hq.2.2 _ hc25 s3).1
    rw [hc5', ← hl, ← hP] at hlow
    refine key 0 16 (by norm_num) (by norm_num) (by rw [Nat.cast_zero]; linarith)
      (by rw [Nat.cast_ofNat]; linarith) fun v _ hv => ?_
    rw [hr]; exact half_spec.2.2.1 u v hu hv
  · rw [if_neg h0] at s3
    have hl : e / 64 % 2 = 1 := w_odd _ h0 h2 (Nat.div_lt_of_lt_mul he)
    have hup := (hq.2.2 _ hc25 s3).2
    rw [hc5', ← hl, ← hP] at hup
    refine key 16 32 (by norm_num) (by norm_num) (by rw [Nat.cast_ofNat]; linarith)
      (by rw [Nat.cast_ofNat]; linarith) fun v hv1 hv => ?_
    rw [hr]; exact half_spec.2.2.2 u v hu hv1 hv

theorem inv_init {a b : ℕ} (hab : ∀ i, b.testBit i = true → a.testBit i = true)
    {q : ℕ → ℕ → Point} (hq : NQ a b q) {ns pos : ℕ}
    (hs : ∀ k, k < ns → slotOK a b (slotE pos k) = true) : Inv q ns pos (initS pos ns) := by
  obtain ⟨h1, h2⟩ := initS_spec pos ns
  refine ⟨h1, fun k hk => ?_⟩
  rw [h2 k hk]
  exact ⟨initReg_sub _, init_holds hab hq _ (slotE_lt pos k) (hs k hk)⟩

/-- Soundness of the checker: a refuted pattern `(a, b)` with `b ⊆ a` is infeasible. -/
theorem refuted_sound (a b ns pos : ℕ) (c : Cert) (hab : ∀ i, b.testBit i = true → a.testBit i = true)
    (h : refuted a b ns pos c = true) : Infeasible a b := by
  unfold refuted at h
  rw [Bool.and_eq_true] at h
  unfold Infeasible
  rintro ⟨p, hp1, hp2⟩
  obtain ⟨q, hq⟩ := exists_NQ a b hab p hp1 hp2
  have hs := slotsOK_spec a b pos ns h.1
  exact chk_sound (good_of hab hq hs) c _ (inv_init hab hq hs) h.2

theorem refutedAll_sound : ∀ (L : List (ℕ × ℕ)) (G : List (ℕ × ℕ × Cert)),
    refutedAll L G = true → ∀ i, i < G.length → ∀ x, L[i]? = some x → Infeasible x.1 x.2
  | _, [], _, i, hi, _, _ => absurd hi (by simp)
  | [], _ :: _, h, _, _, _, _ => absurd h (by simp [refutedAll])
  | y :: ys, g :: gs, h, i, hi, x, hx => by
    rw [refutedAll, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases i with
    | zero =>
      rw [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      refine refuted_sound _ _ _ _ _ ?_ h2
      have h1' : y.1 &&& y.2 = y.2 := Nat.eq_of_beq_eq_true h1
      intro i hi
      rw [← h1', Nat.testBit_and, Bool.and_eq_true] at hi
      exact hi.1
    | succ i =>
      rw [List.getElem?_cons_succ] at hx
      exact refutedAll_sound ys gs h3 i (by simpa using hi) x hx

/-- Soundness of a batch: the library entries `lo ≤ e < lo + G.length` are infeasible. -/
theorem batch_sound (lo : ℕ) (G : List (ℕ × ℕ × Cert)) (h : batchOK lo G = true) (e : ℕ) (h1 : lo ≤ e)
    (h2 : e < lo + G.length) (x : ℕ × ℕ) (hx : nogoods[e]? = some x) : Infeasible x.1 x.2 := by
  unfold batchOK at h
  refine refutedAll_sound _ G h (e - lo) (by omega) x ?_
  rw [List.getElem?_drop, Nat.add_sub_cancel' h1]
  exact hx

end Bitmap
end Twentyfive
end CirclePackingConstants


