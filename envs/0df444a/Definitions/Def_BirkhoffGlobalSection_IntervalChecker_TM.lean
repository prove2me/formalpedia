-- Prove2me | Definitions.Def_BirkhoffGlobalSection_IntervalChecker_TM
-- name    : BirkhoffGlobalSection_IntervalChecker_TM
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-01T08:24:28.397986+00:00
-- url     : https://prove2.me/theorems/ff4c8cfd-b904-4e06-a7e1-8ed3432e6727
-- title:
--   Taylor models over exact checker scalars
-- statement:
--   Taylor models $\langle p, e\rangle$: a dense polynomial $p$ in the noise symbols plus an error bound, representing $x$ at the noise point $d$ when $|x-p(d)|\le e$. Products are truncated at a total degree $N$; the dropped monomials are bounded by the sum of their absolute coefficients (`TM.rep_mul`). Polynomial layer with soundness lemmas: dense product (`eval_mul`), split by total degree (`eval_trunc_add_high`), coefficient bound on $[-1,1]^n$ (`abs_eval_le_absSum`), variable scaling, an unused last variable. `TM.rep_piece`: the Taylor model of a polynomial on a box, with the last variable folded into the error. `invsqrt_newton`: if $y\ge0$ and $1/r\le k$ then $|1/r-y|\le k\,|1-y^2r^2|$; `TM.rep_invsqrt` packages it. All computable (`decide +kernel`).
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_IntervalChecker_Affine

/-!
# Taylor models over exact checker scalars

A *Taylor model* `⟨p, e⟩ : TM α n` is a dense polynomial `p : NP α n` in `n` noise symbols together with
an error bound `e`; it represents a real `x` at the noise point `d` (`|dₖ| ≤ 1`) when
`|x - p(d)| ≤ e` (`TM.Rep`). Products are truncated at a total degree `N`: the dropped monomials are
bounded by the sum of their absolute coefficients (`NP.absSum`) and moved into the error (`TM.rep_mul`).
With `N = 1` this is affine arithmetic; `N ≥ 2` keeps the second-order dependency between factors,
which removes most of the overestimation of affine arithmetic on long product chains.

Polynomial layer (all by structural recursion, so the kernel evaluates it):
* `NP.mul` (dense product, `eval_mul`), `NP.trunc` / `NP.high` (split by total degree,
  `eval_trunc_add_high`), `NP.absSum` (`abs_eval_le_absSum` on the noise box),
  `NP.scaleVars` (`p(x) ↦ p(h ⊙ x)`, `eval_scaleVars`), `NP.lift` (add an unused last variable,
  `eval_lift`).

Real lemma: `invsqrt_newton`, the residual bound for a nonnegative approximation `y` of `1/r`:
`|1/r - y| ≤ k · |1 - y² r²|` whenever `1/r ≤ k`; `TM.rep_invsqrt` packages it for Taylor models.

Taylor models: Berz–Hoffstätter, *Computation and application of Taylor polynomials with interval
remainder bounds*, Reliable Computing 4 (1998) 83–97; Makino–Berz, Int. J. Pure Appl. Math. 4 (2003).
-/

namespace BirkhoffGlobalSection.TangentialHessian.Checker

open CNum

variable {α : Type} [CNum α]

namespace NP

/-! ### Products -/

/-- Product of coefficient lists (Cauchy product) with a given coefficient product. -/
def mulL {β : Type} (m : β → β → β) (ad : β → β → β) (z : β) : List β → List β → List β
  | [], _ => []
  | a :: as, bs => addList ad (bs.map (m a)) (z :: mulL m ad z as bs)

/-- Dense product. -/
def mul : (n : ℕ) → NP α n → NP α n → NP α n
  | 0, a, b => CNum.mul (α := α) a b
  | n + 1, as, bs => mulL (mul n) (add n) (zero n) (as : List (NP α n)) bs

theorem evalList_map_mul (n : ℕ)
    (hmul : ∀ (a b : NP α n) (xs : List ℝ), eval n (mul n a b) xs = eval n a xs * eval n b xs)
    (a : NP α n) (bs : List (NP α n)) (x : ℝ) (xs : List ℝ) :
    evalList n (bs.map (mul n a)) x xs = eval n a xs * evalList n bs x xs := by
  induction bs with
  | nil => simp [evalList_nil]
  | cons b bs ih => simp only [List.map_cons, evalList_cons, hmul, ih]; ring

theorem eval_mul : ∀ (n : ℕ) (a b : NP α n) (xs : List ℝ),
    eval n (mul n a b) xs = eval n a xs * eval n b xs
  | 0, a, b, _ => CNum.toReal_mul (α := α) a b
  | _ + 1, _, _, [] => by simp [eval]
  | n + 1, as, bs, x :: xs => by
    show evalList n (mulL (mul n) (add n) (zero n) as bs) x xs = evalList n as x xs * evalList n bs x xs
    induction (as : List (NP α n)) with
    | nil => simp [mulL, evalList_nil]
    | cons a as ih =>
      simp only [mulL, evalList_addList, evalList_map_mul n (eval_mul n) a bs x xs, evalList_cons,
        eval_zero, ih]
      ring

/-! ### Splitting by total degree -/

def truncL {β : Type} (t : ℕ → β → β) : ℕ → List β → List β
  | _, [] => []
  | 0, c :: _ => [t 0 c]
  | N + 1, c :: cs => t (N + 1) c :: truncL t N cs

def highL {β : Type} (h : ℕ → β → β) : ℕ → List β → List β
  | _, [] => []
  | 0, c :: cs => h 0 c :: cs
  | N + 1, c :: cs => h (N + 1) c :: highL h N cs

/-- The monomials of total degree `≤ N`. -/
def trunc : (n : ℕ) → ℕ → NP α n → NP α n
  | 0, _, a => a
  | n + 1, N, cs => truncL (trunc n) N (cs : List (NP α n))

/-- The monomials of total degree `> N`. -/
def high : (n : ℕ) → ℕ → NP α n → NP α n
  | 0, _, _ => (CNum.zero : α)
  | n + 1, N, cs => highL (high n) N (cs : List (NP α n))

theorem eval_trunc_add_high : ∀ (n N : ℕ) (p : NP α n) (xs : List ℝ),
    eval n (trunc n N p) xs + eval n (high n N p) xs = eval n p xs
  | 0, _, a, _ => by
    show toReal (α := α) a + toReal (α := α) CNum.zero = toReal (α := α) a
    rw [toReal_zero, add_zero]
  | _ + 1, _, _, [] => by simp [eval]
  | n + 1, N, cs, x :: xs => by
    show evalList n (truncL (trunc n) N cs) x xs + evalList n (highL (high n) N cs) x xs =
      evalList n cs x xs
    induction (cs : List (NP α n)) generalizing N with
    | nil => cases N <;> simp [truncL, highL, evalList_nil]
    | cons c cs ih =>
      cases N with
      | zero =>
        simp only [truncL, highL, evalList_cons, evalList_nil]
        rw [← eval_trunc_add_high n 0 c xs]; ring
      | succ N =>
        simp only [truncL, highL, evalList_cons]
        rw [← eval_trunc_add_high n (N + 1) c xs, ← ih N]; ring

/-! ### Sum of absolute coefficients -/

def absSumL {β : Type} (f : β → α) : List β → α
  | [] => CNum.zero
  | c :: cs => CNum.add (f c) (absSumL f cs)

/-- `Σ |coefficients|`: a bound for `|p|` on the noise box `[-1, 1]ⁿ`. -/
def absSum : (n : ℕ) → NP α n → α
  | 0, a => CNum.aabs a
  | n + 1, cs => absSumL (absSum n) (cs : List (NP α n))

theorem absSum_nonneg : ∀ (n : ℕ) (p : NP α n), 0 ≤ toReal (absSum n p)
  | 0, a => by
    have h := CNum.toReal_aabs (α := α) a
    exact h ▸ abs_nonneg _
  | n + 1, cs => by
    show 0 ≤ toReal (absSumL (absSum n) (cs : List (NP α n)))
    induction (cs : List (NP α n)) with
    | nil => simp [absSumL, toReal_zero]
    | cons c cs ih => simp only [absSumL, toReal_add]; exact add_nonneg (absSum_nonneg n c) ih

theorem abs_eval_le_absSum : ∀ (n : ℕ) (p : NP α n) (xs : List ℝ), AF.Noise xs →
    |eval n p xs| ≤ toReal (absSum n p)
  | 0, a, _, _ => (CNum.toReal_aabs (α := α) a).ge
  | n + 1, p, [], _ => by simp only [eval, abs_zero]; exact absSum_nonneg (n + 1) p
  | n + 1, cs, x :: xs, hd => by
    have hx : |x| ≤ 1 := hd x (by simp)
    have hxs : AF.Noise xs := fun t ht => hd t (by simp [ht])
    show |evalList n cs x xs| ≤ toReal (absSumL (absSum n) (cs : List (NP α n)))
    induction (cs : List (NP α n)) with
    | nil => simp [evalList_nil, absSumL, toReal_zero]
    | cons c cs ih =>
      rw [evalList_cons]
      simp only [absSumL, toReal_add]
      calc |eval n c xs + x * evalList n cs x xs|
          ≤ |eval n c xs| + |x| * |evalList n cs x xs| := by
            rw [← abs_mul]; exact abs_add_le _ _
        _ ≤ toReal (absSum n c) + 1 * toReal (absSumL (absSum n) cs) := by
            gcongr
            exact abs_eval_le_absSum n c xs hxs
        _ = _ := by ring

/-! ### Scaling the variables -/

def svL {β : Type} (sc : β → β) (s : β → β) : List β → List β
  | [] => []
  | c :: cs => sc c :: (svL sc s cs).map s

/-- `p(x) ↦ p(h ⊙ x)`. -/
def scaleVars : (n : ℕ) → List α → NP α n → NP α n
  | 0, _, c => c
  | n + 1, h :: hs, cs => svL (scaleVars n hs) (scale n h) (cs : List (NP α n))
  | _ + 1, [], cs => cs

/-- Pointwise `h ⊙ t`. -/
noncomputable def mulPt : List α → List ℝ → List ℝ
  | h :: hs, t :: ts => (toReal h * t) :: mulPt hs ts
  | _, _ => []

theorem length_mulPt : ∀ (hs : List α) (ts : List ℝ), (mulPt hs ts).length = min hs.length ts.length
  | [], _ => by simp [mulPt]
  | _ :: _, [] => by simp [mulPt]
  | _ :: hs, _ :: ts => by simp [mulPt, length_mulPt hs ts, Nat.min_def]; split_ifs <;> omega

theorem eval_scaleVars : ∀ (n : ℕ) (hs : List α) (p : NP α n) (ts : List ℝ),
    hs.length = n → ts.length = n → eval n (scaleVars n hs p) ts = eval n p (mulPt hs ts)
  | 0, _, _, _, _, _ => by simp [scaleVars, eval]
  | _ + 1, [], _, _, h, _ => by simp at h
  | _ + 1, _ :: _, _, [], _, h => by simp at h
  | n + 1, h :: hs, cs, t :: ts, hh, ht => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hh ht
    show evalList n (svL (scaleVars n hs) (scale n h) (cs : List (NP α n))) t ts =
      evalList n cs (toReal h * t) (mulPt hs ts)
    have hscale : ∀ q : List (NP α n),
        evalList n (q.map (scale n h)) t ts = toReal h * evalList n q t ts := fun q =>
      eval_scale (n + 1) h q (t :: ts)
    induction (cs : List (NP α n)) with
    | nil => simp [svL, evalList_nil]
    | cons c cs ih =>
      simp only [svL, evalList_cons, hscale, ih, eval_scaleVars n hs c ts hh ht]
      ring

/-! ### An unused last variable -/

/-- `p` as a polynomial in one more (last) variable. -/
def lift : (n : ℕ) → NP α n → NP α (n + 1)
  | 0, c => ([c] : List α)
  | n + 1, cs => (cs : List (NP α n)).map (lift n)

theorem eval_lift : ∀ (n : ℕ) (p : NP α n) (xs : List ℝ) (t : ℝ), xs.length = n →
    eval (n + 1) (lift n p) (xs ++ [t]) = eval n p xs
  | 0, c, [], t, _ => by
    show evalList 0 [c] t [] = toReal (α := α) c
    rw [evalList_cons, evalList_nil]; simp [eval]
  | 0, _, _ :: _, _, h => by simp at h
  | _ + 1, _, [], _, h => by simp at h
  | n + 1, cs, x :: xs, t, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    show evalList (n + 1) ((cs : List (NP α n)).map (lift n)) x (xs ++ [t]) = evalList n cs x xs
    induction (cs : List (NP α n)) with
    | nil => simp [evalList_nil]
    | cons c cs ih => simp only [List.map_cons, evalList_cons, eval_lift n c xs t h, ih]

/-- Constant term in the last variable (any choice is sound; used to drop a variable). -/
def dropLast : (n : ℕ) → NP α (n + 1) → NP α n
  | 0, cs => ((match (cs : List α) with | [] => (CNum.zero : α) | c :: _ => c) : α)
  | n + 1, cs => (cs : List (NP α (n + 1))).map (dropLast n)

/-- The unit box `[-1, 1]ⁿ`. -/
def unitBox (n : ℕ) : List (Iv α) := List.replicate n (CNum.neg CNum.one, CNum.one)

theorem inBox_unitBox {d : List ℝ} (hd : AF.Noise d) : InBox d (unitBox (α := α) d.length) := by
  induction d with
  | nil => exact List.Forall₂.nil
  | cons t d ih =>
    have ht : |t| ≤ 1 := hd t (by simp)
    refine List.Forall₂.cons ?_ (ih fun s hs => hd s (by simp [hs]))
    rw [abs_le] at ht
    exact ⟨by simp [toReal_neg, toReal_one]; linarith, by simp [toReal_one]; linarith⟩

end NP

/-! ### Real lemma: residual bound for an approximate inverse square root -/

/-- If `y ≥ 0` approximates `1/r` with residual `|1 - y² r²| ≤ ρ` and `1/r ≤ k`, then
`|1/r - y| ≤ k ρ`. (With `t = y r ≥ 0`: `1/r - y = (1/r)(1 - t²)/(1 + t)`.) -/
theorem invsqrt_newton {r y ρ k : ℝ} (hr : 0 < r) (hy : 0 ≤ y) (hk : r⁻¹ ≤ k)
    (hρ : |1 - y ^ 2 * r ^ 2| ≤ ρ) : |r⁻¹ - y| ≤ k * ρ := by
  have ht : 0 ≤ y * r := mul_nonneg hy hr.le
  have hden : 0 < 1 + y * r := by linarith
  have key : r⁻¹ - y = r⁻¹ * (1 - y ^ 2 * r ^ 2) / (1 + y * r) := by
    field_simp; ring
  have hinv : 0 < r⁻¹ := inv_pos.2 hr
  rw [key, abs_div, abs_mul, abs_of_pos hinv, abs_of_pos hden]
  calc r⁻¹ * |1 - y ^ 2 * r ^ 2| / (1 + y * r)
      ≤ r⁻¹ * |1 - y ^ 2 * r ^ 2| :=
        div_le_self (mul_nonneg hinv.le (abs_nonneg _)) (by linarith)
    _ ≤ k * ρ := mul_le_mul hk hρ (abs_nonneg _) (hinv.le.trans hk)

/-! ### Taylor models -/

/-- A Taylor model in `n` noise symbols: polynomial part and error bound. -/
structure TM (α : Type) (n : ℕ) where
  p : NP α n
  e : α

namespace TM

variable {n : ℕ}

/-- `A` represents `x` at the noise point `d`. -/
def Rep (d : List ℝ) (A : TM α n) (x : ℝ) : Prop := |x - NP.eval n A.p d| ≤ toReal A.e

def const (n : ℕ) (q : α) : TM α n := ⟨NP.mono n q [], CNum.zero⟩

/-- The box variable `m + h dₖ`. -/
def var (n k : ℕ) (m h : α) : TM α n :=
  ⟨NP.add n (NP.mono n m []) (NP.mono n h (List.replicate k 0 ++ [1])), CNum.zero⟩

def add (A B : TM α n) : TM α n := ⟨NP.add n A.p B.p, CNum.add A.e B.e⟩

def scal (q : α) (A : TM α n) : TM α n := ⟨NP.scale n q A.p, CNum.mul (CNum.aabs q) A.e⟩

def sub (A B : TM α n) : TM α n := add A (scal (CNum.neg CNum.one) B)

/-- Product truncated at total degree `N`. -/
def mul (N : ℕ) (A B : TM α n) : TM α n :=
  let P := NP.mul n A.p B.p
  ⟨NP.trunc n N P,
    CNum.add (CNum.add (NP.absSum n (NP.high n N P)) (CNum.mul (NP.absSum n A.p) B.e))
      (CNum.add (CNum.mul (NP.absSum n B.p) A.e) (CNum.mul A.e B.e))⟩

/-- Interval enclosure (monomial-wise bound of the polynomial part on `[-1, 1]ⁿ`, widened by `e`). -/
def range (A : TM α n) : Iv α :=
  let I := NP.ieval n A.p (NP.unitBox n)
  (CNum.sub I.1 A.e, CNum.add I.2 A.e)

variable {d : List ℝ}

theorem rep_const (hl : d.length = n) (q : α) : Rep d (const n q) (toReal q) := by
  simp [Rep, const, NP.eval_mono n q [] d hl, monoR, toReal_zero]

theorem rep_var (hl : d.length = n) (k : ℕ) (m h : α) :
    Rep d (var n k m h) (toReal m + toReal h * monoR (List.replicate k 0 ++ [1]) d) := by
  simp [Rep, var, NP.eval_add, NP.eval_mono n _ _ d hl, monoR, toReal_zero]

theorem rep_add {A B : TM α n} {x y : ℝ} (hA : Rep d A x) (hB : Rep d B y) :
    Rep d (add A B) (x + y) := by
  unfold Rep at *
  simp only [add, NP.eval_add, toReal_add]
  calc |x + y - (NP.eval n A.p d + NP.eval n B.p d)|
      = |(x - NP.eval n A.p d) + (y - NP.eval n B.p d)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hA hB)

theorem rep_scal (q : α) {A : TM α n} {x : ℝ} (hA : Rep d A x) :
    Rep d (scal q A) (toReal q * x) := by
  unfold Rep at *
  simp only [scal, NP.eval_scale, toReal_mul, CNum.toReal_aabs]
  rw [show toReal q * x - toReal q * NP.eval n A.p d = toReal q * (x - NP.eval n A.p d) by ring,
    abs_mul]
  exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)

theorem rep_sub {A B : TM α n} {x y : ℝ} (hA : Rep d A x) (hB : Rep d B y) :
    Rep d (sub A B) (x - y) := by
  have h := rep_add hA (rep_scal (CNum.neg CNum.one) hB)
  simp only [toReal_neg, toReal_one, neg_one_mul] at h
  simpa [sub, sub_eq_add_neg] using h

theorem rep_mul (hd : AF.Noise d) (N : ℕ) {A B : TM α n} {x y : ℝ} (hA : Rep d A x)
    (hB : Rep d B y) : Rep d (mul N A B) (x * y) := by
  unfold Rep at *
  simp only [mul, toReal_add, toReal_mul]
  have hsplit := NP.eval_trunc_add_high n N (NP.mul n A.p B.p) d
  rw [NP.eval_mul] at hsplit
  set P := NP.eval n A.p d
  set Q := NP.eval n B.p d
  set T := NP.eval n (NP.trunc n N (NP.mul n A.p B.p)) d
  set H := NP.eval n (NP.high n N (NP.mul n A.p B.p)) d
  have hH := NP.abs_eval_le_absSum n (NP.high n N (NP.mul n A.p B.p)) d hd
  have hP := NP.abs_eval_le_absSum n A.p d hd
  have hQ := NP.abs_eval_le_absSum n B.p d hd
  set u := x - P with hu
  set v := y - Q with hv
  have e₁ : x * y - T = H + P * v + Q * u + u * v := by
    rw [hu, hv]; linear_combination -hsplit
  rw [e₁]
  calc |H + P * v + Q * u + u * v| ≤ |H| + |P| * |v| + |Q| * |u| + |u| * |v| := by
        simp only [← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ toReal (NP.absSum n (NP.high n N (NP.mul n A.p B.p))) + toReal (NP.absSum n A.p) * toReal B.e
        + (toReal (NP.absSum n B.p) * toReal A.e + toReal A.e * toReal B.e) := by
        have hv0 := abs_nonneg v
        have hu0 := abs_nonneg u
        have := mul_le_mul hP hB hv0 (NP.absSum_nonneg n A.p)
        have := mul_le_mul hQ hA hu0 (NP.absSum_nonneg n B.p)
        have := mul_le_mul hA hB hv0 ((abs_nonneg _).trans hA)
        linarith

/-- The represented value lies in `range A`. -/
theorem mem_range (hd : AF.Noise d) (hl : d.length = n) {A : TM α n} {x : ℝ} (hA : Rep d A x) :
    Mem x (range A) := by
  unfold Rep at hA
  have hI := NP.mem_ieval n A.p d (NP.unitBox n) (hl ▸ NP.inBox_unitBox hd)
  unfold Mem at hI ⊢
  rw [abs_le] at hA
  simp only [range, CNum.sub, toReal_add, toReal_neg]
  constructor <;> linarith [hI.1, hI.2, hA.1, hA.2]

/-- Taylor model (in the first `n` noise symbols) of a polynomial `p` in `n + 1` variables over the box
with centres `M` and half-widths `H`: exact Taylor shift, scaling to the noise box, the last variable
folded into the error, and the monomials of total degree `> N` bounded by their absolute coefficients. -/
def piece (n N : ℕ) (M H : List α) (p : NP α (n + 1)) : TM α n :=
  let S4 := NP.scaleVars (n + 1) H (NP.shift (n + 1) M p)
  let S := NP.dropLast n S4
  let rest := NP.add (n + 1) S4 (NP.scale (n + 1) (CNum.neg CNum.one) (NP.lift n S))
  ⟨NP.trunc n N S, CNum.add (NP.absSum n (NP.high n N S)) (NP.absSum (n + 1) rest)⟩

theorem rep_piece (hd : AF.Noise d) (hl : d.length = n) {t : ℝ} (ht : |t| ≤ 1) (N : ℕ)
    {M H : List α} (hM : M.length = n + 1) (hH : H.length = n + 1) (p : NP α (n + 1)) :
    Rep d (piece n N M H p) (NP.eval (n + 1) p (NP.addPt M (NP.mulPt H (d ++ [t])))) := by
  have hdt : AF.Noise (d ++ [t]) := by
    intro s hs
    rcases List.mem_append.mp hs with h | h
    · exact hd s h
    · simp only [List.mem_singleton] at h; exact h ▸ ht
  have hlt : (d ++ [t]).length = n + 1 := by simp [hl]
  have hmp : (NP.mulPt H (d ++ [t])).length = n + 1 := by rw [NP.length_mulPt, hH, hlt, min_self]
  set S4 := NP.scaleVars (n + 1) H (NP.shift (n + 1) M p)
  set S := NP.dropLast n S4
  have h1 : NP.eval (n + 1) p (NP.addPt M (NP.mulPt H (d ++ [t]))) = NP.eval (n + 1) S4 (d ++ [t]) := by
    rw [NP.eval_scaleVars (n + 1) H _ _ hH hlt, NP.eval_shift (n + 1) M p _ hM hmp]
  have h2 : NP.eval (n + 1) S4 (d ++ [t]) = NP.eval n S d +
      NP.eval (n + 1) (NP.add (n + 1) S4 (NP.scale (n + 1) (CNum.neg CNum.one) (NP.lift n S))) (d ++ [t]) := by
    rw [NP.eval_add, NP.eval_scale, NP.eval_lift n S d t hl, toReal_neg, toReal_one]; ring
  have h3 := NP.eval_trunc_add_high n N S d
  have hR := NP.abs_eval_le_absSum (n + 1)
    (NP.add (n + 1) S4 (NP.scale (n + 1) (CNum.neg CNum.one) (NP.lift n S))) (d ++ [t]) hdt
  have hHi := NP.abs_eval_le_absSum n (NP.high n N S) d hd
  unfold Rep
  simp only [piece, toReal_add]
  rw [h1, h2, ← h3]
  calc |NP.eval n (NP.trunc n N S) d + NP.eval n (NP.high n N S) d + _ - NP.eval n (NP.trunc n N S) d|
      = |NP.eval n (NP.high n N S) d + NP.eval (n + 1)
          (NP.add (n + 1) S4 (NP.scale (n + 1) (CNum.neg CNum.one) (NP.lift n S))) (d ++ [t])| := by
        ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hHi hR)

/-- Taylor model of `1/r` from a Taylor model `Dt` of `r²` and a candidate polynomial `Yp ≥ 0`:
the error is `k · max|1 - Yp² · r²|` for any upper bound `k` of `1/r`. -/
def invsqrt (N : ℕ) (Dt : TM α n) (Yp : NP α n) (k : α) : TM α n :=
  let R := range (sub (const n CNum.one) (mul N (mul N ⟨Yp, CNum.zero⟩ ⟨Yp, CNum.zero⟩) Dt))
  ⟨Yp, CNum.mul k (amax (CNum.neg R.1) R.2)⟩

theorem rep_invsqrt (hd : AF.Noise d) (hl : d.length = n) (N : ℕ) {Dt : TM α n} {r : ℝ}
    (hr : 0 < r) (hD : Rep d Dt (r ^ 2)) (Yp : NP α n)
    (hY : ble CNum.zero (NP.ieval n Yp (NP.unitBox n)).1 = true) (k : α) (hk : r⁻¹ ≤ toReal k) :
    Rep d (invsqrt N Dt Yp k) r⁻¹ := by
  set y := NP.eval n Yp d
  have hY0 : Rep d (⟨Yp, CNum.zero⟩ : TM α n) y := by simp [Rep, y, toReal_zero]
  have hy : 0 ≤ y := by
    have hI := NP.mem_ieval n Yp d (NP.unitBox n) (hl ▸ NP.inBox_unitBox hd)
    rw [ble_iff, toReal_zero] at hY
    exact hY.trans hI.1
  have hrho := mem_range hd hl
    (rep_sub (rep_const hl CNum.one) (rep_mul hd N (rep_mul hd N hY0 hY0) hD))
  set R := range (sub (const n CNum.one) (mul N (mul N ⟨Yp, CNum.zero⟩ ⟨Yp, CNum.zero⟩) Dt))
  unfold Mem at hrho
  rw [toReal_one] at hrho
  have e2 : y * y * r ^ 2 = y ^ 2 * r ^ 2 := by ring
  have hv1 : toReal R.1 ≤ 1 - y ^ 2 * r ^ 2 := by linarith [hrho.1]
  have hv2 : 1 - y ^ 2 * r ^ 2 ≤ toReal R.2 := by linarith [hrho.2]
  have hρ : |1 - y ^ 2 * r ^ 2| ≤ toReal (amax (CNum.neg R.1) R.2) := by
    rw [amax, abs_le]
    split_ifs with h
    · rw [ble_iff, toReal_neg] at h
      constructor <;> linarith
    · rw [ble_iff, toReal_neg] at h
      rw [toReal_neg]
      constructor <;> linarith [not_le.mp h]
  show |r⁻¹ - NP.eval n Yp d| ≤ toReal (CNum.mul k (amax (CNum.neg R.1) R.2))
  rw [toReal_mul]
  exact invsqrt_newton hr hy hk hρ

end TM

end BirkhoffGlobalSection.TangentialHessian.Checker


