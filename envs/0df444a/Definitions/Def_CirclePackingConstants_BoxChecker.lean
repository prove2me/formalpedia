-- Prove2me | Definitions.Def_CirclePackingConstants_BoxChecker
-- name    : CirclePackingConstants_BoxChecker
-- status  : Definition
-- author  : @vebis
-- created : 2026-10-06T15:04:03.895005+00:00
-- url     : https://prove2.me/theorems/276f1471-0fa0-47f0-9d86-7de77b8e47d1
-- title:
--   A certified box checker for strictly separated points
-- statement:
--   A *box state* for $r$ points of the plane consists of an axis-parallel box $[x_l,x_h]\times[y_l,y_h]$ with integer endpoints (in units $1/M$, $M=12\cdot2^{24}$) for each point, packed into one natural number. The checker `checkS` verifies a finite certificate that no points in the boxes can have all pairwise squared distances greater than $\tfrac19$. The certificate is a stream of integers describing a tree: at every node a list of *tightening steps* is executed, then the node either closes (a contradiction is found), splits one box at a computed point (given by a fraction code), or is a *leaf* accepted by an external predicate.
--
--   A tightening step for the pair $(p,q)$ and an axis uses the following fact: if the boxes force $|y_p-y_q|\le Y/M$ and $W\ge0$ satisfies $9(W^2+Y^2)\le M^2$, then $(x_p-x_q)^2>\tfrac19-Y^2/M^2\ge W^2/M^2$, hence $x_p\ge x_q+W/M$ or $x_p\le x_q-W/M$, and the box of $p$ is replaced by the hull of the intersection of its box with this union (the branch is closed if the intersection is empty). The integer $W$ is recomputed from the state by a Newton iteration for the integer square root of $(M^2-9Y^2)/9$; its exactness is not needed for soundness, since the guard $9(W^2+Y^2)\le M^2$ is re-checked. An *order step* uses a given constraint $x_p\le x_q$.
--
--   The main results are `tighten_sound`, `order_sound` and `checkS_sound`: if the checker accepts a certificate in a state `S` and real points lie in the boxes of `S` with all pairwise squared distances $>\tfrac19$ (and satisfy the order constraints), then the leaf predicate cannot hold, i.e. the situation is contradictory.
--
--   **Formalization Note.** The state is a single natural number with fields of width $2^{30}$; the kernel evaluates the checker with `decide +kernel`. The file contains the definitions together with their soundness proofs; no axioms beyond `propext`, `Classical.choice` and `Quot.sound` are used.
-- source:
--   G. Wengerodt, Die dichteste Packung von 16 Kreisen in einem Quadrat, Beitraege zur Algebra und Geometrie 16 (1983), 173-190 (optimality of the 4x4 grid); the occupancy-pattern decomposition, the pattern library and the certificates are computer generated for this formalization.

import Definitions.Def_CirclePackingConstants

open CirclePackingConstants

namespace CPQ

inductive Tree where
  | closed : Nat → List Nat → Tree
  | split : Nat → List Nat → Nat → Nat → Nat → Tree → Tree → Tree

abbrev TC := @Tree.closed
abbrev TS := @Tree.split

def M : Nat := 12 * 2 ^ 24
def MM : Nat := M * M
def FW : Nat := 2 ^ 30

def fld (S i : Nat) : Nat := S / 2 ^ (30 * i) % FW
def setf (S i v : Nat) : Nat := S - fld S i * 2 ^ (30 * i) + v * 2 ^ (30 * i)

def adiff (a b : Nat) : Nat := bif Nat.ble b a then a - b else b - a
def nmax (a b : Nat) : Nat := bif Nat.ble a b then b else a
def nmin (a b : Nat) : Nat := bif Nat.ble a b then a else b

/-- result: none = invalid certificate; some none = contradiction (branch closed); some (some S') = new state -/
def tightenStep (n : Nat) (S : Nat) (p q : Nat) (ax : Nat) (W : Nat) : Option (Option Nat) :=
  bif Nat.beq p q || !(Nat.ble (p + 1) n) || !(Nat.ble (q + 1) n) || !(Nat.ble ax 1) then none else
  let o := 1 - ax
  let Plo := fld S (4 * p + 2 * ax)
  let Phi := fld S (4 * p + 2 * ax + 1)
  let Qlo := fld S (4 * q + 2 * ax)
  let Qhi := fld S (4 * q + 2 * ax + 1)
  let Y := nmax (adiff (fld S (4 * p + 2 * o)) (fld S (4 * q + 2 * o + 1))) (adiff (fld S (4 * p + 2 * o + 1)) (fld S (4 * q + 2 * o)))
  bif Nat.ble (9 * (W * W + Y * Y)) MM then
    let s1 := Nat.ble (Qlo + W) Phi
    let s2 := Nat.ble (Plo + W) Qhi
    bif s1 || s2 then
      let nl := bif s2 then Plo else nmax Plo (Qlo + W)
      let nh := bif s1 then Phi else nmin Phi (Qhi - W)
      some (some (setf (setf S (4 * p + 2 * ax) nl) (4 * p + 2 * ax + 1) nh))
    else some none
  else none

/-- order step: x_p ≤ x_q (only allowed when (p,q) ∈ ords) -/
def orderStep (n : Nat) (ords : List (Nat × Nat)) (S : Nat) (p q : Nat) : Option (Option Nat) :=
  bif !(decide ((p, q) ∈ ords)) || !(Nat.ble (p + 1) n) || !(Nat.ble (q + 1) n) then none else
  let Pxl := fld S (4 * p)
  let Pxh := fld S (4 * p + 1)
  let Qxl := fld S (4 * q)
  let Qxh := fld S (4 * q + 1)
  let nQl := nmax Qxl Pxl
  let nPh := nmin Pxh Qxh
  bif Nat.ble nQl Qxh && Nat.ble Pxl nPh then
    some (some (setf (setf (setf (setf S (4 * q) nQl) (4 * q + 1) Qxh) (4 * p) Pxl) (4 * p + 1) nPh))
  else some none

inductive Res where
  | contra : Res
  | bad : Res
  | ok : Nat → Res

def isqLoop : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | k+1, N, x =>
    let x' := (x + N / x) / 2
    bif Nat.ble x x' then x else isqLoop k N x'

/-- integer square root of N (= (M^2 - 9 Y^2)/9) by Newton iteration from the start M/3 - 3Y^2/(2M) + 1; exactness is not needed for soundness (tightenStep re-checks the guard) -/
def isqF (N Y : Nat) : Nat := isqLoop 60 N (M / 3 - 3 * Y * Y / (2 * M) + 1)

/-- the certified half-gap W for the pair (p,q) on axis ax, recomputed from the state -/
def wOfState (S p q ax : Nat) : Nat :=
  let o := 1 - ax
  let Y := nmax (adiff (fld S (4 * p + 2 * o)) (fld S (4 * q + 2 * o + 1))) (adiff (fld S (4 * p + 2 * o + 1)) (fld S (4 * q + 2 * o)))
  isqF ((MM - 9 * Y * Y) / 9) Y

/-- command c = p + 16 q + 256 ax ; ax = 2 means an order step -/
def runOne (n : Nat) (ords : List (Nat × Nat)) (c : Nat) (S : Nat) : Option (Option Nat) :=
  bif Nat.beq (c / 256 % 4) 2 then orderStep n ords S (c % 16) (c / 16 % 16)
  else tightenStep n S (c % 16) (c / 16 % 16) (c / 256 % 4) (wOfState S (c % 16) (c / 16 % 16) (c / 256 % 4))

def runGroup (n : Nat) (ords : List (Nat × Nat)) : Nat → Nat → Nat → Nat → Res
  | 0, _, S, _ => .ok S
  | k+1, g, S, m =>
    bif Nat.beq m 0 then .ok S else
    match runOne n ords (g % 1024) S with
    | none => .bad
    | some none => .contra
    | some (some S') => runGroup n ords k (g / 1024) S' (m - 1)

def runCmds (n : Nat) (ords : List (Nat × Nat)) : Nat → List Nat → Nat → Res
  | _, [], S => .ok S
  | m, g :: t, S =>
    match runGroup n ords 16 g S m with
    | .ok S' => runCmds n ords (m - 16) t S'
    | r => r

/-- split fractions (numerator, denominator) -/
def fracNum (fi : Nat) : Nat := bif Nat.beq fi 0 then 1 else bif Nat.beq fi 1 then 7 else bif Nat.beq fi 2 then 13 else bif Nat.beq fi 3 then 1 else bif Nat.beq fi 4 then 3 else bif Nat.beq fi 5 then 21 else 29
def fracDen (fi : Nat) : Nat := bif Nat.beq fi 0 then 2 else bif Nat.beq fi 1 then 20 else bif Nat.beq fi 2 then 20 else bif Nat.beq fi 3 then 4 else bif Nat.beq fi 4 then 4 else bif Nat.beq fi 5 then 50 else 50

/-- split value from the current box of point p on axis ax -/
def splitV (S : Nat) (p ax fi : Nat) : Nat :=
  fld S (4 * p + 2 * ax) + (fld S (4 * p + 2 * ax + 1) - fld S (4 * p + 2 * ax)) * fracNum fi / fracDen fi

def check (n : Nat) (ords : List (Nat × Nat)) : Tree → Nat → Bool
  | .closed m cs, S => match runCmds n ords m cs S with | .contra => true | _ => false
  | .split m cs p ax v l r, S =>
    match runCmds n ords m cs S with
    | .contra => true
    | .bad => false
    | .ok S' =>
      bif Nat.ble (p + 1) n && Nat.ble ax 1 && Nat.ble (splitV S' p ax v + 1) FW then
        check n ords l (setf (setf S' (4 * p + 2 * ax) (fld S' (4 * p + 2 * ax))) (4 * p + 2 * ax + 1) (splitV S' p ax v)) &&
        check n ords r (setf (setf S' (4 * p + 2 * ax) (splitV S' p ax v)) (4 * p + 2 * ax + 1) (fld S' (4 * p + 2 * ax + 1)))
      else false

end CPQ

namespace CPQ

theorem fld_lt (S i : Nat) : fld S i < FW := Nat.mod_lt _ (by unfold FW; positivity)

theorem pow30 (j : Nat) : 2 ^ (30 * j) = FW ^ j := by
  unfold FW; rw [pow_mul]

theorem fld_eq (S j : Nat) : fld S j = S / FW ^ j % FW := by
  unfold fld; rw [pow30]

theorem FW_pos : 0 < FW := by unfold FW; positivity

theorem fld_of_decomp (A c B i j : Nat) (hA : A < FW ^ i) (hc : c < FW) :
    (A + FW ^ i * (c + FW * B)) / FW ^ j % FW =
      if j < i then A / FW ^ j % FW else if j = i then c else B / FW ^ (j - i - 1) % FW := by
  have hFW := FW_pos
  have hcB : (c + FW * B) / FW = B := by
    rw [Nat.add_mul_div_left _ _ hFW, Nat.div_eq_of_lt hc, zero_add]
  rcases lt_trichotomy j i with hj | hj | hj
  · rw [if_pos hj]
    obtain ⟨d, hd⟩ : ∃ d, i = j + d + 1 := ⟨i - j - 1, by omega⟩
    subst hd
    have e : FW ^ (j + d + 1) = FW ^ j * (FW ^ d * FW) := by rw [pow_succ, pow_add, mul_assoc]
    have h1 : (A + FW ^ (j + d + 1) * (c + FW * B)) / FW ^ j
        = A / FW ^ j + FW ^ d * FW * (c + FW * B) := by
      rw [e, mul_assoc, Nat.add_mul_div_left _ _ (by positivity)]
    rw [h1]
    have h2 : FW ^ d * FW * (c + FW * B) = FW * (FW ^ d * (c + FW * B)) := by ring
    rw [h2, Nat.add_mul_mod_self_left]
  · rw [if_neg (by omega), if_pos hj]
    subst hj
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · rw [if_neg (by omega), if_neg (by omega)]
    obtain ⟨e, he⟩ : ∃ e, j = i + 1 + e := ⟨j - i - 1, by omega⟩
    subst he
    have hpow : FW ^ (i + 1 + e) = FW ^ i * (FW * FW ^ e) := by
      rw [show i + 1 + e = i + (1 + e) by omega, pow_add, pow_add, pow_one]
    rw [hpow, ← Nat.div_div_eq_div_mul]
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add]
    rw [← Nat.div_div_eq_div_mul, hcB]
    have : i + 1 + e - i - 1 = e := by omega
    rw [this]

theorem decomp_fld (S i : Nat) :
    S = S % FW ^ i + FW ^ i * (fld S i + FW * (S / FW ^ (i + 1))) := by
  have hFW := FW_pos
  have h1 : S = S % FW ^ i + FW ^ i * (S / FW ^ i) := (Nat.mod_add_div S (FW ^ i)).symm
  have h2 : S / FW ^ i = fld S i + FW * (S / FW ^ (i + 1)) := by
    rw [fld_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    have := Nat.mod_add_div (S / FW ^ i) FW
    omega
  rw [← h2]; exact h1

theorem setf_decomp (S i v : Nat) :
    setf S i v = S % FW ^ i + FW ^ i * (v + FW * (S / FW ^ (i + 1))) := by
  unfold setf
  rw [pow30]
  have h := decomp_fld S i
  generalize S % FW ^ i = A at *
  generalize S / FW ^ (i + 1) = B at *
  generalize hf : fld S i = f at *
  generalize FW ^ i = P at *
  have h2 : S - f * P = A + P * (FW * B) := by
    apply Nat.sub_eq_of_eq_add
    rw [h]; ring
  rw [h2]; ring

theorem fld_decomp_val (A c B i j : Nat) (hA : A < FW ^ i) (hc : c < FW) :
    fld (A + FW ^ i * (c + FW * B)) j =
      if j < i then A / FW ^ j % FW else if j = i then c else B / FW ^ (j - i - 1) % FW := by
  rw [fld_eq, fld_of_decomp _ _ _ _ _ hA hc]

theorem fld_setf (S i v j : Nat) (hv : v < FW) :
    fld (setf S i v) j = if j = i then v else fld S j := by
  have hFW := FW_pos
  have hA : S % FW ^ i < FW ^ i := Nat.mod_lt _ (by positivity)
  have hf := fld_lt S i
  have hS := congrArg (fun T => fld T j) (decomp_fld S i)
  rw [setf_decomp, fld_decomp_val _ _ _ _ _ hA hv, hS, fld_decomp_val _ _ _ _ _ hA hf]
  rcases lt_trichotomy j i with hj | hj | hj
  · simp [hj, hj.ne]
  · simp [hj]
  · simp [hj.ne', not_lt.2 hj.le]

end CPQ

open CirclePackingConstants

namespace CPQ

theorem M_pos : (0 : ℝ) < (M : ℝ) := by unfold M; norm_num

theorem ble_t {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by simpa using h
theorem ble_f {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hh : Nat.ble a b
  · rfl
  · exact absurd (by simpa using hh) h

theorem nmax_eq (a b : Nat) : nmax a b = max a b := by
  unfold nmax
  by_cases h : a ≤ b
  · rw [ble_t h]; simp [Nat.max_eq_right h]
  · have : b ≤ a := by omega
    rw [ble_f h]; simp [Nat.max_eq_left this]

theorem nmin_eq (a b : Nat) : nmin a b = min a b := by
  unfold nmin
  by_cases h : a ≤ b
  · rw [ble_t h]; simp [Nat.min_eq_left h]
  · have : b ≤ a := by omega
    rw [ble_f h]; simp [Nat.min_eq_right this]

theorem adiff_eq (a b : Nat) : adiff a b = if b ≤ a then a - b else b - a := by
  unfold adiff
  by_cases h : b ≤ a
  · rw [ble_t h]; simp [h]
  · rw [ble_f h]; simp [h]

def cx (ax : Nat) (a : ℝ × ℝ) : ℝ := if ax = 0 then a.1 else a.2

def InS (S k : Nat) (a : ℝ × ℝ) : Prop :=
  (fld S (4 * k) : ℝ) ≤ a.1 * M ∧ a.1 * M ≤ (fld S (4 * k + 1) : ℝ) ∧
  (fld S (4 * k + 2) : ℝ) ≤ a.2 * M ∧ a.2 * M ≤ (fld S (4 * k + 3) : ℝ)

def Sat (n : Nat) (ords : List (Nat × Nat)) (S : Nat) (pt : Nat → ℝ × ℝ) : Prop :=
  (∀ k, k < n → InS S k (pt k)) ∧
  (∀ k l, k < n → l < n → k ≠ l → (1 : ℝ) / 9 < sqDist (pt k) (pt l)) ∧
  (∀ a b, (a, b) ∈ ords → (pt a).1 ≤ (pt b).1)

theorem adiff_cast (a b : Nat) : ((adiff a b : Nat) : ℝ) = |(a : ℝ) - b| := by
  rw [adiff_eq]
  split_ifs with h
  · have h' : (b : ℝ) ≤ a := Nat.cast_le.2 h
    rw [Nat.cast_sub h, abs_of_nonneg (by linarith)]
  · have h' : (a : ℝ) ≤ b := Nat.cast_le.2 (by omega)
    rw [Nat.cast_sub (by omega), abs_of_nonpos (by linarith)]
    ring

theorem sqDist_split (ax : Nat) (hax : ax ≤ 1) (a b : ℝ × ℝ) :
    sqDist a b = (cx ax a - cx ax b) ^ 2 + (cx (1 - ax) a - cx (1 - ax) b) ^ 2 := by
  rcases (by omega : ax = 0 ∨ ax = 1) with h | h <;> subst h <;> simp [sqDist, cx] <;> ring

theorem inS_ax {S k : Nat} {a : ℝ × ℝ} (h : InS S k a) (ax : Nat) (hax : ax ≤ 1) :
    (fld S (4 * k + 2 * ax) : ℝ) ≤ cx ax a * M ∧ cx ax a * M ≤ (fld S (4 * k + 2 * ax + 1) : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases (by omega : ax = 0 ∨ ax = 1) with e | e
  · subst e
    have hc : cx 0 a = a.1 := by simp [cx]
    rw [hc]
    have e1 : 4 * k + 2 * 0 = 4 * k := by omega
    have e2 : 4 * k + 2 * 0 + 1 = 4 * k + 1 := by omega
    rw [e1, e2]; exact ⟨h1, h2⟩
  · subst e
    have hc : cx 1 a = a.2 := by simp [cx]
    rw [hc]
    have e1 : 4 * k + 2 * 1 = 4 * k + 2 := by omega
    have e2 : 4 * k + 2 * 1 + 1 = 4 * k + 3 := by omega
    rw [e1, e2]; exact ⟨h3, h4⟩

theorem core_scaled (X Y O O' : ℝ) (l h ql qh ol oh qol qoh W : Nat)
    (hx1 : (l : ℝ) ≤ X) (hx2 : X ≤ (h : ℝ))
    (hy1 : (ql : ℝ) ≤ Y) (hy2 : Y ≤ (qh : ℝ))
    (ho1 : (ol : ℝ) ≤ O) (ho2 : O ≤ (oh : ℝ))
    (hq1 : (qol : ℝ) ≤ O') (hq2 : O' ≤ (qoh : ℝ))
    (hsep : (M : ℝ) ^ 2 / 9 < (X - Y) ^ 2 + (O - O') ^ 2)
    (hW : 9 * (W * W + (max (adiff ol qoh) (adiff oh qol)) * (max (adiff ol qoh) (adiff oh qol))) ≤ M * M) :
    (ql + W ≤ h ∨ l + W ≤ qh) ∧
    (((if l + W ≤ qh then l else max l (ql + W) : Nat) : ℝ) ≤ X) ∧
    (X ≤ ((if ql + W ≤ h then h else min h (qh - W) : Nat) : ℝ)) := by
  set Yn : Nat := max (adiff ol qoh) (adiff oh qol) with hY
  have e1 : ((adiff ol qoh : Nat) : ℝ) = |(ol : ℝ) - qoh| := adiff_cast _ _
  have e2 : ((adiff oh qol : Nat) : ℝ) = |(oh : ℝ) - qol| := adiff_cast _ _
  have g1 : (|(ol : ℝ) - qoh| : ℝ) ≤ Yn := by rw [← e1]; exact_mod_cast le_max_left _ _
  have g2 : (|(oh : ℝ) - qol| : ℝ) ≤ Yn := by rw [← e2]; exact_mod_cast le_max_right _ _
  have a1 := abs_le.1 g1
  have a2 := abs_le.1 g2
  have hOO : (O - O') ^ 2 ≤ (Yn : ℝ) ^ 2 := by
    apply sq_le_sq' <;> linarith [a1.1, a1.2, a2.1, a2.2]
  have hWr : (9 : ℝ) * ((W : ℝ) * W + (Yn : ℝ) * Yn) ≤ (M : ℝ) * M := by exact_mod_cast hW
  have hlt : (W : ℝ) ^ 2 < (X - Y) ^ 2 := by nlinarith
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have habs : (W : ℝ) < |X - Y| := by
    by_contra hc
    replace hc := not_lt.1 hc
    have := sq_le_sq' (by linarith [abs_le.1 hc]) (abs_le.1 hc).2
    linarith [sq_abs (X - Y)]
  rcases lt_abs.1 habs with hA | hB
  · have hs1 : ql + W < h := by
      have : ((ql : ℝ) + W) < h := by linarith
      exact_mod_cast this
    have hs1' : ql + W ≤ h := hs1.le
    refine ⟨Or.inl hs1', ?_, ?_⟩
    · split_ifs with hc
      · exact hx1
      · have : ((max l (ql + W) : Nat) : ℝ) ≤ X := by
          rw [Nat.cast_max]
          apply max_le hx1
          push_cast; linarith
        exact this
    · rw [if_pos hs1']; exact hx2
  · have hs2 : l + W < qh := by
      have : ((l : ℝ) + W) < qh := by linarith
      exact_mod_cast this
    have hs2' : l + W ≤ qh := hs2.le
    refine ⟨Or.inr hs2', ?_, ?_⟩
    · rw [if_pos hs2']; exact hx1
    · split_ifs with hc
      · exact hx2
      · have hWq : W ≤ qh := by omega
        have : X ≤ ((min h (qh - W) : Nat) : ℝ) := by
          rw [Nat.cast_min]
          apply le_min hx2
          rw [Nat.cast_sub hWq]; linarith
        exact this

end CPQ

namespace CPQ

theorem fld_set2 (S a b nl nh j : Nat) (hnl : nl < FW) (hnh : nh < FW) :
    fld (setf (setf S a nl) b nh) j = if j = b then nh else if j = a then nl else fld S j := by
  rw [fld_setf _ _ _ _ hnh, fld_setf _ _ _ _ hnl]

/-- new state satisfies the box facts when only the axis fields of point p changed -/
theorem sat_update {n : Nat} {ords : List (Nat × Nat)} {S : Nat} {pt : Nat → ℝ × ℝ}
    (hs : Sat n ords S pt) (p ax nl nh : Nat) (hax : ax ≤ 1) (hp : p < n)
    (hnl : nl < FW) (hnh : nh < FW)
    (h1 : (nl : ℝ) ≤ cx ax (pt p) * M) (h2 : cx ax (pt p) * M ≤ (nh : ℝ)) :
    Sat n ords (setf (setf S (4 * p + 2 * ax) nl) (4 * p + 2 * ax + 1) nh) pt := by
  refine ⟨?_, hs.2.1, hs.2.2⟩
  intro k hk
  have hk' := hs.1 k hk
  obtain ⟨c1, c2, c3, c4⟩ := hk'
  by_cases hkp : k = p
  · subst hkp
    rcases (by omega : ax = 0 ∨ ax = 1) with e | e
    · subst e
      have hc : cx 0 (pt k) = (pt k).1 := by simp [cx]
      rw [hc] at h1 h2
      have f0 := fld_set2 S (4 * k + 2 * 0) (4 * k + 2 * 0 + 1) nl nh (4 * k) hnl hnh
      have f1 := fld_set2 S (4 * k + 2 * 0) (4 * k + 2 * 0 + 1) nl nh (4 * k + 1) hnl hnh
      have f2 := fld_set2 S (4 * k + 2 * 0) (4 * k + 2 * 0 + 1) nl nh (4 * k + 2) hnl hnh
      have f3 := fld_set2 S (4 * k + 2 * 0) (4 * k + 2 * 0 + 1) nl nh (4 * k + 3) hnl hnh
      rw [if_neg (by omega), if_pos (by omega)] at f0
      rw [if_pos (by omega)] at f1
      rw [if_neg (by omega), if_neg (by omega)] at f2
      rw [if_neg (by omega), if_neg (by omega)] at f3
      unfold InS
      rw [f0, f1, f2, f3]
      exact ⟨h1, h2, c3, c4⟩
    · subst e
      have hc : cx 1 (pt k) = (pt k).2 := by simp [cx]
      rw [hc] at h1 h2
      have f0 := fld_set2 S (4 * k + 2 * 1) (4 * k + 2 * 1 + 1) nl nh (4 * k) hnl hnh
      have f1 := fld_set2 S (4 * k + 2 * 1) (4 * k + 2 * 1 + 1) nl nh (4 * k + 1) hnl hnh
      have f2 := fld_set2 S (4 * k + 2 * 1) (4 * k + 2 * 1 + 1) nl nh (4 * k + 2) hnl hnh
      have f3 := fld_set2 S (4 * k + 2 * 1) (4 * k + 2 * 1 + 1) nl nh (4 * k + 3) hnl hnh
      rw [if_neg (by omega), if_neg (by omega)] at f0
      rw [if_neg (by omega), if_neg (by omega)] at f1
      rw [if_neg (by omega), if_pos (by omega)] at f2
      rw [if_pos (by omega)] at f3
      unfold InS
      rw [f0, f1, f2, f3]
      exact ⟨c1, c2, h1, h2⟩
  · have f0 := fld_set2 S (4 * p + 2 * ax) (4 * p + 2 * ax + 1) nl nh (4 * k) hnl hnh
    have f1 := fld_set2 S (4 * p + 2 * ax) (4 * p + 2 * ax + 1) nl nh (4 * k + 1) hnl hnh
    have f2 := fld_set2 S (4 * p + 2 * ax) (4 * p + 2 * ax + 1) nl nh (4 * k + 2) hnl hnh
    have f3 := fld_set2 S (4 * p + 2 * ax) (4 * p + 2 * ax + 1) nl nh (4 * k + 3) hnl hnh
    rw [if_neg (by omega), if_neg (by omega)] at f0 f1 f2 f3
    unfold InS
    rw [f0, f1, f2, f3]
    exact ⟨c1, c2, c3, c4⟩

theorem sat_update' {n : Nat} {ords : List (Nat × Nat)} {S : Nat} {pt : Nat → ℝ × ℝ}
    (hs : Sat n ords S pt) (p ax nl nh a b : Nat) (hax : ax ≤ 1) (hp : p < n)
    (hnl : nl < FW) (hnh : nh < FW)
    (h1 : (nl : ℝ) ≤ cx ax (pt p) * M) (h2 : cx ax (pt p) * M ≤ (nh : ℝ))
    (ha : a = 4 * p + 2 * ax) (hb : b = 4 * p + 2 * ax + 1) :
    Sat n ords (setf (setf S a nl) b nh) pt := by
  subst ha hb
  exact sat_update hs p ax nl nh hax hp hnl hnh h1 h2

end CPQ

namespace CPQ

theorem guard_facts (n p q ax : Nat) : (Nat.beq p q || !(Nat.ble (p + 1) n) || !(Nat.ble (q + 1) n) || !(Nat.ble ax 1)) = false ↔ (p ≠ q ∧ p < n ∧ q < n ∧ ax ≤ 1) := by
  constructor
  · intro h
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro e; subst e; simp at h1
    · have := Nat.le_of_ble_eq_true h2; omega
    · have := Nat.le_of_ble_eq_true h3; omega
    · exact Nat.le_of_ble_eq_true h4
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false']
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · cases hb : Nat.beq p q
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) h1
    · exact Nat.ble_eq_true_of_le (by omega)
    · exact Nat.ble_eq_true_of_le (by omega)
    · exact Nat.ble_eq_true_of_le h4

theorem tighten_sound {n : Nat} {ords : List (Nat × Nat)} {S : Nat} {pt : Nat → ℝ × ℝ}
    (hs : Sat n ords S pt) (p q ax W : Nat) :
    (tightenStep n S p q ax W = some none → False) ∧
    (∀ S', tightenStep n S p q ax W = some (some S') → Sat n ords S' pt) := by
  have hM := M_pos
  unfold tightenStep
  by_cases hg : (Nat.beq p q || !(Nat.ble (p + 1) n) || !(Nat.ble (q + 1) n) || !(Nat.ble ax 1)) = true
  · rw [hg]; simp
  · have hg' : (Nat.beq p q || !(Nat.ble (p + 1) n) || !(Nat.ble (q + 1) n) || !(Nat.ble ax 1)) = false :=
      Bool.eq_false_iff.2 hg
    rw [hg']
    obtain ⟨hpq, hp, hq, hax⟩ := (guard_facts n p q ax).1 hg'
    simp only [cond_false]
    simp only [Bool.cond_eq_ite, Nat.ble_eq, nmax_eq, nmin_eq, MM, Bool.or_eq_true]
    have hP := hs.1 p hp
    have hQ := hs.1 q hq
    obtain ⟨x1, x2⟩ := inS_ax hP ax hax
    obtain ⟨y1, y2⟩ := inS_ax hQ ax hax
    obtain ⟨o1, o2⟩ := inS_ax hP (1 - ax) (by omega)
    obtain ⟨q1, q2⟩ := inS_ax hQ (1 - ax) (by omega)
    have hsep := hs.2.1 p q hp hq hpq
    rw [sqDist_split ax hax] at hsep
    have hsc : (M : ℝ) ^ 2 / 9 < (cx ax (pt p) * M - cx ax (pt q) * M) ^ 2 +
        (cx (1 - ax) (pt p) * M - cx (1 - ax) (pt q) * M) ^ 2 := by
      have e : (cx ax (pt p) * M - cx ax (pt q) * M) ^ 2 +
          (cx (1 - ax) (pt p) * M - cx (1 - ax) (pt q) * M) ^ 2 =
          ((cx ax (pt p) - cx ax (pt q)) ^ 2 + (cx (1 - ax) (pt p) - cx (1 - ax) (pt q)) ^ 2) * (M : ℝ) ^ 2 := by ring
      rw [e]
      have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
      nlinarith
    by_cases hW : 9 * (W * W + max (adiff (fld S (4 * p + 2 * (1 - ax))) (fld S (4 * q + 2 * (1 - ax) + 1)))
          (adiff (fld S (4 * p + 2 * (1 - ax) + 1)) (fld S (4 * q + 2 * (1 - ax)))) *
        max (adiff (fld S (4 * p + 2 * (1 - ax))) (fld S (4 * q + 2 * (1 - ax) + 1)))
          (adiff (fld S (4 * p + 2 * (1 - ax) + 1)) (fld S (4 * q + 2 * (1 - ax))))) ≤ M * M
    · rw [if_pos hW]
      obtain ⟨hor, hlo, hhi⟩ := core_scaled _ _ _ _ _ _ _ _ _ _ _ _ _ x1 x2 y1 y2 o1 o2 q1 q2 hsc hW
      rw [if_pos (by rcases hor with h | h; exact Or.inl h; exact Or.inr h)]
      have hnl : (if fld S (4 * p + 2 * ax) + W ≤ fld S (4 * q + 2 * ax + 1) then fld S (4 * p + 2 * ax)
          else max (fld S (4 * p + 2 * ax)) (fld S (4 * q + 2 * ax) + W)) < FW := by
        split_ifs with hc
        · exact fld_lt _ _
        · have hh : fld S (4 * q + 2 * ax) + W ≤ fld S (4 * p + 2 * ax + 1) := by
            rcases hor with h | h
            · exact h
            · exact absurd h hc
          exact max_lt (fld_lt _ _) (lt_of_le_of_lt hh (fld_lt _ _))
      have hnh : (if fld S (4 * q + 2 * ax) + W ≤ fld S (4 * p + 2 * ax + 1) then fld S (4 * p + 2 * ax + 1)
          else min (fld S (4 * p + 2 * ax + 1)) (fld S (4 * q + 2 * ax + 1) - W)) < FW := by
        split_ifs with hc
        · exact fld_lt _ _
        · exact lt_of_le_of_lt (min_le_left _ _) (fld_lt _ _)
      refine ⟨(fun h => absurd (Option.some.inj h) (by simp)), fun S' hS' => ?_⟩
      obtain rfl := Option.some.inj (Option.some.inj hS')
      exact sat_update hs p ax _ _ hax hp hnl hnh hlo hhi
    · rw [if_neg hW]
      simp

end CPQ

namespace CPQ

theorem order_sound {n : Nat} {ords : List (Nat × Nat)} {S : Nat} {pt : Nat → ℝ × ℝ}
    (hs : Sat n ords S pt) (p q : Nat) :
    (orderStep n ords S p q = some none → False) ∧
    (∀ S', orderStep n ords S p q = some (some S') → Sat n ords S' pt) := by
  have hM := M_pos
  unfold orderStep
  by_cases hg : (!(decide ((p, q) ∈ ords)) || !(Nat.ble (p + 1) n) || !(Nat.ble (q + 1) n)) = true
  · rw [hg]; simp
  · have hg' : (!(decide ((p, q) ∈ ords)) || !(Nat.ble (p + 1) n) || !(Nat.ble (q + 1) n)) = false :=
      Bool.eq_false_iff.2 hg
    rw [hg']
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at hg'
    obtain ⟨⟨hmem, h1⟩, h2⟩ := hg'
    have hp : p < n := by have := Nat.le_of_ble_eq_true h1; omega
    have hq : q < n := by have := Nat.le_of_ble_eq_true h2; omega
    simp only [cond_false]
    have hord := hs.2.2 p q hmem
    have hP := hs.1 p hp
    have hQ := hs.1 q hq
    obtain ⟨a1, a2, a3, a4⟩ := hP
    obtain ⟨b1, b2, b3, b4⟩ := hQ
    have hxx : (pt p).1 * M ≤ (pt q).1 * M := mul_le_mul_of_nonneg_right hord hM.le
    simp only [Bool.cond_eq_ite, Nat.ble_eq, nmax_eq, nmin_eq, Bool.and_eq_true]
    by_cases hc : max (fld S (4 * q)) (fld S (4 * p)) ≤ fld S (4 * q + 1) ∧
        fld S (4 * p) ≤ min (fld S (4 * p + 1)) (fld S (4 * q + 1))
    · rw [if_pos hc]
      refine ⟨(fun h => absurd (Option.some.inj h) (by simp)), fun S' hS' => ?_⟩
      obtain rfl := Option.some.inj (Option.some.inj hS')
      have hl : fld S (4 * q) ⊔ fld S (4 * p) < FW := lt_of_le_of_lt hc.1 (fld_lt _ _)
      have hr : min (fld S (4 * p + 1)) (fld S (4 * q + 1)) < FW :=
        lt_of_le_of_lt (min_le_left _ _) (fld_lt _ _)
      have hc0 : cx 0 (pt q) = (pt q).1 := by simp [cx]
      have hc0p : cx 0 (pt p) = (pt p).1 := by simp [cx]
      have s1 := sat_update' hs q 0 (max (fld S (4 * q)) (fld S (4 * p))) (fld S (4 * q + 1))
        (4 * q) (4 * q + 1) (by omega) hq (by simpa using hl) (fld_lt _ _)
        (by rw [hc0, Nat.cast_max]; exact max_le b1 (by linarith))
        (by rw [hc0]; exact b2) (by omega) (by omega)
      have s2 := sat_update' s1 p 0 (fld S (4 * p)) (min (fld S (4 * p + 1)) (fld S (4 * q + 1)))
        (4 * p) (4 * p + 1) (by omega) hp (fld_lt _ _) hr
        (by rw [hc0p]; exact a1)
        (by rw [hc0p, Nat.cast_min]; exact le_min a2 (by linarith)) (by omega) (by omega)
      exact s2
    · exfalso
      apply hc
      refine ⟨?_, ?_⟩
      · apply max_le
        · have : ((fld S (4 * q) : Nat) : ℝ) ≤ (fld S (4 * q + 1) : ℝ) := by
            have := b1.trans b2; exact_mod_cast (by exact_mod_cast this : (fld S (4 * q) : ℝ) ≤ fld S (4 * q + 1))
          exact_mod_cast this
        · have : ((fld S (4 * p) : Nat) : ℝ) ≤ (fld S (4 * q + 1) : ℝ) := by linarith
          exact_mod_cast this
      · apply le_min
        · have : ((fld S (4 * p) : Nat) : ℝ) ≤ (fld S (4 * p + 1) : ℝ) := by linarith
          exact_mod_cast this
        · have : ((fld S (4 * p) : Nat) : ℝ) ≤ (fld S (4 * q + 1) : ℝ) := by linarith
          exact_mod_cast this

end CPQ

namespace CPQ

theorem runOne_sound {n : Nat} {ords : List (Nat × Nat)} {S : Nat} {pt : Nat → ℝ × ℝ}
    (hs : Sat n ords S pt) (c : Nat) :
    (runOne n ords c S = some none → False) ∧
    (∀ S', runOne n ords c S = some (some S') → Sat n ords S' pt) := by
  unfold runOne
  by_cases h : Nat.beq (c / 256 % 4) 2 = true
  · rw [h]; exact order_sound hs _ _
  · have h' : Nat.beq (c / 256 % 4) 2 = false := Bool.eq_false_iff.2 h
    rw [h']; exact tighten_sound hs _ _ _ _

theorem runGroup_sound {n : Nat} {ords : List (Nat × Nat)} {pt : Nat → ℝ × ℝ} :
    ∀ (k g S m : Nat), Sat n ords S pt →
      (runGroup n ords k g S m = .contra → False) ∧ (∀ S', runGroup n ords k g S m = .ok S' → Sat n ords S' pt) := by
  intro k
  induction k with
  | zero =>
    intro g S m hs
    refine ⟨fun h => by simp [runGroup] at h, fun S' h => ?_⟩
    simp [runGroup] at h
    subst h; exact hs
  | succ k ih =>
    intro g S m hs
    unfold runGroup
    by_cases hm : Nat.beq m 0 = true
    · rw [hm]
      refine ⟨fun h => by simp at h, fun S' h => ?_⟩
      simp at h
      subst h; exact hs
    · have hm' : Nat.beq m 0 = false := Bool.eq_false_iff.2 hm
      rw [hm']
      simp only [cond_false]
      have key := runOne_sound hs (g % 1024)
      rcases h : runOne n ords (g % 1024) S with _ | _ | S1
      · simp
      · exact ⟨fun _ => key.1 h, fun S' hb => by simp at hb⟩
      · have hs1 := key.2 S1 h
        have := ih (g / 1024) S1 (m - 1) hs1
        simpa using this

theorem runCmds_sound {n : Nat} {ords : List (Nat × Nat)} {pt : Nat → ℝ × ℝ} :
    ∀ (gs : List Nat) (m S : Nat), Sat n ords S pt →
      (runCmds n ords m gs S = .contra → False) ∧ (∀ S', runCmds n ords m gs S = .ok S' → Sat n ords S' pt) := by
  intro gs
  induction gs with
  | nil =>
    intro m S hs
    refine ⟨fun h => by simp [runCmds] at h, fun S' h => ?_⟩
    simp [runCmds] at h
    subst h; exact hs
  | cons g t ih =>
    intro m S hs
    have key := runGroup_sound (n := n) (ords := ords) (pt := pt) 16 g S m hs
    unfold runCmds
    rcases h : runGroup n ords 16 g S m with _ | _ | S1
    · exact ⟨fun _ => key.1 h, fun S' hb => by simp at hb⟩
    · simp
    · have hs1 := key.2 S1 h
      have := ih (m - 16) S1 hs1
      simpa using this

theorem check_sound {n : Nat} {ords : List (Nat × Nat)} {pt : Nat → ℝ × ℝ} :
    ∀ (t : Tree) (S : Nat), check n ords t S = true → Sat n ords S pt → False := by
  intro t
  induction t with
  | closed m cs =>
    intro S h hs
    unfold check at h
    have key := runCmds_sound (n := n) (ords := ords) (pt := pt) cs m S hs
    rcases hr : runCmds n ords m cs S with _ | _ | S1
    · exact key.1 hr
    · simp [hr] at h
    · simp [hr] at h
  | split m cs p ax v l r ihl ihr =>
    intro S h hs
    unfold check at h
    have key := runCmds_sound (n := n) (ords := ords) (pt := pt) cs m S hs
    rcases hr : runCmds n ords m cs S with _ | _ | S1
    · exact key.1 hr
    · simp [hr] at h
    · simp only [hr] at h
      have hs1 := key.2 S1 hr
      by_cases hg : (Nat.ble (p + 1) n && Nat.ble ax 1 && Nat.ble (splitV S1 p ax v + 1) FW) = true
      · rw [hg] at h
        simp only [cond_true, Bool.and_eq_true] at h hg
        obtain ⟨hl, hr'⟩ := h
        obtain ⟨⟨hp1, hax1⟩, hv1⟩ := hg
        have hp : p < n := by have := Nat.le_of_ble_eq_true hp1; omega
        have hax : ax ≤ 1 := Nat.le_of_ble_eq_true hax1
        have hv : splitV S1 p ax v < FW := by have := Nat.le_of_ble_eq_true hv1; omega
        have hM := M_pos
        have hP := hs1.1 p hp
        obtain ⟨c1, c2⟩ := inS_ax hP ax hax
        rcases le_total (cx ax (pt p) * M) ((splitV S1 p ax v : Nat) : ℝ) with hc | hc
        · apply ihl _ hl
          exact sat_update' hs1 p ax (fld S1 (4 * p + 2 * ax)) (splitV S1 p ax v) _ _ hax hp (fld_lt _ _) hv c1 hc rfl rfl
        · apply ihr _ hr'
          exact sat_update' hs1 p ax (splitV S1 p ax v) (fld S1 (4 * p + 2 * ax + 1)) _ _ hax hp hv (fld_lt _ _) hc c2 rfl rfl
      · have hg' : (Nat.ble (p + 1) n && Nat.ble ax 1 && Nat.ble (splitV S1 p ax v + 1) FW) = false := Bool.eq_false_iff.2 hg
        rw [hg'] at h
        simp at h

end CPQ

namespace CPQ

/-- run a list of command fields (each c = p + 16 q + 256 ax) -/
def runList (n : Nat) (ords : List (Nat × Nat)) : List Nat → Nat → Res
  | [], S => .ok S
  | c :: t, S =>
    match runOne n ords c S with
    | none => .bad
    | some none => .contra
    | some (some S') => runList n ords t S'

/-- one node of the stream checker, parametrised by the recursive call `rec`.
    Stream fields (each < 4096): closed node: m (< 2048) followed by m command fields;
    leaf node: 4095, m, then m command fields (accepted iff `lk` holds afterwards);
    split node: 2048 + m, then g = p + 16*ax + 32*fi, then m command fields, then left and right subtrees. -/
def csBody (lk : Nat → Bool) (n : Nat) (ords : List (Nat × Nat)) (rec : List Nat → Nat → Option (List Nat))
    (h : Nat) (rest : List Nat) (S : Nat) : Option (List Nat) :=
  if h = 4095 then
    match rest with
    | [] => none
    | m :: rest2 =>
      match runList n ords (rest2.take m) S with
      | .contra => some (rest2.drop m)
      | .bad => none
      | .ok S' => if lk S' = true then some (rest2.drop m) else none
  else
  if 2048 ≤ h then
    match rest with
    | [] => none
    | g :: rest2 =>
      match runList n ords (rest2.take (h - 2048)) S with
      | .contra => some (rest2.drop (h - 2048))
      | .bad => none
      | .ok S' =>
        if g % 16 + 1 ≤ n ∧ g / 16 % 2 ≤ 1 ∧ splitV S' (g % 16) (g / 16 % 2) (g / 32) + 1 ≤ FW then
          match rec (rest2.drop (h - 2048)) (setf (setf S' (4 * (g % 16) + 2 * (g / 16 % 2)) (fld S' (4 * (g % 16) + 2 * (g / 16 % 2)))) (4 * (g % 16) + 2 * (g / 16 % 2) + 1) (splitV S' (g % 16) (g / 16 % 2) (g / 32))) with
          | none => none
          | some r1 => rec r1 (setf (setf S' (4 * (g % 16) + 2 * (g / 16 % 2)) (splitV S' (g % 16) (g / 16 % 2) (g / 32))) (4 * (g % 16) + 2 * (g / 16 % 2) + 1) (fld S' (4 * (g % 16) + 2 * (g / 16 % 2) + 1)))
        else none
  else
    match runList n ords (rest.take h) S with
    | .contra => some (rest.drop h)
    | _ => none

def checkS (lk : Nat → Bool) (n : Nat) (ords : List (Nat × Nat)) : Nat → List Nat → Nat → Option (List Nat)
  | 0, _, _ => none
  | _+1, [], _ => none
  | f+1, h :: rest, S => csBody lk n ords (fun st S' => checkS lk n ords f st S') h rest S

end CPQ

namespace CPQ

/-- leaf test for the 16 quarter-cell problem: every box lies within 1/200 of the grid point (k/4/3, k%4/3) and inside the unit square -/
def leafOK (S : Nat) : Bool :=
  (List.range 16).all fun k =>
    Nat.ble (k / 4 * M / 3) (fld S (4 * k) + M / 200) && Nat.ble (fld S (4 * k + 1)) (k / 4 * M / 3 + M / 200) &&
    Nat.ble (k % 4 * M / 3) (fld S (4 * k + 2) + M / 200) && Nat.ble (fld S (4 * k + 3)) (k % 4 * M / 3 + M / 200) &&
    Nat.ble (fld S (4 * k + 1)) M && Nat.ble (fld S (4 * k + 3)) M

end CPQ

namespace CPQ

theorem checkS_zero (lk : Nat → Bool) (n : Nat) (ords : List (Nat × Nat)) (st : List Nat) (S : Nat) : checkS lk n ords 0 st S = none := by
  cases st <;> rfl

theorem checkS_nil (lk : Nat → Bool) (n : Nat) (ords : List (Nat × Nat)) (f S : Nat) : checkS lk n ords (f + 1) [] S = none := rfl

theorem checkS_cons (lk : Nat → Bool) (n : Nat) (ords : List (Nat × Nat)) (f hd : Nat) (st : List Nat) (S : Nat) :
    checkS lk n ords (f + 1) (hd :: st) S = csBody lk n ords (fun st S' => checkS lk n ords f st S') hd st S := rfl

theorem runList_sound {n : Nat} {ords : List (Nat × Nat)} {pt : Nat → ℝ × ℝ} :
    ∀ (cs : List Nat) (S : Nat), Sat n ords S pt →
      (runList n ords cs S = .contra → False) ∧ (∀ S', runList n ords cs S = .ok S' → Sat n ords S' pt) := by
  intro cs
  induction cs with
  | nil =>
    intro S hs
    refine ⟨fun h => by simp [runList] at h, fun S' h => ?_⟩
    simp [runList] at h
    subst h; exact hs
  | cons c t ih =>
    intro S hs
    have key := runOne_sound hs c
    unfold runList
    rcases h : runOne n ords c S with _ | _ | S1
    · simp
    · exact ⟨fun _ => key.1 h, fun S' hb => by simp at hb⟩
    · have hs1 := key.2 S1 h
      have := ih S1 hs1
      simpa using this

theorem csBody_sound {n : Nat} {ords : List (Nat × Nat)} {pt : Nat → ℝ × ℝ} (lk : Nat → Bool)
    (hlk : ∀ S, lk S = true → Sat n ords S pt → False)
    (rec : List Nat → Nat → Option (List Nat))
    (hrec : ∀ st S rest, rec st S = some rest → Sat n ords S pt → False)
    (hd : Nat) (st : List Nat) (S : Nat) (rest : List Nat)
    (h : csBody lk n ords rec hd st S = some rest) (hs : Sat n ords S pt) : False := by
  unfold csBody at h
  by_cases h4 : hd = 4095
  · rw [if_pos h4] at h
    cases st with
    | nil => simp at h
    | cons m rest2 =>
      simp only at h
      have key := runList_sound (n := n) (ords := ords) (pt := pt) (rest2.take m) S hs
      rcases hr : runList n ords (rest2.take m) S with _ | _ | S1
      · exact key.1 hr
      · rw [hr] at h; simp at h
      · rw [hr] at h
        simp only at h
        have hs1 := key.2 S1 hr
        by_cases hl : lk S1 = true
        · exact hlk S1 hl hs1
        · rw [if_neg hl] at h; simp at h
  rw [if_neg h4] at h
  by_cases h2 : 2048 ≤ hd
  · rw [if_pos h2] at h
    cases st with
    | nil => simp at h
    | cons g rest2 =>
      simp only at h
      have key := runList_sound (n := n) (ords := ords) (pt := pt) (rest2.take (hd - 2048)) S hs
      rcases hr : runList n ords (rest2.take (hd - 2048)) S with _ | _ | S1
      · exact key.1 hr
      · rw [hr] at h; simp at h
      · rw [hr] at h
        simp only at h
        have hs1 := key.2 S1 hr
        by_cases hg : (g % 16 + 1 ≤ n ∧ g / 16 % 2 ≤ 1 ∧ splitV S1 (g % 16) (g / 16 % 2) (g / 32) + 1 ≤ FW)
        · rw [if_pos hg] at h
          obtain ⟨hp1, hax, hv1⟩ := hg
          have hp : g % 16 < n := by omega
          have hv : splitV S1 (g % 16) (g / 16 % 2) (g / 32) < FW := by omega
          have hM := M_pos
          have hP := hs1.1 (g % 16) hp
          obtain ⟨c1, c2⟩ := inS_ax hP (g / 16 % 2) hax
          rcases hA : rec (rest2.drop (hd - 2048)) (setf (setf S1 (4 * (g % 16) + 2 * (g / 16 % 2)) (fld S1 (4 * (g % 16) + 2 * (g / 16 % 2)))) (4 * (g % 16) + 2 * (g / 16 % 2) + 1) (splitV S1 (g % 16) (g / 16 % 2) (g / 32))) with _ | r1
          · rw [hA] at h; simp at h
          rw [hA] at h
          simp only at h
          rcases le_total (cx (g / 16 % 2) (pt (g % 16)) * M) ((splitV S1 (g % 16) (g / 16 % 2) (g / 32) : Nat) : ℝ) with hc | hc
          · exact hrec _ _ _ hA (sat_update' hs1 (g % 16) (g / 16 % 2) (fld S1 (4 * (g % 16) + 2 * (g / 16 % 2))) (splitV S1 (g % 16) (g / 16 % 2) (g / 32)) _ _ hax hp (fld_lt _ _) hv c1 hc rfl rfl)
          · exact hrec _ _ _ h (sat_update' hs1 (g % 16) (g / 16 % 2) (splitV S1 (g % 16) (g / 16 % 2) (g / 32)) (fld S1 (4 * (g % 16) + 2 * (g / 16 % 2) + 1)) _ _ hax hp hv (fld_lt _ _) hc c2 rfl rfl)
        · rw [if_neg hg] at h; simp at h
  · rw [if_neg h2] at h
    have key := runList_sound (n := n) (ords := ords) (pt := pt) (st.take hd) S hs
    rcases hr : runList n ords (st.take hd) S with _ | _ | S1
    · exact key.1 hr
    · rw [hr] at h; simp at h
    · rw [hr] at h; simp at h

theorem checkS_sound {n : Nat} {ords : List (Nat × Nat)} {pt : Nat → ℝ × ℝ} (lk : Nat → Bool)
    (hlk : ∀ S, lk S = true → Sat n ords S pt → False) :
    ∀ (f : Nat) (st : List Nat) (S : Nat) (rest : List Nat), checkS lk n ords f st S = some rest →
      Sat n ords S pt → False := by
  intro f
  induction f with
  | zero => intro st S rest h; rw [checkS_zero] at h; cases h
  | succ f ih =>
    intro st S rest h hs
    cases st with
    | nil => rw [checkS_nil] at h; cases h
    | cons hd st1 =>
      rw [checkS_cons] at h
      exact csBody_sound (pt := pt) lk hlk (fun st S' => checkS lk n ords f st S') (fun st S' r hr hs' => ih st S' r hr hs') hd st1 S rest h hs

end CPQ


