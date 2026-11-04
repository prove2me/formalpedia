-- Prove2me | Definitions.Def_QMCLeafB_RoundingOut
-- name    : QMCLeafB_RoundingOut
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:10:07.797237+00:00
-- url     : https://prove2.me/theorems/114b3ff3-206a-4da9-b3e9-32b342cab01e
-- title:
--   QMCLeafB RoundingOut
-- statement:
--   Prove2me QMC campaign — leaf B phase 2 — brick `brick-rounding-out` (member m7).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
Prove2me QMC campaign — leaf B phase 2 — brick `brick-rounding-out` (member m7).

# Rounding-out: from the central approximant to a certified rational pair

This file owns the *pure-mathematical* rounding-out step of the leaf-B engine: the transfer from
the central approximate point of the rational shallow-cut ellipsoid loop to a *display pair*
`(Xbar, ybar)` of exactly the shape that `QMCLeafB.IntegrationProbe.rat_sandwich` consumes:

* `Xbarᵀ = Xbar`, `∀ i, Xbar i i = 1`, `∀ x : Fin n → ℚ, 0 ≤ xᵀ Xbar x`;
* `(diagonal ybar + A)ᵀ = diagonal ybar + A`, `∀ x : Fin n → ℚ, 0 ≤ xᵀ (diagonal ybar + A) x`;
* `(∑ i, ybar i) + (A * Xbar).trace ≤ (∑ i, ∑ j, A i j) / 5000`.

Everything below is **exact rational arithmetic**: each step is an identity or a nonnegativity
statement over `ℚ`.  No eigenvalues, no spectral theory, no `Real.sqrt`, no limits.  The file
imports only `Mathlib`, and the quadratic form `qf` used throughout is *definitionally*
`QMCLeafB.CastBridge.qf` (both are `x ⬝ᵥ (M *ᵥ x)`), so every hypothesis slot below is literally
the corresponding `rat_sandwich` premise after unfolding.

## 1.  Diagonal fixing (`roundDiag`)

A rational point `X` with a nonnegative quadratic form and `|X i i - 1| ≤ ν` is replaced by an
*exactly* unit-diagonal rational matrix

  `Xbar = diagonal c * X * diagonal c + diagonal e`,   `c i = 2 / (1 + X i i)`,
  `e i = 1 - c i ^ 2 * X i i`.

The scaling is in closed form, chosen so that `c i ^ 2 * X i i ≤ 1` holds *always* over `ℚ`
(`(1+d)^2 - 4d = (1-d)^2 ≥ 0`): no square roots and no dyadic approximations are needed, and
`e ≥ 0` follows.  Then the key identity

  `xᵀ Xbar x = (c ∘ x)ᵀ X (c ∘ x) + ∑ i, e i * x i ^ 2`

writes the quadratic form of `Xbar` as a nonnegative combination of *the same form at a
rescaled vector* plus squares, so the rational PSD certificate of `X` transfers verbatim to
`Xbar` — the certification obligation of the engine never has to be recomputed from scratch.

The **cost** of the rounding is explicit and small:
`tr (A X) ≤ tr (A Xbar) + (1+ν)(2ν+ν²) ∑ᵢⱼ |Aᵢⱼ| + ν² ∑ᵢ |Aᵢᵢ|`.

A margin `δ` (`δ‖x‖² ≤ xᵀ X x`) is transported to `δ(1-ν)²`, which is what makes the rounded
pair robust against the entrywise rational perturbations whose budget `LeafB.ErrProp` tracks
(entrywise `ε` costs `ε·n` of margin).

## 2.  Cut-histogram dual aggregation (`dualAvg`)

The engine records, at every iteration `t`, a cut together with a dual candidate `y t` and a
budget `g t`.  The histogram average `ybar = ∑ t, w t • y t` (`w ≥ 0`, `∑ w = 1`) is again dual
feasible, and its objective `∑ i, ybar i` is the weighted average of the recorded ones.  Hence
the aggregated gap is at most `∑ t, w t * g t`: per-cut budgets **average, they do not add**.

## 3.  Assembly (`rounding_out`, `rounding_out_premises`, `DisplayPair`)

The two steps compose to a single existence statement whose conclusion has the exact shape of
`rat_sandwich`'s hypotheses; `DisplayPair A` is that premise triple as a structure (the output
contract the engine brick consumes) and `exists_displayPair` its existence form.
`budget_closes` records the arithmetic regime in which the accumulated budget stays under
`V/5000`: histogram part `≤ V/10000`, rounding part `≤ 3ν·V` with `ν ≤ 1/30000`, so the
diagonal tolerance the ellipsoid loop must maintain is `ν ≤ 1/30000`.  The worked instance
`instance_displayPair` (single edge, gap `0`) shows the hypotheses are simultaneously
satisfiable by kernel computation.

No `sorry`, no `axiom`, no `native_decide`.
-/


open scoped BigOperators
open Finset
open Matrix

namespace QMCLeafB.RoundingOut

variable {n : ℕ}

/-! ## 1.  The rational quadratic form and the rational PSD tests -/

/-- The rational quadratic form `x ⬝ᵥ (M *ᵥ x)` (`= QMCLeafB.CastBridge.qf`, definitionally). -/
def qf (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ := x ⬝ᵥ (M *ᵥ x)

/-- **The rational PSD test**: the exact shape in which the engine's PSD certificate
(`brick-certpsd`) delivers nonnegativity. -/
def RatPSD (M : Matrix (Fin n) (Fin n) ℚ) : Prop := ∀ x : Fin n → ℚ, 0 ≤ qf M x

/-- The same test with a positive margin `δ`: `M ⪰ δ • 1` on rational vectors.  This is the
shape in which the ellipsoid iteration maintains interiority. -/
def RatPSDm (M : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) : Prop :=
  ∀ x : Fin n → ℚ, δ * (x ⬝ᵥ x) ≤ qf M x

theorem qf_eq_sum (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf M x = ∑ i, ∑ j, x i * (M i j * x j) := by
  simp only [qf, dotProduct, mulVec, Finset.mul_sum]

theorem qf_add (A B : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (A + B) x = qf A x + qf B x := by
  simp only [qf, Matrix.add_mulVec, Pi.add_apply, dotProduct, mul_add, Finset.sum_add_distrib]

theorem qf_smul (c : ℚ) (A : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (c • A) x = c * qf A x := by
  simp only [qf, Matrix.smul_mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem symm_apply {M : Matrix (Fin n) (Fin n) ℚ} (h : Mᵀ = M) (i j : Fin n) :
    M j i = M i j := by
  have := congrFun (congrFun h i) j
  simpa [Matrix.transpose_apply] using this

/-- The quadratic form of a diagonal matrix. -/
theorem qf_diagonal (e x : Fin n → ℚ) :
    qf (diagonal e) x = ∑ i, e i * x i ^ 2 := by
  rw [qf_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne e (Ne.symm hj)])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp only [Matrix.diagonal_apply_eq, pow_two]
  ring

/-- A diagonal shift of the quadratic form. -/
theorem qf_diagonal_add (A : Matrix (Fin n) (Fin n) ℚ) (e x : Fin n → ℚ) :
    qf (A + diagonal e) x = qf A x + ∑ i, e i * x i ^ 2 := by
  rw [qf_add, qf_diagonal]

/-- **Diagonal conjugation is a reparametrisation of the quadratic form**: for a diagonal `c`,
`xᵀ (D X D) x = (c ∘ x)ᵀ X (c ∘ x)`.  This is the algebraic heart of diagonal fixing: no
spectral input is needed to move between the two. -/
theorem qf_diagonal_conj (c : Fin n → ℚ) (X : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (diagonal c * X * diagonal c) x = qf X (fun i => c i * x i) := by
  rw [qf_eq_sum, qf_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_diagonal, diagonal_mul]
  ring

/-! ## 2.  Entry bounds implied by the rational PSD test -/

theorem dotProduct_add_left (x y z : Fin n → ℚ) : (x + y) ⬝ᵥ z = x ⬝ᵥ z + y ⬝ᵥ z := by
  simp [dotProduct, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dotProduct_add_right (x y z : Fin n → ℚ) : x ⬝ᵥ (y + z) = x ⬝ᵥ y + x ⬝ᵥ z := by
  simp [dotProduct, Finset.sum_add_distrib, mul_add]

theorem dotProduct_sub_left (x y z : Fin n → ℚ) : (x - y) ⬝ᵥ z = x ⬝ᵥ z - y ⬝ᵥ z := by
  simp [dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem dotProduct_sub_right (x y z : Fin n → ℚ) : x ⬝ᵥ (y - z) = x ⬝ᵥ y - x ⬝ᵥ z := by
  simp [dotProduct, Finset.sum_sub_distrib, mul_sub]

theorem single_dotProduct (i : Fin n) (c : ℚ) (y : Fin n → ℚ) :
    (Pi.single i c) ⬝ᵥ y = c * y i := by
  simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq', ite_mul]

theorem dotProduct_self (x : Fin n → ℚ) : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
  simp [dotProduct, pow_two]

/-- The diagonal entry is nonnegative. -/
theorem diag_nonneg {X : Matrix (Fin n) (Fin n) ℚ} (hX : RatPSD X) (i : Fin n) : 0 ≤ X i i := by
  have h := hX (Pi.single i 1)
  rw [qf, Matrix.mulVec_single_one] at h
  simpa [Matrix.col_apply, single_dotProduct] using h

/-- The quadratic form at the test vector `eᵢ + eⱼ`. -/
theorem qf_single_add {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X) (i j : Fin n) :
    qf X (Pi.single i 1 + Pi.single j 1) = X i i + 2 * X i j + X j j := by
  have hsym : X j i = X i j := symm_apply hX i j
  rw [qf, Matrix.mulVec_add, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    dotProduct_add_left, dotProduct_add_right, dotProduct_add_right,
    single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  simp only [Matrix.col_apply, one_mul]
  rw [hsym]; ring

/-- The quadratic form at the test vector `eᵢ - eⱼ`. -/
theorem qf_single_sub {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X) (i j : Fin n) :
    qf X (Pi.single i 1 - Pi.single j 1) = X i i - 2 * X i j + X j j := by
  have hsym : X j i = X i j := symm_apply hX i j
  rw [qf, Matrix.mulVec_sub, Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    dotProduct_sub_left, dotProduct_sub_right, dotProduct_sub_right,
    single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct]
  simp only [Matrix.col_apply, one_mul]
  rw [hsym]; ring

/-- **The `2 × 2` minor bound over `ℚ`**, from the two sign tests alone: `2|Xᵢⱼ| ≤ Xᵢᵢ + Xⱼⱼ`.
This is the only entrywise information the engine needs about the central point, and it is
*derived*, not assumed (the analogue of `LeafB.ErrProp.sq_entry_le_diag_mul` over `ℚ`). -/
theorem two_mul_abs_entry_le_diag_add {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X)
    (hXp : RatPSD X) (i j : Fin n) : 2 * |X i j| ≤ X i i + X j j := by
  by_cases hij : i = j
  · subst hij
    have h1 : 0 ≤ X i i := diag_nonneg hXp i
    rw [abs_of_nonneg h1]; linarith
  · have hpos := hXp (Pi.single i 1 + Pi.single j 1)
    have hneg := hXp (Pi.single i 1 - Pi.single j 1)
    rw [qf_single_add hX i j] at hpos
    rw [qf_single_sub hX i j] at hneg
    have h2 : 2 * |X i j| = |2 * X i j| := by rw [abs_mul]; norm_num
    rw [h2, abs_le]
    constructor <;> linarith

/-- Entrywise bound: a unit-diagonal-with-tolerance PSD point has entries at most `1 + ν`. -/
theorem abs_entry_le {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X) (hXp : RatPSD X)
    {ν : ℚ} (hdiag : ∀ i, |X i i - 1| ≤ ν) (i j : Fin n) : |X i j| ≤ 1 + ν := by
  have h2 := two_mul_abs_entry_le_diag_add hX hXp i j
  have hi := (abs_le.mp (hdiag i)).2
  have hj := (abs_le.mp (hdiag j)).2
  linarith

/-! ## 3.  Diagonal fixing -/

/-- The closed-form rational diagonal scaling `2 / (1 + d)`. -/
def cDiag (d : ℚ) : ℚ := 2 / (1 + d)

theorem cDiag_pos {d : ℚ} (hd : 0 ≤ d) : 0 < cDiag d := by
  unfold cDiag
  apply div_pos (by norm_num); linarith

/-- The defining property: the scaled diagonal never exceeds `1`, so the compensating diagonal
entry `1 - c ^ 2 * d` is nonnegative.  No square root is involved. -/
theorem cDiag_sq_mul_le_one {d : ℚ} (hd : 0 ≤ d) : cDiag d ^ 2 * d ≤ 1 := by
  have h1 : (0:ℚ) < 1 + d := by linarith
  unfold cDiag
  rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)]
  nlinarith [sq_nonneg (d - 1)]

theorem cDiag_sub_one_abs_le {d ν : ℚ} (hd : 0 ≤ d) (h : |d - 1| ≤ ν) :
    |cDiag d - 1| ≤ ν := by
  have h1 : (0:ℚ) < 1 + d := by linarith
  have hν0 : 0 ≤ ν := le_trans (abs_nonneg _) h
  have key : cDiag d - 1 = (1 - d) / (1 + d) := by
    unfold cDiag; field_simp; ring
  rw [key, abs_div, abs_of_pos h1]
  rw [div_le_iff₀ h1]
  have h2 : |1 - d| ≤ ν := by rw [abs_sub_comm]; exact h
  have : ν * 1 ≤ ν * (1 + d) := by nlinarith
  linarith

theorem eDiag_nonneg (d : ℚ) (hd : 0 ≤ d) : 0 ≤ 1 - cDiag d ^ 2 * d := by
  linarith [cDiag_sq_mul_le_one hd]

/-- The compensating diagonal entry is at most `ν²`. -/
theorem eDiag_le_sq {d ν : ℚ} (hd : 0 ≤ d) (h : |d - 1| ≤ ν) :
    1 - cDiag d ^ 2 * d ≤ ν ^ 2 := by
  have h1 : (0:ℚ) < 1 + d := by linarith
  have hν0 : 0 ≤ ν := le_trans (abs_nonneg _) h
  have key : 1 - cDiag d ^ 2 * d = (1 - d) ^ 2 / (1 + d) ^ 2 := by
    unfold cDiag; field_simp; ring
  have h2 : (1 - d) ^ 2 ≤ ν ^ 2 := by
    have h' : |1 - d| ≤ ν := by rw [abs_sub_comm]; exact h
    have h3 := pow_le_pow_left₀ (abs_nonneg (1 - d)) h' 2
    rw [sq_abs] at h3
    exact h3
  have h3 : (0:ℚ) < (1 + d) ^ 2 := by positivity
  rw [key, div_le_iff₀ h3]
  have h4 : (1:ℚ) ≤ (1 + d) ^ 2 := by nlinarith
  nlinarith

/-- The scaling vector of diagonal fixing. -/
def sc (X : Matrix (Fin n) (Fin n) ℚ) : Fin n → ℚ := fun i => cDiag (X i i)

theorem sc_apply (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : sc X i = cDiag (X i i) := rfl

/-- **Diagonal fixing**: replace `X` by an exactly unit-diagonal matrix, by a diagonal
congruence plus the compensating diagonal shift. -/
def roundDiag (X : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  diagonal (sc X) * X * diagonal (sc X) + diagonal (fun i => 1 - sc X i ^ 2 * X i i)

/-- The scaling is positive. -/
theorem sc_pos {X : Matrix (Fin n) (Fin n) ℚ} (hd : ∀ i, 0 ≤ X i i) (i : Fin n) :
    0 < sc X i := cDiag_pos (hd i)

theorem sc_ge {X : Matrix (Fin n) (Fin n) ℚ} {ν : ℚ} (hd : ∀ i, 0 ≤ X i i)
    (hdiag : ∀ i, |X i i - 1| ≤ ν) (i : Fin n) : 1 - ν ≤ sc X i := by
  have h := cDiag_sub_one_abs_le (hd i) (hdiag i)
  have h' := (abs_le.mp h).1
  simp only [sc]
  linarith

theorem sc_le {X : Matrix (Fin n) (Fin n) ℚ} {ν : ℚ} (hd : ∀ i, 0 ≤ X i i)
    (hdiag : ∀ i, |X i i - 1| ≤ ν) (i : Fin n) : sc X i ≤ 1 + ν := by
  have h := cDiag_sub_one_abs_le (hd i) (hdiag i)
  have h' := (abs_le.mp h).2
  simp only [sc]
  linarith

/-- The scaling is `1 + O(ν)`: its products move every entry by at most `2ν + ν²`. -/
theorem sc_mul_abs_sub_one_le {X : Matrix (Fin n) (Fin n) ℚ} {ν : ℚ}
    (hd : ∀ i, 0 ≤ X i i) (hdiag : ∀ i, |X i i - 1| ≤ ν) (hν0 : 0 ≤ ν) (i j : Fin n) :
    |sc X i * sc X j - 1| ≤ 2 * ν + ν ^ 2 := by
  have h1 : |sc X i - 1| ≤ ν := cDiag_sub_one_abs_le (hd i) (hdiag i)
  have h2 : |sc X j - 1| ≤ ν := cDiag_sub_one_abs_le (hd j) (hdiag j)
  have hj : |sc X j| ≤ 1 + ν := by
    rw [abs_of_pos (sc_pos hd j)]; exact sc_le hd hdiag j
  have key : sc X i * sc X j - 1 = (sc X i - 1) * sc X j + (sc X j - 1) := by ring
  rw [key]
  calc |(sc X i - 1) * sc X j + (sc X j - 1)|
      ≤ |(sc X i - 1) * sc X j| + |sc X j - 1| := abs_add_le _ _
    _ ≤ ν * (1 + ν) + ν := by
        rw [abs_mul]
        have h4 : |sc X i - 1| * |sc X j| ≤ ν * (1 + ν) :=
          mul_le_mul h1 hj (abs_nonneg _) hν0
        linarith
    _ ≤ 2 * ν + ν ^ 2 := by nlinarith

theorem roundDiag_apply (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    roundDiag X i j = sc X i * X i j * sc X j
      + (if i = j then (1 - sc X i ^ 2 * X i i) else 0) := by
  simp only [roundDiag, Matrix.add_apply, mul_diagonal, diagonal_mul, diagonal_apply]

/-- **The diagonal is exactly `1`.** -/
theorem roundDiag_diag (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : roundDiag X i i = 1 := by
  rw [roundDiag_apply]; simp only [↓reduceIte]; ring

theorem roundDiag_symm {X : Matrix (Fin n) (Fin n) ℚ} (hX : Xᵀ = X) :
    (roundDiag X)ᵀ = roundDiag X := by
  ext i j
  have hsym : X j i = X i j := symm_apply hX i j
  rw [Matrix.transpose_apply, roundDiag_apply, roundDiag_apply, hsym]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]; ring

/-- **The quadratic form of the rounded matrix**, in the form that transfers the certificate:
the same form at the rescaled vector plus a nonnegative diagonal sum. -/
theorem qf_roundDiag (X : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf (roundDiag X) x
      = qf X (fun i => sc X i * x i) + ∑ i, (1 - sc X i ^ 2 * X i i) * x i ^ 2 := by
  rw [roundDiag, qf_diagonal_add, qf_diagonal_conj]

/-- **Diagonal fixing preserves the rational PSD test**: the engine's certificate for `X`
implies the certificate for the (exactly unit-diagonal) `Xbar`. -/
theorem roundDiag_ratPSD {X : Matrix (Fin n) (Fin n) ℚ} (hXp : RatPSD X) :
    RatPSD (roundDiag X) := by
  intro x
  rw [qf_roundDiag]
  have h1 : 0 ≤ qf X (fun i => sc X i * x i) := hXp _
  have h2 : 0 ≤ ∑ i, (1 - sc X i ^ 2 * X i i) * x i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (eDiag_nonneg _ (diag_nonneg hXp i)) (sq_nonneg _)
  linarith

/-- **A margin survives diagonal fixing**, losing only the factor `(1-ν)²`. -/
theorem roundDiag_ratPSDm {X : Matrix (Fin n) (Fin n) ℚ} {δ ν : ℚ}
    (hXm : RatPSDm X δ) (hδ0 : 0 ≤ δ) (hdiag : ∀ i, |X i i - 1| ≤ ν)
    (_hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    RatPSDm (roundDiag X) (δ * (1 - ν) ^ 2) := by
  have hd : ∀ i, 0 ≤ X i i := by
    intro i
    have h1 := hXm (Pi.single i (1:ℚ))
    rw [qf, Matrix.mulVec_single_one] at h1
    have h3 : (Pi.single i (1:ℚ)) ⬝ᵥ (X.col i) = X i i := by
      rw [single_dotProduct, Matrix.col_apply, one_mul]
    rw [h3] at h1
    have h2 : (0:ℚ) ≤ δ * (Pi.single i (1:ℚ) ⬝ᵥ Pi.single i (1:ℚ)) := by
      apply mul_nonneg hδ0
      rw [dotProduct_self]
      exact Finset.sum_nonneg fun k _ => sq_nonneg _
    linarith
  intro x
  rw [qf_roundDiag]
  have hstep : (1 - ν) ^ 2 * (x ⬝ᵥ x)
      ≤ (fun i => sc X i * x i) ⬝ᵥ (fun i => sc X i * x i) := by
    rw [dotProduct_self, dotProduct_self, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc : 1 - ν ≤ sc X i := sc_ge hd hdiag i
    have : (1 - ν) ^ 2 * x i ^ 2 ≤ (sc X i) ^ 2 * x i ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (by linarith) hc 2
    simpa [mul_pow, mul_assoc, mul_comm, mul_left_comm] using this
  have h1 : δ * ((1 - ν) ^ 2 * (x ⬝ᵥ x)) ≤ qf X (fun i => sc X i * x i) := by
    have h := hXm (fun i => sc X i * x i)
    nlinarith
  have h2 : 0 ≤ ∑ i, (1 - sc X i ^ 2 * X i i) * x i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (eDiag_nonneg _ (hd i)) (sq_nonneg _)
  have h3 : δ * (1 - ν) ^ 2 * (x ⬝ᵥ x) = δ * ((1 - ν) ^ 2 * (x ⬝ᵥ x)) := by ring
  rw [h3]; linarith



/-! ## 4.  Robustness: an entrywise rational perturbation costs `ε · n` of margin -/

/-- The quadratic form of an entrywise-bounded perturbation. -/
theorem abs_qf_le_of_entry_le {Δ : Matrix (Fin n) (Fin n) ℚ} {ε : ℚ}
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (hε : 0 ≤ ε) (x : Fin n → ℚ) :
    |qf Δ x| ≤ ε * (n : ℚ) * (x ⬝ᵥ x) := by
  have h1 : |qf Δ x| ≤ ∑ i, ∑ j, |x i| * (ε * |x j|) := by
    rw [qf_eq_sum]
    calc |∑ i, ∑ j, x i * (Δ i j * x j)|
        ≤ ∑ i, |∑ j, x i * (Δ i j * x j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i * (Δ i j * x j)| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i| * (ε * |x j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          simp only [abs_mul]
          have h1 : |Δ i j| * |x j| ≤ ε * |x j| :=
            mul_le_mul_of_nonneg_right (hΔ i j) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have h2 : (∑ i, ∑ j, |x i| * (ε * |x j|)) = ε * (∑ i, |x i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : (∑ i, |x i|) ^ 2 ≤ (n : ℚ) * ∑ i, |x i| ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |x i|)
    simpa using h
  have h4 : (∑ i, |x i| ^ 2) = x ⬝ᵥ x := by
    rw [dotProduct_self]
    exact Finset.sum_congr rfl fun i _ => by rw [sq_abs]
  rw [h4] at h3
  rw [h2] at h1
  have h6 : ε * (∑ i, |x i|) ^ 2 ≤ ε * (n : ℚ) * (x ⬝ᵥ x) := by
    have h7 := mul_le_mul_of_nonneg_left h3 hε
    calc ε * (∑ i, |x i|) ^ 2 ≤ ε * ((n : ℚ) * (x ⬝ᵥ x)) := h7
      _ = ε * (n : ℚ) * (x ⬝ᵥ x) := by ring
  linarith

/-- **A certifiable margin is what makes a rational rounding safe**: if `X` passes the rational
PSD test with margin `δ` and `X' = X + Δ` is entrywise within `ε`, then `X'` passes the plain
rational PSD test as soon as `ε·n ≤ δ`.  (Over `ℚ` this is the exact counterpart of
`LeafB.ErrProp.posSemidef_of_entry_near`.) -/
theorem ratPSD_add_of_entry_le {X Δ : Matrix (Fin n) (Fin n) ℚ} {δ ε : ℚ}
    (hX : RatPSDm X δ) (hΔ : ∀ i j, |Δ i j| ≤ ε) (hε : 0 ≤ ε) (hlt : ε * (n : ℚ) ≤ δ) :
    RatPSD (X + Δ) := by
  intro x
  rw [qf_add]
  have h1 := hX x
  have h2 := abs_qf_le_of_entry_le hΔ hε x
  have h3 : (0:ℚ) ≤ x ⬝ᵥ x := by
    rw [dotProduct_self]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have h4 : -(qf Δ x) ≤ ε * (n : ℚ) * (x ⬝ᵥ x) := by
    have := (abs_le.mp h2).1
    linarith
  have h5 : ε * (n : ℚ) * (x ⬝ᵥ x) ≤ δ * (x ⬝ᵥ x) := by
    apply mul_le_mul_of_nonneg_right hlt h3
  linarith

/-- **The composition the engine actually performs**: a central point with a *margin* `δ`,
diagonal tolerance `ν`, and an entrywise grid rounding `Δ` (size `ε`) — round the diagonal first,
then absorb the grid error.  The condition is `ε·n ≤ δ(1-ν)²`: the margin is transported by the
diagonal fixing and then spent on the rounding. -/
theorem roundDiag_add_ratPSD {X Δ : Matrix (Fin n) (Fin n) ℚ} {δ ν ε : ℚ}
    (hXm : RatPSDm X δ) (hδ0 : 0 ≤ δ) (hdiag : ∀ i, |X i i - 1| ≤ ν)
    (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) (hΔ : ∀ i j, |Δ i j| ≤ ε) (hε : 0 ≤ ε)
    (hεδ : ε * (n : ℚ) ≤ δ * (1 - ν) ^ 2) :
    RatPSD (roundDiag X + Δ) := by
  have hm : RatPSDm (roundDiag X) (δ * (1 - ν) ^ 2) :=
    roundDiag_ratPSDm hXm hδ0 hdiag hν0 hν1
  exact ratPSD_add_of_entry_le hm hΔ hε hεδ

/-! ## 5.  The objective cost of diagonal fixing -/

theorem trace_mul_eq_sum (A M : Matrix (Fin n) (Fin n) ℚ) :
    (A * M).trace = ∑ i, ∑ j, A i j * M j i := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trace_mul_diagonal (A : Matrix (Fin n) (Fin n) ℚ) (e : Fin n → ℚ) :
    (A * diagonal e).trace = ∑ i, A i i * e i := by
  simp [Matrix.trace, mul_diagonal]

theorem diagConj_apply (c : Fin n → ℚ) (X : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (diagonal c * X * diagonal c) i j = c i * X i j * c j := by
  rw [mul_diagonal, diagonal_mul]

/-- The trace of `A * roundDiag X`, split into the rescaled part and the diagonal repair. -/
theorem trace_mul_roundDiag (A X : Matrix (Fin n) (Fin n) ℚ) (hX : Xᵀ = X) :
    (A * roundDiag X).trace
      = (∑ i, ∑ j, A i j * (sc X i * X i j * sc X j))
        + ∑ i, A i i * (1 - sc X i ^ 2 * X i i) := by
  rw [roundDiag, Matrix.mul_add, Matrix.trace_add, trace_mul_diagonal, trace_mul_eq_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hsym : X j i = X i j := symm_apply hX i j
  rw [diagConj_apply, hsym]
  ring

/-- **The cost of diagonal fixing**: replacing `X` by the exactly unit-diagonal `roundDiag X`
lowers the objective `tr (A X)` by at most
`(1+ν)(2ν+ν²) ∑ᵢⱼ |Aᵢⱼ| + ν² ∑ᵢ |Aᵢᵢ|` — quadratic in the diagonal tolerance `ν`. -/
theorem trace_roundDiag_ge {A X : Matrix (Fin n) (Fin n) ℚ} {ν : ℚ}
    (hX : Xᵀ = X) (hXp : RatPSD X) (hdiag : ∀ i, |X i i - 1| ≤ ν) (hν0 : 0 ≤ ν) :
    (A * X).trace
      ≤ (A * roundDiag X).trace
        + ((1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |A i j|) + ν ^ 2 * (∑ i, |A i i|)) := by
  have hd : ∀ i, 0 ≤ X i i := diag_nonneg hXp
  have hXtr : (A * X).trace = ∑ i, ∑ j, A i j * X i j := by
    rw [trace_mul_eq_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [symm_apply hX i j]
  rw [hXtr, trace_mul_roundDiag A X hX]
  -- the rescaled part moves every term by at most `(1+ν)(2ν+ν²)`
  have hmain : (∑ i, ∑ j, A i j * X i j)
      - (∑ i, ∑ j, A i j * (sc X i * X i j * sc X j))
      ≤ (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |A i j|) := by
    rw [← Finset.sum_sub_distrib]
    have hstep : ∀ i : Fin n, (∑ j, A i j * X i j) - (∑ j, A i j * (sc X i * X i j * sc X j))
        ≤ ∑ j, |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := by
      intro i
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have hx : |X i j| ≤ 1 + ν := abs_entry_le hX hXp hdiag i j
      have hs : |sc X i * sc X j - 1| ≤ 2 * ν + ν ^ 2 := sc_mul_abs_sub_one_le hd hdiag hν0 i j
      have hkey : A i j * X i j - A i j * (sc X i * X i j * sc X j)
          = A i j * X i j * (1 - sc X i * sc X j) := by ring
      rw [hkey]
      calc A i j * X i j * (1 - sc X i * sc X j)
          ≤ |A i j * X i j * (1 - sc X i * sc X j)| := le_abs_self _
        _ = |A i j| * |X i j| * |1 - sc X i * sc X j| := by rw [abs_mul, abs_mul]
        _ ≤ |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := by
            have h1 : |A i j| * |X i j| ≤ |A i j| * (1 + ν) :=
              mul_le_mul_of_nonneg_left hx (abs_nonneg _)
            have h1 : |A i j| * |X i j| ≤ |A i j| * (1 + ν) :=
              mul_le_mul_of_nonneg_left hx (abs_nonneg _)
            have h2 : |1 - sc X i * sc X j| ≤ 2 * ν + ν ^ 2 := by
              rw [abs_sub_comm]; exact hs
            have h2' : (0:ℚ) ≤ 2 * ν + ν ^ 2 := by nlinarith
            have hb : (0:ℚ) ≤ |A i j| * (1 + ν) := by positivity
            calc |A i j| * |X i j| * |1 - sc X i * sc X j|
                ≤ (|A i j| * (1 + ν)) * (2 * ν + ν ^ 2) :=
                  mul_le_mul h1 h2 (abs_nonneg _) hb
              _ = |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := by ring
    calc (∑ i, ((∑ j, A i j * X i j) - (∑ j, A i j * (sc X i * X i j * sc X j))))
        ≤ ∑ i, ∑ j, |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := Finset.sum_le_sum fun i _ => hstep i
      _ = (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |A i j|) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
  have hdiagterm : -(∑ i, A i i * (1 - sc X i ^ 2 * X i i)) ≤ ν ^ 2 * (∑ i, |A i i|) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : 0 ≤ 1 - sc X i ^ 2 * X i i := eDiag_nonneg _ (hd i)
    have h2 : 1 - sc X i ^ 2 * X i i ≤ ν ^ 2 := eDiag_le_sq (hd i) (hdiag i)
    calc -(A i i * (1 - sc X i ^ 2 * X i i)) ≤ |A i i * (1 - sc X i ^ 2 * X i i)| := neg_le_abs _
      _ = |A i i| * (1 - sc X i ^ 2 * X i i) := by rw [abs_mul, abs_of_nonneg h1]
      _ ≤ |A i i| * ν ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = ν ^ 2 * |A i i| := by rw [mul_comm]
  linarith

/-- The other side of the rounding cost: the exactly unit-diagonal `roundDiag X` does not
*increase* the objective by more than the same `roundCost`.  (Together with
`trace_roundDiag_ge` this is the two-sided statement `|Δtr| ≤ roundCost`.) -/
theorem trace_roundDiag_le {A X : Matrix (Fin n) (Fin n) ℚ} {ν : ℚ}
    (hX : Xᵀ = X) (hXp : RatPSD X) (hdiag : ∀ i, |X i i - 1| ≤ ν) (hν0 : 0 ≤ ν) :
    (A * roundDiag X).trace
      ≤ (A * X).trace
        + ((1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |A i j|) + ν ^ 2 * (∑ i, |A i i|)) := by
  have hd : ∀ i, 0 ≤ X i i := diag_nonneg hXp
  have hXtr : (A * X).trace = ∑ i, ∑ j, A i j * X i j := by
    rw [trace_mul_eq_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [symm_apply hX i j]
  rw [hXtr, trace_mul_roundDiag A X hX]
  have hmain : (∑ i, ∑ j, A i j * (sc X i * X i j * sc X j)) - (∑ i, ∑ j, A i j * X i j)
      ≤ (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |A i j|) := by
    rw [← Finset.sum_sub_distrib]
    have hstep : ∀ i : Fin n,
        (∑ j, A i j * (sc X i * X i j * sc X j)) - (∑ j, A i j * X i j)
          ≤ ∑ j, |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := by
      intro i
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have hx : |X i j| ≤ 1 + ν := abs_entry_le hX hXp hdiag i j
      have hs : |sc X i * sc X j - 1| ≤ 2 * ν + ν ^ 2 := sc_mul_abs_sub_one_le hd hdiag hν0 i j
      have hkey : A i j * (sc X i * X i j * sc X j) - A i j * X i j
          = -(A i j * X i j * (1 - sc X i * sc X j)) := by ring
      rw [hkey]
      calc -(A i j * X i j * (1 - sc X i * sc X j))
          ≤ |A i j * X i j * (1 - sc X i * sc X j)| := neg_le_abs _
        _ = |A i j| * |X i j| * |1 - sc X i * sc X j| := by rw [abs_mul, abs_mul]
        _ ≤ |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := by
            have h1 : |A i j| * |X i j| ≤ |A i j| * (1 + ν) :=
              mul_le_mul_of_nonneg_left hx (abs_nonneg _)
            have h2 : |1 - sc X i * sc X j| ≤ 2 * ν + ν ^ 2 := by
              rw [abs_sub_comm]; exact hs
            have h2' : (0:ℚ) ≤ 2 * ν + ν ^ 2 := by nlinarith
            have hb : (0:ℚ) ≤ |A i j| * (1 + ν) := by positivity
            calc |A i j| * |X i j| * |1 - sc X i * sc X j|
                ≤ (|A i j| * (1 + ν)) * (2 * ν + ν ^ 2) :=
                  mul_le_mul h1 h2 (abs_nonneg _) hb
              _ = |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := by ring
    calc (∑ i, ((∑ j, A i j * (sc X i * X i j * sc X j)) - (∑ j, A i j * X i j)))
        ≤ ∑ i, ∑ j, |A i j| * ((1 + ν) * (2 * ν + ν ^ 2)) := Finset.sum_le_sum fun i _ => hstep i
      _ = (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |A i j|) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
  have hdiagterm : (∑ i, A i i * (1 - sc X i ^ 2 * X i i)) ≤ ν ^ 2 * (∑ i, |A i i|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : 0 ≤ 1 - sc X i ^ 2 * X i i := eDiag_nonneg _ (hd i)
    have h2 : 1 - sc X i ^ 2 * X i i ≤ ν ^ 2 := eDiag_le_sq (hd i) (hdiag i)
    calc A i i * (1 - sc X i ^ 2 * X i i) ≤ |A i i * (1 - sc X i ^ 2 * X i i)| := le_abs_self _
      _ = |A i i| * (1 - sc X i ^ 2 * X i i) := by rw [abs_mul, abs_of_nonneg h1]
      _ ≤ |A i i| * ν ^ 2 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = ν ^ 2 * |A i i| := by rw [mul_comm]
  linarith

/-! ## 6.  Cut-histogram dual aggregation -/

variable {T : ℕ}

/-- The histogram average of the recorded dual candidates: `ybar i = ∑ t, w t * y t i`. -/
def dualAvg (w : Fin T → ℚ) (y : Fin T → Fin n → ℚ) : Fin n → ℚ := fun i => ∑ t, w t * y t i

/-- A convex combination of dual-feasible slacks is dual feasible (symmetry part). -/
theorem dualAvg_symm {A : Matrix (Fin n) (Fin n) ℚ} (hAsym : Aᵀ = A) (w : Fin T → ℚ)
    (y : Fin T → Fin n → ℚ) :
    (diagonal (dualAvg w y) + A)ᵀ = diagonal (dualAvg w y) + A := by
  rw [Matrix.transpose_add, diagonal_transpose, hAsym]

/-- **The quadratic form of the aggregated slack is the histogram average of the recorded
ones.**  This is the whole content of "aggregate the cut histogram": the dual objective is
linear in the recorded candidates, so its *average* is what the histogram produces. -/
theorem qf_diagonal_dualAvg {A : Matrix (Fin n) (Fin n) ℚ} (w : Fin T → ℚ)
    (y : Fin T → Fin n → ℚ) (hw1 : ∑ t, w t = 1) (x : Fin n → ℚ) :
    qf (diagonal (dualAvg w y) + A) x
      = ∑ t, w t * qf (diagonal (y t) + A) x := by
  have hL : qf (diagonal (dualAvg w y) + A) x
      = qf A x + ∑ i, (dualAvg w y i) * x i ^ 2 := by
    rw [add_comm, qf_diagonal_add]
  have hR : ∀ t, qf (diagonal (y t) + A) x = qf A x + ∑ i, y t i * x i ^ 2 := by
    intro t; rw [add_comm, qf_diagonal_add]
  rw [hL]
  have hmix : (∑ i, (dualAvg w y i) * x i ^ 2) = ∑ t, w t * ∑ i, y t i * x i ^ 2 := by
    simp only [dualAvg, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hmix]
  have hexp : (∑ t, w t * qf (diagonal (y t) + A) x)
      = (∑ t, w t * qf A x) + ∑ t, w t * ∑ i, y t i * x i ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by rw [hR t]; ring
  rw [hexp, ← Finset.sum_mul, hw1, one_mul]

/-- **Dual feasibility is preserved by histogram aggregation.** -/
theorem dualAvg_test {A : Matrix (Fin n) (Fin n) ℚ} {w : Fin T → ℚ} {y : Fin T → Fin n → ℚ}
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (htest : ∀ t x, 0 ≤ qf (diagonal (y t) + A) x) :
    ∀ x, 0 ≤ qf (diagonal (dualAvg w y) + A) x := by
  intro x
  rw [qf_diagonal_dualAvg w y hw1 x]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (hw0 t) (htest t x)

/-- The dual objective of the aggregate is the weighted average of the recorded ones. -/
theorem dualAvg_sum (w : Fin T → ℚ) (y : Fin T → Fin n → ℚ) :
    (∑ i, dualAvg w y i) = ∑ t, w t * ∑ i, y t i := by
  simp only [dualAvg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]

/-! ## 7.  Assembly: the display pair -/

/-- The rounding cost of one pass of diagonal fixing. -/
def roundCost (A : Matrix (Fin n) (Fin n) ℚ) (ν : ℚ) : ℚ :=
  (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |A i j|) + ν ^ 2 * (∑ i, |A i i|)

/-- **Rounding-out.**  From a central rational point `X` (rational PSD test, diagonal within `ν`
of `1`), a histogram of recorded dual candidates `y t` with weights `w t`, and per-cut budgets
`g t` that hold at `X`, the engine can produce an *exactly* feasible rational display pair:
unit-diagonal `Xbar` with a working rational PSD test, and dual `ybar` whose slack is dual
feasible, with duality gap at most

  `∑ t, w t * g t + roundCost A ν`.

The per-cut budgets **average** (weighted by the histogram), and the rounding loses only
`roundCost A ν`. -/
theorem rounding_out {A X : Matrix (Fin n) (Fin n) ℚ} {w : Fin T → ℚ} {y : Fin T → Fin n → ℚ}
    {g : Fin T → ℚ} {ν : ℚ} (hν0 : 0 ≤ ν) (hAsym : Aᵀ = A) (hXsym : Xᵀ = X) (hXp : RatPSD X)
    (hdiag : ∀ i, |X i i - 1| ≤ ν) (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hypTest : ∀ t x, 0 ≤ qf (diagonal (y t) + A) x)
    (hbudget : ∀ t, (∑ i, y t i) + (A * X).trace ≤ g t) :
    ∃ (Xbar : Matrix (Fin n) (Fin n) ℚ) (ybar : Fin n → ℚ),
      Xbarᵀ = Xbar ∧ RatPSD Xbar ∧ (∀ i, Xbar i i = 1) ∧
        (diagonal ybar + A)ᵀ = diagonal ybar + A ∧ RatPSD (diagonal ybar + A) ∧
        (∑ i, ybar i) + (A * Xbar).trace ≤ (∑ t, w t * g t) + roundCost A ν := by
  refine ⟨roundDiag X, dualAvg w y, roundDiag_symm hXsym, roundDiag_ratPSD hXp,
    roundDiag_diag X, dualAvg_symm hAsym w y, dualAvg_test hw0 hw1 hypTest, ?_⟩
  have htr : (A * roundDiag X).trace ≤ (A * X).trace + roundCost A ν :=
    trace_roundDiag_le hXsym hXp hdiag hν0
  have hsum := dualAvg_sum w y
  rw [hsum]
  have htrw : (A * X).trace = ∑ t, w t * (A * X).trace := by
    rw [← Finset.sum_mul, hw1, one_mul]
  have h2 : (∑ t, w t * ∑ i, y t i) + (A * X).trace ≤ ∑ t, w t * g t := by
    rw [htrw, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun t _ => ?_
    have hb := mul_le_mul_of_nonneg_left (hbudget t) (hw0 t)
    calc w t * (∑ i, y t i) + w t * (A * X).trace
        = w t * ((∑ i, y t i) + (A * X).trace) := by ring
      _ ≤ w t * g t := hb
  linarith

/-- **The display pair, in the exact shape of the `rat_sandwich` hypotheses.**  If the
accumulated budget sits below `V/5000`, the engine returns `Xbar`, `ybar` satisfying precisely
the three premises of `QMCLeafB.IntegrationProbe.rat_sandwich` — unit-diagonal rational PSD
primal, rational PSD dual slack, rational gap bound. -/
theorem rounding_out_premises {A X : Matrix (Fin n) (Fin n) ℚ} {w : Fin T → ℚ}
    {y : Fin T → Fin n → ℚ} {g : Fin T → ℚ} {ν : ℚ} (hν0 : 0 ≤ ν) (hAsym : Aᵀ = A)
    (hXsym : Xᵀ = X) (hXp : RatPSD X) (hdiag : ∀ i, |X i i - 1| ≤ ν)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hypTest : ∀ t x, 0 ≤ qf (diagonal (y t) + A) x)
    (hbudget : ∀ t, (∑ i, y t i) + (A * X).trace ≤ g t)
    (hV : (∑ t, w t * g t) + roundCost A ν ≤ (∑ i, ∑ j, A i j) / 5000) :
    ∃ (Xbar : Matrix (Fin n) (Fin n) ℚ) (ybar : Fin n → ℚ),
      Xbarᵀ = Xbar ∧ (∀ x : Fin n → ℚ, 0 ≤ qf Xbar x) ∧ (∀ i, Xbar i i = 1) ∧
        (diagonal ybar + A)ᵀ = diagonal ybar + A ∧
        (∀ x : Fin n → ℚ, 0 ≤ qf (diagonal ybar + A) x) ∧
        (∑ i, ybar i) + (A * Xbar).trace ≤ (∑ i, ∑ j, A i j) / 5000 := by
  obtain ⟨Xbar, ybar, h1, h2, h3, h4, h5, h6⟩ :=
    rounding_out hν0 hAsym hXsym hXp hdiag hw0 hw1 hypTest hbudget
  exact ⟨Xbar, ybar, h1, h2, h3, h4, h5, le_trans h6 hV⟩

/-- The engine-side entry point: the same rounding-out from a *margin* certificate
(`RatPSDm X δ`, `0 ≤ δ`) instead of the plain rational test — this is the form in which
`brick-certpsd`'s margin check and `brick-ellipsoid-step`'s interiority are recorded. -/
theorem rounding_out_margin {A X : Matrix (Fin n) (Fin n) ℚ} {w : Fin T → ℚ}
    {y : Fin T → Fin n → ℚ} {g : Fin T → ℚ} {ν δ : ℚ} (hν0 : 0 ≤ ν) (hδ0 : 0 ≤ δ)
    (hAsym : Aᵀ = A) (hXsym : Xᵀ = X) (hXm : RatPSDm X δ) (hdiag : ∀ i, |X i i - 1| ≤ ν)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hypTest : ∀ t x, 0 ≤ qf (diagonal (y t) + A) x)
    (hbudget : ∀ t, (∑ i, y t i) + (A * X).trace ≤ g t) :
    ∃ (Xbar : Matrix (Fin n) (Fin n) ℚ) (ybar : Fin n → ℚ),
      Xbarᵀ = Xbar ∧ RatPSD Xbar ∧ (∀ i, Xbar i i = 1) ∧
        (diagonal ybar + A)ᵀ = diagonal ybar + A ∧ RatPSD (diagonal ybar + A) ∧
        (∑ i, ybar i) + (A * Xbar).trace ≤ (∑ t, w t * g t) + roundCost A ν := by
  have hXp : RatPSD X := by
    intro x
    have h := hXm x
    have hx : (0:ℚ) ≤ x ⬝ᵥ x := by
      rw [dotProduct_self]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith [mul_nonneg hδ0 hx]
  exact rounding_out hν0 hAsym hXsym hXp hdiag hw0 hw1 hypTest hbudget

/-! ## 8.  The typed interface handed to the engine brick -/

/-- **The premise triple of `QMCLeafB.IntegrationProbe.rat_sandwich`, typed.**

An engine brick that produces a `DisplayPair A` has discharged every analytic obligation of the
numerical endgame of leaf B: the remaining step is `rat_sandwich` itself, applied to the six
fields (which are, after unfolding `qf`, literally its six hypotheses). -/
structure DisplayPair (A : Matrix (Fin n) (Fin n) ℚ) where
  /-- the primal point -/
  X : Matrix (Fin n) (Fin n) ℚ
  /-- the dual point -/
  y : Fin n → ℚ
  /-- `X` is symmetric -/
  Xsym : Xᵀ = X
  /-- the rational PSD test for `X` (the `brick-certpsd` output shape) -/
  Xtest : ∀ x : Fin n → ℚ, 0 ≤ qf X x
  /-- `X` has unit diagonal -/
  Xdiag : ∀ i, X i i = 1
  /-- the dual slack is symmetric -/
  ysym : (diagonal y + A)ᵀ = diagonal y + A
  /-- the rational PSD test for the dual slack -/
  ytest : ∀ x : Fin n → ℚ, 0 ≤ qf (diagonal y + A) x
  /-- the rational duality gap bound of the campaign -/
  gap : (∑ i, y i) + (A * X).trace ≤ (∑ i, ∑ j, A i j) / 5000

/-- **The engine's output contract**: under the rounding-out hypotheses and the budget regime
`∑ w_t g_t + roundCost A ν ≤ V/5000`, a certified display pair exists. -/
theorem exists_displayPair {A X : Matrix (Fin n) (Fin n) ℚ} {w : Fin T → ℚ}
    {y : Fin T → Fin n → ℚ} {g : Fin T → ℚ} {ν : ℚ} (hν0 : 0 ≤ ν) (hAsym : Aᵀ = A)
    (hXsym : Xᵀ = X) (hXp : RatPSD X) (hdiag : ∀ i, |X i i - 1| ≤ ν)
    (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hypTest : ∀ t x, 0 ≤ qf (diagonal (y t) + A) x)
    (hbudget : ∀ t, (∑ i, y t i) + (A * X).trace ≤ g t)
    (hV : (∑ t, w t * g t) + roundCost A ν ≤ (∑ i, ∑ j, A i j) / 5000) :
    Nonempty (DisplayPair A) := by
  obtain ⟨Xbar, ybar, h1, h2, h3, h4, h5, h6⟩ :=
    rounding_out_premises hν0 hAsym hXsym hXp hdiag hw0 hw1 hypTest hbudget hV
  exact ⟨⟨Xbar, ybar, h1, h2, h3, h4, h5, h6⟩⟩

/-! ## 9.  Non-vacuity: rank-one Grams, and a worked display pair -/

/-- A rank-one rational Gram matrix `u uᵀ` passes every rational test (its quadratic form is
the square `(∑ i, u i * x i)²`).  This is the elementary non-vacuity witness for the certificate
notion: the hypothesis slots of the brick are simultaneously satisfiable by computation. -/
theorem ratPSD_vecMulVec (u : Fin n → ℚ) : RatPSD (vecMulVec u u) := by
  intro x
  rw [qf_eq_sum]
  have h : (∑ i, ∑ j, x i * (vecMulVec u u i j * x j)) = (∑ i, u i * x i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [vecMulVec, Matrix.of_apply]
    ring
  rw [h]; exact sq_nonneg _

/-- **A worked instance: the single edge.**  For `A = [[0,1],[1,0]]` (`V = 2`) the optimal
rank-one pair `X = [[1,-1],[-1,1]]`, `y = (1,1)` has duality gap `0`, and the brick's engine
contract produces a certified display pair from the (trivial) one-cut histogram with `ν = 0`. -/
theorem instance_displayPair :
    Nonempty (DisplayPair (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)) := by
  have hAsym : (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
      = (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hXsym : (!![(1:ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ)ᵀ
      = (!![(1:ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hXp : RatPSD (!![(1:ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by
    have h : (!![(1:ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) = vecMulVec ![1, -1] ![1, -1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec]
    rw [h]; exact ratPSD_vecMulVec _
  have hdiag : ∀ i, |(!![(1:ℚ), -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) i i - 1| ≤ 0 := by
    intro i; fin_cases i <;> simp
  have hSlack : (diagonal (![1, 1] : Fin 2 → ℚ)
      + (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)) = vecMulVec ![1, 1] ![1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [vecMulVec, diagonal]
  have hypTest : ∀ t : Fin 1, ∀ x : Fin 2 → ℚ,
      0 ≤ qf (diagonal (![1, 1] : Fin 2 → ℚ)
        + (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)) x := by
    intro t x
    rw [hSlack]; exact ratPSD_vecMulVec ![1, 1] x
  have hbudget : ∀ t : Fin 1, (∑ i, (![1, 1] : Fin 2 → ℚ) i)
      + ((!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![(1:ℚ), -1; -1, 1]).trace ≤ 0 := by
    intro t
    have h1 : (∑ i, (![1, 1] : Fin 2 → ℚ) i) = 2 := by norm_num [Fin.sum_univ_two]
    have h2 : ((!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ)
        * !![(1:ℚ), -1; -1, 1]).trace = -2 := by
      simp [Matrix.trace, Fin.sum_univ_two]
      norm_num
    rw [h1, h2]; norm_num
  have hV : (∑ t : Fin 1, (fun _ : Fin 1 => (1:ℚ)) t * (fun _ : Fin 1 => (0:ℚ)) t)
      + roundCost (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) 0
      ≤ (∑ i, ∑ j, (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) i j) / 5000 := by
    have hS : (∑ i, ∑ j, (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) i j) = 2 := by
      norm_num [Fin.sum_univ_two]
    have hcost : roundCost (!![(0:ℚ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) 0 = 0 := by
      simp [roundCost]
    rw [hcost, hS]
    norm_num [Fin.sum_univ_one]
  exact exists_displayPair (A := !![(0:ℚ), 1; 1, 0]) (X := !![(1:ℚ), -1; -1, 1])
    (w := fun _ => 1) (y := fun _ => ![1, 1]) (g := fun _ => 0) (ν := 0)
    (show (0:ℚ) ≤ 0 by norm_num) hAsym hXsym hXp hdiag (fun _ => zero_le_one)
    (by simp) hypTest hbudget hV

/-! ## 10.  The arithmetic regime: the accumulated budget stays under `V/5000` -/

/-- In the QMC regime the weights are **nonnegative with zero diagonal**, and the histogram
budget is `V/10000`, the rounding budget `3ν·V` with `ν ≤ 1/30000` — total `V/5000`.  This is
the `5000` of the IntegrationProbe premise, and it fixes the diagonal tolerance the engine has
to maintain: `ν ≤ 1/30000`. -/
theorem budget_closes {A : Matrix (Fin n) (Fin n) ℚ} {w : Fin T → ℚ} {g : Fin T → ℚ} {ν : ℚ}
    (hAnonneg : ∀ i j, 0 ≤ A i j) (hAz : ∀ i, A i i = 0) (hν0 : 0 ≤ ν) (hν : ν ≤ 1 / 30000)
    (hg : (∑ t, w t * g t) ≤ (∑ i, ∑ j, A i j) / 10000) :
    (∑ t, w t * g t) + roundCost A ν ≤ (∑ i, ∑ j, A i j) / 5000 := by
  have hS : (∑ i, ∑ j, |A i j|) = ∑ i, ∑ j, A i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact abs_of_nonneg (hAnonneg i j)
  have hS2 : (∑ i, |A i i|) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hAz i, abs_zero]
  have hV0 : (0:ℚ) ≤ ∑ i, ∑ j, A i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hAnonneg i j
  have hν1 : ν ≤ 1 := by linarith
  have hν2 : ν ^ 2 ≤ ν := by nlinarith
  have hν3 : ν ^ 3 ≤ ν := by nlinarith [sq_nonneg ν]
  have hcoef : (1 + ν) * (2 * ν + ν ^ 2) ≤ 3 * ν := by nlinarith
  have hstep : (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, A i j) ≤ 3 * ν * (∑ i, ∑ j, A i j) :=
    mul_le_mul_of_nonneg_right hcoef hV0
  have hstep2 : 3 * ν * (∑ i, ∑ j, A i j) ≤ (∑ i, ∑ j, A i j) / 10000 := by
    have h3ν : 3 * ν ≤ 1 / 10000 := by linarith
    calc 3 * ν * (∑ i, ∑ j, A i j) ≤ (1 / 10000) * (∑ i, ∑ j, A i j) :=
          mul_le_mul_of_nonneg_right h3ν hV0
      _ = (∑ i, ∑ j, A i j) / 10000 := by ring
  have hcost : roundCost A ν ≤ (∑ i, ∑ j, A i j) / 10000 := by
    rw [roundCost, hS, hS2, mul_zero, add_zero]
    exact le_trans hstep hstep2
  have hsum : (∑ i, ∑ j, A i j) / 10000 + (∑ i, ∑ j, A i j) / 10000
      = (∑ i, ∑ j, A i j) / 5000 := by ring
  linarith

end QMCLeafB.RoundingOut

#print axioms QMCLeafB.RoundingOut.roundDiag_ratPSD
#print axioms QMCLeafB.RoundingOut.trace_roundDiag_ge
#print axioms QMCLeafB.RoundingOut.dualAvg_test
#print axioms QMCLeafB.RoundingOut.rounding_out
#print axioms QMCLeafB.RoundingOut.rounding_out_premises
#print axioms QMCLeafB.RoundingOut.roundDiag_add_ratPSD
#print axioms QMCLeafB.RoundingOut.rounding_out_margin
#print axioms QMCLeafB.RoundingOut.instance_displayPair
#print axioms QMCLeafB.RoundingOut.exists_displayPair
#print axioms QMCLeafB.RoundingOut.budget_closes


