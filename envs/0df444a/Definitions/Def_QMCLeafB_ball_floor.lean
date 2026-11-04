-- Prove2me | Definitions.Def_QMCLeafB_ball_floor
-- name    : QMCLeafB_ball_floor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:05:02.280209+00:00
-- url     : https://prove2.me/theorems/bd10a536-7641-4e2e-99e4-f064e1dc0a6f
-- title:
--   QMCLeafB ball_floor
-- statement:
--   # leaf B phase 4 — brick `ball-floor`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# leaf B phase 4 — brick `ball-floor`

The audit's missing geometric seam between the separation oracle and the ellipsoid engine's
volume potential.  Two statements, both pure `ℝ`-analysis, neither depending on any runtime.

**1. A positive-margin body contains a Euclidean ball** (`ball_subset_relaxBody`).
The engine searches the *relaxed* threshold body at tolerance `δ > 0`,
```
relaxBody A t δ X  :=  (∀ x, -(δ/2)·∑x² ≤ xᵀXx) ∧ (∀ i, |Xᵢᵢ - 1| ≤ δ/4) ∧ (t - δ/2 ≤ ⟪A,X⟫),
```
a *superset* of the exact unit-diagonal PSD body `{X | X ⪰ 0, diag X = 1, tr (A X) ≥ t}`
(`body_subset_relaxBody`).  If a point `X₀` satisfies the ledger at *half* tolerance `δ/2` — the
content of `QMCLeafB.SepOracle.OkReport` at tolerance `δ/2` — then the whole Frobenius ball
```
‖X - X₀‖_F ≤ r,      r = δ / (8·(c_A + 1)),      c_A = ∑ᵢ ∑ⱼ |Aᵢⱼ|,
```
lies in the body at tolerance `δ` (`ball_subset_relaxBody`).  The three constraint families are
`1`-, `1`- and `c_A`-Lipschitz in the Frobenius metric (`abs_apply_le_of_frobNormSq_le`,
`abs_qfR_le_of_frobNormSq_le`, `abs_frob_le`), so `r` is explicit, **rational, and independent of
the dimension**.  The radius is delivered as the computable rational
`ballFloorRadius δ cA = δ / (8·(cA + 1))` (`cast_ballFloorRadius`).

**2. A contained ball floors the determinant** (`pow_two_mul_det_le_one_of_ball_subset_Ell`).
For the engine's ellipsoid `Ell A a = {x | (x - a)ᵀ A (x - a) ≤ 1}` with `A` positive definite,
```
Euclidean ball of radius r ⊆ Ell A a   ⟹   r ^ (2n) · det A ≤ 1.
```
Spectral proof: the ball hypothesis forces the Rayleigh bound `r²·xᵀAx ≤ xᵀx` for **every** `x`
(`sq_mul_qfR_le_of_ball`), so `r²·A ⪯ 1`; the eigenvalues of `r²·A` are its Rayleigh quotients at
unit eigenvectors (`eigenvalue_le_one`), hence lie in `[0,1]`, and `det` is their product
(`det_le_one_of_qf_le`).  No measure theory is needed, so the statement is available at every
dimension without a volume normalisation.

**3. What the engine does with it** (`pow_le_volPot`, `not_volPot_le_of_ball`, `no_run_of_ball`).
With `volPot A = (√det A)⁻¹` (`QMCLeafB.EngineIterates.volPot`) the floor reads `r ^ n ≤ volPot A`:
the stopping test `volPot A ≤ ε` cannot fire while a ball of radius `r` sits in the body, for
`ε < r ^ n`.  `no_run_of_ball` states the contradiction in the shape
`engine_run`/`engine_run_margin` deliver it (`body ⊆ Ell A_K a_K` plus `volPot A_K ≤ ε`), so the
answer producer's termination condition is a comparison of two *rational* quantities, `ε` and
`r ^ n`.

No `sorry`, no `axiom`; the axiom audit is at the end of the file.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.BallFloor

variable {n : ℕ}

/-! ## 1.  The quadratic form, the Frobenius pairing, and the Frobenius norm -/

/-- The real quadratic form `xᵀ M x` (`= QMCLeafB.EngineIterates.qfR`). -/
noncomputable def qfR (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

/-- The pairing `⟪C, X⟫ = ∑ᵢ ∑ⱼ Cᵢⱼ Xᵢⱼ` (`= QMCLeafB.SepOracle.frob` over `ℝ`). -/
noncomputable def frob (C X : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, C i j * X i j

/-- The squared Frobenius norm `‖X‖_F² = ∑ᵢ ∑ⱼ Xᵢⱼ²`. -/
noncomputable def frobNormSq (X : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, X i j ^ 2

/-- `∑ᵢ ∑ⱼ`-form of the quadratic form. -/
theorem qfR_eq_sum (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qfR M x = ∑ i, ∑ j, x i * M i j * x j := by
  rw [qfR, dot_mulVec_eq_sum_sum, Finset.sum_comm]

theorem qfR_add (M N : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qfR (M + N) x = qfR M x + qfR N x := by
  simp only [qfR, Matrix.add_mulVec, dotProduct_add]

theorem qfR_smul (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qfR (c • M) x = c * qfR M x := by
  rw [qfR, qfR, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem frob_add (C X Y : Matrix (Fin n) (Fin n) ℝ) :
    frob C (X + Y) = frob C X + frob C Y := by
  simp only [frob, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem frobNormSq_nonneg (X : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobNormSq X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `frobNormSq` as a sum over the product index, so that Cauchy–Schwarz applies to it. -/
theorem frobNormSq_eq_sum_prod (X : Matrix (Fin n) (Fin n) ℝ) :
    frobNormSq X = ∑ p : Fin n × Fin n, X p.1 p.2 ^ 2 := by
  rw [frobNormSq, ← Finset.sum_product']
  rfl

theorem sum_sq_mul_sq_eq (x : Fin n → ℝ) :
    ∑ p : Fin n × Fin n, (|x p.1| * |x p.2|) ^ 2 = (∑ i, x i ^ 2) ^ 2 := by
  have h : ∀ i j : Fin n, (|x i| * |x j|) ^ 2 = x i ^ 2 * x j ^ 2 := by
    intro i j
    rw [mul_pow, sq_abs, sq_abs]
  calc ∑ p : Fin n × Fin n, (|x p.1| * |x p.2|) ^ 2
      = ∑ p : Fin n × Fin n, x p.1 ^ 2 * x p.2 ^ 2 :=
        Finset.sum_congr rfl fun p _ => h p.1 p.2
    _ = ∑ i, ∑ j, x i ^ 2 * x j ^ 2 := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = (∑ i, x i ^ 2) * (∑ j, x j ^ 2) := (Finset.sum_mul_sum _ _ _ _).symm
    _ = (∑ i, x i ^ 2) ^ 2 := by ring

/-- The Frobenius ball of radius `r` around `X₀`. -/
def matBall (X₀ : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | frobNormSq (X - X₀) ≤ r ^ 2}

/-! ## 2.  Frobenius control of every functional in the ledger -/

/-- **Entrywise control.**  Inside the Frobenius ball of radius `r`, every entry is `r`-close. -/
theorem abs_apply_le_of_frobNormSq_le {E : Matrix (Fin n) (Fin n) ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : frobNormSq E ≤ r ^ 2) (i j : Fin n) : |E i j| ≤ r := by
  have hrow : (E i j) ^ 2 ≤ ∑ j', (E i j') ^ 2 :=
    Finset.single_le_sum (f := fun j' => (E i j') ^ 2) (fun j' _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hcol : ∑ j', (E i j') ^ 2 ≤ frobNormSq E :=
    Finset.single_le_sum (f := fun i' => ∑ j', (E i' j') ^ 2)
      (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : (E i j) ^ 2 ≤ r ^ 2 := le_trans (le_trans hrow hcol) h
  rw [sq_le_sq, abs_of_nonneg hr] at h2
  exact h2

/-- **Cauchy–Schwarz for the quadratic form of a perturbation.**  A perturbation with
`‖E‖_F ≤ r` moves every quadratic form by at most `r·∑x²`: `|xᵀE x| ≤ r·∑x²`.  This is the
dimension-free form of `QMCLeafB.CertPSD.abs_qf_le_of_entrywise_le`. -/
theorem abs_qfR_le_of_frobNormSq_le {E : Matrix (Fin n) (Fin n) ℝ} {x : Fin n → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (h : frobNormSq E ≤ r ^ 2) : |qfR E x| ≤ r * ∑ i, x i ^ 2 := by
  have hx2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hG : ∑ p : Fin n × Fin n, |E p.1 p.2| ^ 2 = frobNormSq E := by
    rw [frobNormSq_eq_sum_prod]
    exact Finset.sum_congr rfl fun p _ => sq_abs (E p.1 p.2)
  have hCS : (∑ p : Fin n × Fin n, (|x p.1| * |x p.2|) * |E p.1 p.2|) ^ 2
      ≤ (∑ p : Fin n × Fin n, (|x p.1| * |x p.2|) ^ 2)
        * (∑ p : Fin n × Fin n, |E p.1 p.2| ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [hG, sum_sq_mul_sq_eq x] at hCS
  have hsq : (∑ p : Fin n × Fin n, |x p.1| * |x p.2| * |E p.1 p.2|) ^ 2
      ≤ (r * ∑ i, x i ^ 2) ^ 2 := by
    calc (∑ p : Fin n × Fin n, |x p.1| * |x p.2| * |E p.1 p.2|) ^ 2
        ≤ ((∑ i, x i ^ 2) ^ 2) * frobNormSq E := hCS
      _ ≤ ((∑ i, x i ^ 2) ^ 2) * r ^ 2 := by
          exact mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = (r * ∑ i, x i ^ 2) ^ 2 := by ring
  rw [sq_le_sq, abs_of_nonneg (mul_nonneg hr hx2)] at hsq
  have hsum_nonneg : 0 ≤ ∑ p : Fin n × Fin n, |x p.1| * |x p.2| * |E p.1 p.2| :=
    Finset.sum_nonneg fun p _ => by positivity
  rw [abs_of_nonneg hsum_nonneg] at hsq
  refine le_trans ?_ hsq
  calc |qfR E x| = |∑ i, ∑ j, x i * E i j * x j| := by rw [qfR_eq_sum]
    _ = |∑ p : Fin n × Fin n, x p.1 * E p.1 p.2 * x p.2| := by
        rw [← Finset.sum_product']
        rfl
    _ ≤ ∑ p : Fin n × Fin n, |x p.1 * E p.1 p.2 * x p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p : Fin n × Fin n, |x p.1| * |x p.2| * |E p.1 p.2| := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [abs_mul, abs_mul]
        ring

/-- **The objective is `c_A`-Lipschitz**, `c_A = ∑ᵢ ∑ⱼ |Aᵢⱼ|`, in the Frobenius metric. -/
theorem abs_frob_le {A E : Matrix (Fin n) (Fin n) ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : frobNormSq E ≤ r ^ 2) : |frob A E| ≤ r * (∑ i, ∑ j, |A i j|) := by
  have h1 : |frob A E| ≤ ∑ i, ∑ j, |A i j| * r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_apply_le_of_frobNormSq_le hr h i j) (abs_nonneg _)
  have h2 : (∑ i, ∑ j, |A i j|) * r = ∑ i, ∑ j, |A i j| * r := by
    simp only [Finset.sum_mul]
  calc |frob A E| ≤ ∑ i, ∑ j, |A i j| * r := h1
    _ = r * (∑ i, ∑ j, |A i j|) := by rw [← h2, mul_comm]

/-! ## 3.  The positive-margin body contains a ball -/

/-- The unit-diagonal positive semidefinite body (`= ModernConvex.Relaxations.IsUnitDiagPSD`,
restated so this brick stands alone). -/
def UnitDiagPSD (X : Matrix (Fin n) (Fin n) ℝ) : Prop := X.PosSemidef ∧ ∀ i, X i i = 1

/-- **The relaxed threshold body at tolerance `δ`.**  Its three fields are exactly the three
fields of `QMCLeafB.SepOracle.OkReport`, transported to `ℝ`: the PSD margin `-δ/2·∑x²`, the
diagonal closeness `δ/4`, and the objective closeness `δ/2` to the threshold `t`.  Every
unit-diagonal PSD `X` with `tr (A X) ≥ t` is in it (`body_subset_relaxBody`). -/
def relaxBody (A : Matrix (Fin n) (Fin n) ℝ) (t δ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qfR X x) ∧
    (∀ i, |X i i - 1| ≤ δ / 4) ∧ (t - δ / 2 ≤ frob A X)

theorem body_subset_relaxBody {A : Matrix (Fin n) (Fin n) ℝ} {t δ : ℝ} (hδ : 0 ≤ δ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : UnitDiagPSD X) (htr : t ≤ frob A X) :
    relaxBody A t δ X := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have h0 : 0 ≤ qfR X x := by
      have h := hX.1.dotProduct_mulVec_nonneg x
      simpa [qfR, star_trivial] using h
    have h1 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  · intro i
    rw [hX.2 i]
    rw [show (1 : ℝ) - 1 = 0 by ring, abs_zero]
    linarith
  · linarith

/-- **The relaxed threshold body with an upper trace constraint.**  The engine's refutation targets
the body `{Z | Z ⪰ 0, diag Z = 1, ⟪A,Z⟫ ≤ u}` (an *upper* bound on the objective), which is the
direction `brick-answer-producer`'s `StrictBody` uses.  This is its relaxation: the same three
inequalities as `relaxBody`, with the objective relaxed *upwards* by `δ/2` instead of downwards. -/
def relaxBodyLE (A : Matrix (Fin n) (Fin n) ℝ) (u δ : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qfR X x) ∧
    (∀ i, |X i i - 1| ≤ δ / 4) ∧ (frob A X ≤ u + δ / 2)

theorem bodyLE_subset_relaxBodyLE {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ} (hδ : 0 ≤ δ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : UnitDiagPSD X) (htr : frob A X ≤ u) :
    relaxBodyLE A u δ X := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have h0 : 0 ≤ qfR X x := by
      have h := hX.1.dotProduct_mulVec_nonneg x
      simpa [qfR, star_trivial] using h
    have h1 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  · intro i
    rw [hX.2 i]
    rw [show (1 : ℝ) - 1 = 0 by ring, abs_zero]
    linarith
  · linarith

/-- The explicit rational ball radius of the floor: `δ / (8·(c_A + 1))`. -/
def ballFloorRadius (δ cA : ℚ) : ℚ := δ / (8 * (cA + 1))

theorem ballFloorRadius_pos {δ cA : ℚ} (hδ : 0 < δ) (hcA : 0 ≤ cA) :
    0 < ballFloorRadius δ cA := by
  have h : (0 : ℚ) < 8 * (cA + 1) := by linarith
  exact div_pos hδ h

theorem ballFloorRadius_nonneg {δ cA : ℚ} (hδ : 0 ≤ δ) (hcA : 0 ≤ cA) :
    0 ≤ ballFloorRadius δ cA := by
  have h : (0 : ℚ) ≤ 8 * (cA + 1) := by linarith
  exact div_nonneg hδ h

theorem cast_ballFloorRadius (δ cA : ℚ) :
    ((ballFloorRadius δ cA : ℚ) : ℝ) = (δ : ℝ) / (8 * ((cA : ℝ) + 1)) := by
  simp [ballFloorRadius]

/-- **The ball containment, in the form the iteration loop uses.**  If `X₀` satisfies the ledger
at half tolerance and `‖E‖_F ≤ r = δ/(8(c_A+1))` with `c_A ≥ ∑ᵢ∑ⱼ|Aᵢⱼ|`, then `X₀ + E` satisfies
the ledger at tolerance `δ`. -/
theorem ball_subset_relaxBody_aux {A : Matrix (Fin n) (Fin n) ℝ} {t δ cA : ℝ}
    (hδ : 0 < δ) (hcA : 0 ≤ cA) (hAsum : (∑ i, ∑ j, |A i j|) ≤ cA)
    {X₀ E : Matrix (Fin n) (Fin n) ℝ} (hE : frobNormSq E ≤ (δ / (8 * (cA + 1))) ^ 2)
    (h₀ : relaxBody A t (δ / 2) X₀) : relaxBody A t δ (X₀ + E) := by
  obtain ⟨hpsd, hdiag, htr⟩ := h₀
  set r : ℝ := δ / (8 * (cA + 1)) with hrdef
  have hden : (0 : ℝ) < 8 * (cA + 1) := by linarith
  have hr0 : 0 ≤ r := by rw [hrdef]; exact div_nonneg hδ.le (by linarith)
  have hrδ : r ≤ δ / 4 := by
    rw [hrdef, div_le_iff₀ hden]
    nlinarith
  have hrδ8 : r ≤ δ / 8 := by
    rw [hrdef, div_le_iff₀ hden]
    nlinarith
  have hrcA : r * cA ≤ δ / 4 := by
    rw [hrdef, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hx2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h2 : |qfR E x| ≤ r * ∑ i, x i ^ 2 := abs_qfR_le_of_frobNormSq_le hr0 hE
    have h2' : -(r * ∑ i, x i ^ 2) ≤ qfR E x := (abs_le.mp h2).1
    have h3 : -(δ / 2 / 2) * (∑ i, x i ^ 2) ≤ qfR X₀ x := hpsd x
    have hsig : r * (∑ i, x i ^ 2) ≤ (δ / 4) * ∑ i, x i ^ 2 :=
      mul_le_mul_of_nonneg_right hrδ hx2
    rw [qfR_add]
    nlinarith
  · intro i
    have hsum : (X₀ + E) i i - 1 = (X₀ i i - 1) + E i i := by
      rw [Matrix.add_apply]
      ring
    have h1 : |(X₀ + E) i i - 1| ≤ |X₀ i i - 1| + |E i i| := by
      rw [hsum]
      exact abs_add_le _ _
    have h2 : |E i i| ≤ r := abs_apply_le_of_frobNormSq_le hr0 hE i i
    have h3 : |X₀ i i - 1| ≤ δ / 2 / 4 := hdiag i
    linarith
  · have h1 : frob A (X₀ + E) = frob A X₀ + frob A E := frob_add A X₀ E
    have h2 : |frob A E| ≤ r * (∑ i, ∑ j, |A i j|) := abs_frob_le hr0 hE
    have h2' : -(r * (∑ i, ∑ j, |A i j|)) ≤ frob A E := (abs_le.mp h2).1
    have h3 : r * (∑ i, ∑ j, |A i j|) ≤ δ / 4 := by
      have h4 : r * (∑ i, ∑ j, |A i j|) ≤ r * cA :=
        mul_le_mul_of_nonneg_left hAsum hr0
      linarith
    rw [h1]
    linarith

/-- **The ball containment for the upper-trace body.**  Same radius, same proof: the only change
is the sign in the objective inequality. -/
theorem ball_subset_relaxBodyLE_aux {A : Matrix (Fin n) (Fin n) ℝ} {u δ cA : ℝ}
    (hδ : 0 < δ) (hcA : 0 ≤ cA) (hAsum : (∑ i, ∑ j, |A i j|) ≤ cA)
    {X₀ E : Matrix (Fin n) (Fin n) ℝ} (hE : frobNormSq E ≤ (δ / (8 * (cA + 1))) ^ 2)
    (h₀ : relaxBodyLE A u (δ / 2) X₀) : relaxBodyLE A u δ (X₀ + E) := by
  obtain ⟨hpsd, hdiag, htr⟩ := h₀
  set r : ℝ := δ / (8 * (cA + 1)) with hrdef
  have hden : (0 : ℝ) < 8 * (cA + 1) := by linarith
  have hr0 : 0 ≤ r := by rw [hrdef]; exact div_nonneg hδ.le (by linarith)
  have hrδ : r ≤ δ / 4 := by
    rw [hrdef, div_le_iff₀ hden]
    nlinarith
  have hrδ8 : r ≤ δ / 8 := by
    rw [hrdef, div_le_iff₀ hden]
    nlinarith
  have hrcA : r * cA ≤ δ / 4 := by
    rw [hrdef, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hx2 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h2 : |qfR E x| ≤ r * ∑ i, x i ^ 2 := abs_qfR_le_of_frobNormSq_le hr0 hE
    have h2' : -(r * ∑ i, x i ^ 2) ≤ qfR E x := (abs_le.mp h2).1
    have h3 : -(δ / 2 / 2) * (∑ i, x i ^ 2) ≤ qfR X₀ x := hpsd x
    have hsig : r * (∑ i, x i ^ 2) ≤ (δ / 4) * ∑ i, x i ^ 2 :=
      mul_le_mul_of_nonneg_right hrδ hx2
    rw [qfR_add]
    nlinarith
  · intro i
    have hsum : (X₀ + E) i i - 1 = (X₀ i i - 1) + E i i := by
      rw [Matrix.add_apply]
      ring
    have h1 : |(X₀ + E) i i - 1| ≤ |X₀ i i - 1| + |E i i| := by
      rw [hsum]
      exact abs_add_le _ _
    have h2 : |E i i| ≤ r := abs_apply_le_of_frobNormSq_le hr0 hE i i
    have h3 : |X₀ i i - 1| ≤ δ / 2 / 4 := hdiag i
    linarith
  · have h1 : frob A (X₀ + E) = frob A X₀ + frob A E := frob_add A X₀ E
    have h2 : |frob A E| ≤ r * (∑ i, ∑ j, |A i j|) := abs_frob_le hr0 hE
    have h3 : frob A E ≤ r * (∑ i, ∑ j, |A i j|) := (abs_le.mp h2).2
    have h4 : r * (∑ i, ∑ j, |A i j|) ≤ δ / 4 := by
      have h5 : r * (∑ i, ∑ j, |A i j|) ≤ r * cA := mul_le_mul_of_nonneg_left hAsum hr0
      linarith
    rw [h1]
    linarith

/-- **A positive-margin body contains a Euclidean ball (upper-trace form).** -/
theorem ball_subset_relaxBodyLE {A : Matrix (Fin n) (Fin n) ℝ} {u δ cA : ℝ}
    (hδ : 0 < δ) (hcA : 0 ≤ cA) (hAsum : (∑ i, ∑ j, |A i j|) ≤ cA)
    {X₀ : Matrix (Fin n) (Fin n) ℝ} (h₀ : relaxBodyLE A u (δ / 2) X₀) :
    matBall X₀ (δ / (8 * (cA + 1))) ⊆ relaxBodyLE A u δ := by
  intro X hX
  have hXE : X = X₀ + (X - X₀) := (add_sub_cancel X₀ X).symm
  rw [hXE]
  exact ball_subset_relaxBodyLE_aux hδ hcA hAsum hX h₀

/-- **A positive-margin body contains a Euclidean ball.**  The whole Frobenius ball of radius
`r = δ/(8(c_A+1))` around a half-tolerance point lies in the body at tolerance `δ`.  This is the
seam the audit named: it is what turns the engine's volume potential into a floor. -/
theorem ball_subset_relaxBody {A : Matrix (Fin n) (Fin n) ℝ} {t δ cA : ℝ}
    (hδ : 0 < δ) (hcA : 0 ≤ cA) (hAsum : (∑ i, ∑ j, |A i j|) ≤ cA)
    {X₀ : Matrix (Fin n) (Fin n) ℝ} (h₀ : relaxBody A t (δ / 2) X₀) :
    matBall X₀ (δ / (8 * (cA + 1))) ⊆ relaxBody A t δ := by
  intro X hX
  have hXE : X = X₀ + (X - X₀) := (add_sub_cancel X₀ X).symm
  rw [hXE]
  exact ball_subset_relaxBody_aux hδ hcA hAsum hX h₀


/-! ## 4.  A contained ball floors the determinant

The engine's ellipsoid is `Ell A a = {x | (x - a)ᵀ A (x - a) ≤ 1}` (`QMCLeafB.EngineIterates.Ell`,
repeated here so the brick stands alone).  The floor below says: if it contains a Euclidean ball of
radius `r > 0`, then `r ^ (2n) · det A ≤ 1`, i.e. `r ^ n ≤ (√det A)⁻¹ = volPot A`.

The route is spectral.  Containing the ball forces the Rayleigh bound `r² xᵀAx ≤ xᵀx` for every `x`
(`sq_mul_qfR_le_of_ball`), i.e. `r²·A ⪯ 1`; the eigenvalues of `r²·A` are the Rayleigh quotients
at unit eigenvectors, so each lies in `[0,1]` (`eigenvalue_le_one`), and `det` is their product
(`det_le_one_of_qf_le`).  Nothing is measured, so no volume normalisation enters.
-/

/-- The engine's ellipsoid `{x | (x - a)ᵀ A (x - a) ≤ 1}` (`= QMCLeafB.EngineIterates.Ell`). -/
def Ell (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | (x - a) ⬝ᵥ (A *ᵥ (x - a)) ≤ 1}

/-- The closed Euclidean ball of radius `r`, written with the dot product so that no norm instance
is involved (`= QMCLeafB.EllipsoidVolume.eucBall`). -/
def eucBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {z | ∑ i, z i ^ 2 ≤ r ^ 2}

/-- A translated Euclidean ball. -/
def eucBallAt (c : Fin n → ℝ) (r : ℝ) : Set (Fin n → ℝ) := (fun z => c + z) '' eucBall n r

theorem mem_eucBallAt_iff {c x : Fin n → ℝ} {r : ℝ} :
    x ∈ eucBallAt c r ↔ ∑ i, (x i - c i) ^ 2 ≤ r ^ 2 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [eucBall] using hz
  · intro hx
    exact ⟨x - c, by simpa [eucBall] using hx, by simp⟩

/-- Scaling a vector scales its quadratic form by the square. -/
theorem qfR_smul_vec (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qfR M (c • x) = c ^ 2 * qfR M x := by
  simp only [qfR, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Sum of squares of a scaled vector. -/
theorem sum_sq_smul (c : ℝ) (x : Fin n → ℝ) :
    ∑ i, (c • x) i ^ 2 = c ^ 2 * ∑ i, x i ^ 2 := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- **The averaged expansion.**  The cross terms of `qfR M (y + v)` and `qfR M (-y + v)` cancel
exactly, and no symmetry of `M` is needed for that: the sum of the two quadratic forms is
`2·(qfR M y + qfR M v)`.  This is the algebraic core of "a contained ball bounds the Rayleigh
quotient": the two points `y + v` and `-y + v` are both test points of the ball. -/
theorem qfR_add_vec_add_neg (M : Matrix (Fin n) (Fin n) ℝ) (y v : Fin n → ℝ) :
    qfR M (y + v) + qfR M (-y + v) = 2 * qfR M y + 2 * qfR M v := by
  have key : ∀ i j : Fin n,
      (y + v) i * M i j * (y + v) j + (-y + v) i * M i j * (-y + v) j
        = 2 * (y i * M i j * y j) + 2 * (v i * M i j * v j) := by
    intro i j
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  rw [qfR_eq_sum, qfR_eq_sum, qfR_eq_sum, qfR_eq_sum, ← Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => key i j

/-- **The Rayleigh bound forced by a contained ball.**  If the ellipsoid `Ell A a` contains the
Euclidean ball of radius `r` around `a₀`, then `r² · xᵀAx ≤ xᵀx` for every `x`: the matrix `r²·A`
is below the identity in the Loewner order. -/
theorem sq_mul_qfR_le_of_ball {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {a a₀ : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin n → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + a₀ - a) ⬝ᵥ (A *ᵥ (y + a₀ - a)) ≤ 1) :
    ∀ x : Fin n → ℝ, r ^ 2 * qfR A x ≤ ∑ i, x i ^ 2 := by
  have hsym : Aᵀ = A := by
    have h := hA.isHermitian.eq
    simpa using h
  set v : Fin n → ℝ := a₀ - a with hv
  have hAv : 0 ≤ qfR A v := by
    have h := hA.posSemidef.dotProduct_mulVec_nonneg v
    simpa [qfR, star_trivial] using h
  -- the `±y` average: `qfR A y + qfR A v ≤ 1`, hence `qfR A y ≤ 1`
  have hball' : ∀ z : Fin n → ℝ, (∑ i, z i ^ 2) ≤ r ^ 2 → qfR A (z + v) ≤ 1 := by
    intro z hz
    have h := hball z hz
    have hze : z + v = (z + a₀) - a := by rw [hv]; exact (add_sub_assoc z a₀ a).symm
    rw [hze]
    exact h
  have hstep : ∀ y : Fin n → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 → qfR A y ≤ 1 := by
    intro y hy
    have hy' : (∑ i, (-y) i ^ 2) ≤ r ^ 2 := by simpa using hy
    have h1 : qfR A (y + v) ≤ 1 := hball' y hy
    have h2 : qfR A (-y + v) ≤ 1 := hball' (-y) hy'
    have e := qfR_add_vec_add_neg A y v
    linarith
  intro x
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp [qfR]
  · have hs : 0 < ∑ i, x i ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
        by_contra h
        exact hx (funext (by simpa [not_exists] using h))
      refine Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, Finset.mem_univ i, ?_⟩
      rw [sq]
      exact mul_self_pos.mpr hi
    set c : ℝ := Real.sqrt (r ^ 2 / ∑ i, x i ^ 2) with hc
    have hc2 : c ^ 2 = r ^ 2 / ∑ i, x i ^ 2 := by
      rw [hc, Real.sq_sqrt (by positivity)]
    have hy : (∑ i, (c • x) i ^ 2) ≤ r ^ 2 := by
      rw [sum_sq_smul, hc2, div_mul_cancel₀]
      positivity
    have hb := hstep (c • x) hy
    rw [qfR_smul_vec, hc2] at hb
    rw [div_mul_eq_mul_div, div_le_iff₀ hs] at hb
    linarith

/-- The eigenvalue bound: if `M ⪯ 1` in the Rayleigh sense then every eigenvalue of `M` is at
most `1`.  The eigenvector is a unit vector, so `μᵢ = vᵢᵀ M vᵢ ≤ vᵢᵀ vᵢ = 1`. -/
theorem eigenvalue_le_one {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (h : ∀ x : Fin n → ℝ, qfR M x ≤ ∑ i, x i ^ 2) (i : Fin n) : hM.eigenvalues i ≤ 1 := by
  set v : Fin n → ℝ := fun j => (hM.eigenvectorBasis i : Fin n → ℝ) j with hv
  have hvv : v ⬝ᵥ v = 1 := by
    have h1 : ‖hM.eigenvectorBasis i‖ = 1 := hM.eigenvectorBasis.orthonormal.1 i
    have h2 : ∑ j, (hM.eigenvectorBasis i : Fin n → ℝ) j ^ 2 = 1 := by
      have h3 := EuclideanSpace.real_norm_sq_eq (hM.eigenvectorBasis i)
      rw [h1] at h3
      simpa using h3.symm
    simpa [dotProduct, sq] using h2
  have heq : qfR M v = hM.eigenvalues i := by
    rw [hM.eigenvalues_eq i]
    simp [qfR, hv]
  have hbound := h v
  rw [heq] at hbound
  have hsq : ∑ i, v i ^ 2 = 1 := by simpa [dotProduct, sq] using hvv
  rw [hsq] at hbound
  exact hbound

/-- **A determinant ceiling from a quadratic-form ceiling.**  If `M` is positive semidefinite and
`xᵀMx ≤ xᵀx` for every `x`, then `det M ≤ 1`.  `det` is the product of the eigenvalues
(`Matrix.IsHermitian.det_eq_prod_eigenvalues`), each of which lies in `[0,1]`. -/
theorem det_le_one_of_qf_le {M : Matrix (Fin n) (Fin n) ℝ} (hpsd : M.PosSemidef)
    (h : ∀ x : Fin n → ℝ, qfR M x ≤ ∑ i, x i ^ 2) : M.det ≤ 1 := by
  rw [hpsd.1.det_eq_prod_eigenvalues]
  calc ∏ i, (hpsd.1.eigenvalues i : ℝ) ≤ ∏ _i : Fin n, (1 : ℝ) :=
        Finset.prod_le_prod (fun i _ => hpsd.eigenvalues_nonneg i)
          (fun i _ => eigenvalue_le_one hpsd.1 h i)
    _ = 1 := by simp

/-- The determinant form of the floor: a quadratic-form ceiling `r²·A ⪯ 1` gives
`r ^ (2n) · det A ≤ 1`. -/
theorem pow_two_mul_det_le_one {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {r : ℝ}
    (hr : 0 < r) (hq : ∀ x : Fin n → ℝ, r ^ 2 * qfR A x ≤ ∑ i, x i ^ 2) :
    r ^ (2 * n) * A.det ≤ 1 := by
  have hpos : (0 : ℝ) < r ^ 2 := by positivity
  have hpsd : (r ^ 2 • A).PosSemidef := (Matrix.PosDef.smul hA hpos).posSemidef
  have hdet : (r ^ 2 • A).det ≤ 1 :=
    det_le_one_of_qf_le hpsd fun x => by rw [qfR_smul]; exact hq x
  rw [Matrix.det_smul, Fintype.card_fin, ← pow_mul] at hdet
  exact hdet

/-- **The ellipsoid volume floor.**  If the engine's ellipsoid `Ell A a` contains the Euclidean
ball of radius `r > 0` around `a₀`, then `r ^ (2n) · det A ≤ 1`.  This is the floor of the
determinant potential `log det A`, and it is what makes the shallow-cut loop stop. -/
theorem pow_two_mul_det_le_one_of_ball_subset_Ell {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {a a₀ : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin n → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + a₀ - a) ⬝ᵥ (A *ᵥ (y + a₀ - a)) ≤ 1) :
    r ^ (2 * n) * A.det ≤ 1 :=
  pow_two_mul_det_le_one hA hr (sq_mul_qfR_le_of_ball hA hr hball)

/-- The same floor in `Set` form, with the ball written as `eucBallAt a₀ r`. -/
theorem pow_two_mul_det_le_one_of_eucBallAt_subset_Ell {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {a a₀ : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : eucBallAt a₀ r ⊆ Ell A a) : r ^ (2 * n) * A.det ≤ 1 := by
  refine pow_two_mul_det_le_one_of_ball_subset_Ell (a := a) (a₀ := a₀) hA hr ?_
  intro y hy
  have hy' : y + a₀ ∈ eucBallAt a₀ r := by
    rw [mem_eucBallAt_iff]
    simpa using hy
  have := hsub hy'
  simpa [Ell, add_sub_cancel] using this

/-! ## 5.  The floor on the engine's volume potential

`QMCLeafB.EngineIterates.volPot A = (√det A)⁻¹ = vol (Ell A a) / vol (unit ball)`.  The floor
`r ^ (2n)·det A ≤ 1` reads `r ^ n ≤ volPot A`, so the stopping test `volPot A ≤ ε` cannot fire
while a ball of radius `r` sits in the body, as soon as `ε < r ^ n`.
-/

/-- The entrywise cast of a rational matrix (`= QMCLeafB.EngineIterates.castM`). -/
noncomputable def castM (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  M.map (fun q => (q : ℝ))

/-- The engine's volume potential (`= QMCLeafB.EngineIterates.volPot`). -/
noncomputable def volPot (A : Matrix (Fin n) (Fin n) ℚ) : ℝ :=
  (Real.sqrt (castM A).det)⁻¹

theorem volPot_eq {A : Matrix (Fin n) (Fin n) ℚ} : volPot A = (Real.sqrt (castM A).det)⁻¹ := rfl

/-- The elementary square-root arithmetic of the floor: `r ^ (2n)·D ≤ 1` with `D > 0` gives
`r ^ n ≤ (√D)⁻¹`. -/
theorem rpow_le_sqrt_inv (n : ℕ) {D r : ℝ} (hD : 0 < D) (hr : 0 < r)
    (h : r ^ (2 * n) * D ≤ 1) : r ^ n ≤ (Real.sqrt D)⁻¹ := by
  have hrn : (0 : ℝ) < r ^ n := by positivity
  have h2 : ((r ^ n) ^ 2) = r ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  have hle : D ≤ ((r ^ n)⁻¹) ^ 2 := by
    have h3 : ((r ^ n) ^ 2)⁻¹ = ((r ^ n)⁻¹) ^ 2 := (inv_pow _ _).symm
    calc D ≤ (r ^ (2 * n))⁻¹ := by
          rw [← one_div, le_div_iff₀ (by positivity : (0 : ℝ) < r ^ (2 * n)), mul_comm]
          exact h
      _ = ((r ^ n)⁻¹) ^ 2 := by rw [← h2, h3]
  have hsq : Real.sqrt D ≤ (r ^ n)⁻¹ := Real.sqrt_le_iff.mpr ⟨by positivity, hle⟩
  have h5 : ((r ^ n)⁻¹)⁻¹ ≤ (Real.sqrt D)⁻¹ :=
    (inv_le_inv₀ (by positivity : (0 : ℝ) < (r ^ n)⁻¹) (Real.sqrt_pos.2 hD)).mpr hsq
  rwa [inv_inv] at h5

/-- **The radius floor, real-matrix form.**  A Euclidean ball of radius `r` inside the ellipsoid
`Ell A a` forces `r ^ n ≤ (√det A)⁻¹`: the engine's volume potential is bounded below by the ball
radius to the dimension.  (This is the shape `brick-answer-producer`'s `Squeeze.floor` consumes,
with `n` instantiated at the flattened dimension `n * n`.) -/
theorem rpow_le_sqrt_inv_of_ball_subset_Ell {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {a a₀ : Fin n → ℝ} {r : ℝ} (hr : 0 < r) (hsub : eucBallAt a₀ r ⊆ Ell A a) :
    r ^ n ≤ (Real.sqrt A.det)⁻¹ :=
  rpow_le_sqrt_inv n hA.det_pos hr (pow_two_mul_det_le_one_of_eucBallAt_subset_Ell hA hr hsub)

/-- **The radius floor at the flattened dimension `n * n`.**  This is the form
`brick-answer-producer`'s `Squeeze` consumes: the engine runs on `Fin (n * n) → ℝ` (matrices
flattened), and a Euclidean ball of radius `r` in the covering ellipsoid forces `r ^ (n*n) ≤ Φ`.

Note the ball is the *Euclidean* (sum-of-squares) ball, not the product-norm ball of `ι → ℝ`:
the volume identity `vol (Ell K a) = vol (ball) · Φ` is the Euclidean one.  A product-norm ball
`{z | ‖z - u‖ ≤ r}` is the *larger* set, so a hypothesis `{‖z - u‖ ≤ r} ⊆ Ell K a` also gives the
floor at the same radius (it implies the Euclidean statement), and, when it is the conclusion of
the containment half, it is the *smaller* Euclidean ball one can supply. -/
theorem rpow_le_sqrt_inv_flat (n : ℕ) {K : Matrix (Fin (n * n)) (Fin (n * n)) ℝ} (hK : K.PosDef)
    {a a₀ : Fin (n * n) → ℝ} {r : ℝ} (hr : 0 < r)
    (hsub : ∀ z : Fin (n * n) → ℝ, (∑ k, (z k - a₀ k) ^ 2) ≤ r ^ 2 →
      (z - a) ⬝ᵥ (K *ᵥ (z - a)) ≤ 1) :
    r ^ (n * n) ≤ (Real.sqrt K.det)⁻¹ := by
  refine rpow_le_sqrt_inv_of_ball_subset_Ell (n := n * n) (a := a) (a₀ := a₀) hK hr ?_
  intro z hz
  rw [mem_eucBallAt_iff] at hz
  exact hsub z hz

/-- **The radius floor on the potential.**  A ball of radius `r` in every iterate keeps the
engine's volume potential above `r ^ n`. -/
theorem pow_le_volPot {A : Matrix (Fin n) (Fin n) ℚ} (hA : (castM A).PosDef)
    {a a₀ : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin n → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + a₀ - a) ⬝ᵥ (castM A *ᵥ (y + a₀ - a)) ≤ 1) :
    r ^ n ≤ volPot A := by
  have hfloor : r ^ (2 * n) * (castM A).det ≤ 1 :=
    pow_two_mul_det_le_one_of_ball_subset_Ell hA hr hball
  have hD : 0 < (castM A).det := hA.det_pos
  have hrn : (0 : ℝ) < r ^ n := by positivity
  have h2 : ((r ^ n) ^ 2) = r ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  have hle : (castM A).det ≤ ((r ^ n)⁻¹) ^ 2 := by
    have h3 : ((r ^ n) ^ 2)⁻¹ = ((r ^ n)⁻¹) ^ 2 := by rw [inv_pow]
    calc (castM A).det ≤ (r ^ (2 * n))⁻¹ := by
          rw [← one_div, le_div_iff₀ (by positivity : (0 : ℝ) < r ^ (2 * n)), mul_comm]
          exact hfloor
      _ = ((r ^ n)⁻¹) ^ 2 := by rw [← h2, h3]
  have hsq : Real.sqrt (castM A).det ≤ (r ^ n)⁻¹ :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hle⟩
  have h5 : ((r ^ n)⁻¹)⁻¹ ≤ (Real.sqrt (castM A).det)⁻¹ :=
    (inv_le_inv₀ (by positivity : (0 : ℝ) < (r ^ n)⁻¹) (Real.sqrt_pos.2 hD)).mpr hsq
  rw [inv_inv] at h5
  exact h5

/-- **The stopping test cannot fire.**  If a ball of radius `r` sits in the body, the engine's
stopping condition `volPot A ≤ ε` is false at every `ε < r ^ n`. -/
theorem not_volPot_le_of_ball {A : Matrix (Fin n) (Fin n) ℚ} (hA : (castM A).PosDef)
    {a a₀ : Fin n → ℝ} {r ε : ℝ} (hr : 0 < r)
    (hball : ∀ y : Fin n → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 →
      (y + a₀ - a) ⬝ᵥ (castM A *ᵥ (y + a₀ - a)) ≤ 1)
    (hε : ε < r ^ n) : ¬ volPot A ≤ ε := by
  intro hle
  have := pow_le_volPot hA hr hball
  linarith

/-- **The stopping test cannot fire — rational comparison.**  With the floor radius delivered as a
rational `rq` (`ballFloorRadius`), the hypothesis `ε < rq ^ n` is a comparison in `ℚ` alone. -/
theorem not_volPot_le_of_rat_ball {A : Matrix (Fin n) (Fin n) ℚ} (hA : (castM A).PosDef)
    {a a₀ : Fin n → ℝ} {rq : ℚ} (hrq : 0 < rq)
    (hball : ∀ y : Fin n → ℝ, (∑ i, y i ^ 2) ≤ ((rq : ℚ) : ℝ) ^ 2 →
      (y + a₀ - a) ⬝ᵥ (castM A *ᵥ (y + a₀ - a)) ≤ 1)
    {ε : ℚ} (hε : ε < rq ^ n) : ¬ volPot A ≤ ((ε : ℚ) : ℝ) := by
  have hr : (0 : ℝ) < ((rq : ℚ) : ℝ) := by exact_mod_cast hrq
  have hfloor : ((rq : ℚ) : ℝ) ^ n ≤ volPot A := pow_le_volPot hA hr hball
  have hcast : ((ε : ℚ) : ℝ) < ((rq ^ n : ℚ) : ℝ) := by exact_mod_cast hε
  have hpow : ((rq ^ n : ℚ) : ℝ) = ((rq : ℚ) : ℝ) ^ n := by push_cast; ring
  rw [hpow] at hcast
  linarith

/-- **`engine_run` cannot reach a potential below the floor while the body has a ball.**  This is
the contradiction form the answer producer consumes: the engine's two conclusions
(`body ⊆ Ell A_K a_K`) and (`volPot A_K ≤ ε`) are incompatible with a contained ball once
`ε < r ^ n`. -/
theorem no_run_of_ball {A : Matrix (Fin n) (Fin n) ℚ} (hA : (castM A).PosDef)
    {a a₀ : Fin n → ℝ} {r ε : ℝ} (hr : 0 < r)
    {body : (Fin n → ℝ) → Prop}
    (hball : ∀ y : Fin n → ℝ, (∑ i, y i ^ 2) ≤ r ^ 2 → body (y + a₀))
    (hsub : ∀ z, body z → Ell (castM A) a z) (hpot : volPot A ≤ ε) (hε : ε < r ^ n) :
    False := by
  refine not_volPot_le_of_ball (a := a) (a₀ := a₀) hA hr ?_ hε hpot
  intro y hy
  have h1 : (y + a₀) - a = y + a₀ - a := rfl
  rw [← h1]
  exact hsub _ (hball y hy)


/-! ## 6.  Non-vacuity and tightness of both halves

Both halves are exercised at `n = 1` with `A = 1`: the hypotheses of the containment are
satisfied by the identity matrix, and the floor is an equality (the unit ball *is* the ellipsoid
`Ell 1 0`, so `r ^ (2n)·det A = 1 = 1`). -/

/-- The half-tolerance ledger at `n = 1`, `A = 1`, `t = 1`, `δ = 1/4` is satisfied by `1`. -/
theorem relaxBody_one_half : relaxBody (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (1 / 2 / 2) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp only [qfR, Matrix.one_mulVec, dotProduct, Fin.sum_univ_one]
    nlinarith [sq_nonneg (x 0)]
  · intro i
    simp only [Matrix.one_apply_eq]
    norm_num
  · simp only [frob, Fin.sum_univ_one, Matrix.one_apply_eq, mul_one]
    norm_num

/-- **The containment, instantiated**: at `n = 1`, `A = 1`, `t = 1`, `δ = 1/2`, `c_A = 1`, the
Frobenius ball of radius `1/2 / 16` around `1` lies in the relaxed body. -/
theorem ball_subset_relaxBody_witness :
    matBall (1 : Matrix (Fin 1) (Fin 1) ℝ) ((1 / 2 : ℝ) / (8 * (1 + 1))) ⊆
      relaxBody (1 : Matrix (Fin 1) (Fin 1) ℝ) 1 (1 / 2) := by
  refine ball_subset_relaxBody (A := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (t := 1)
    (δ := 1 / 2) (cA := 1) (by norm_num) (by norm_num) ?_ relaxBody_one_half
  simp

/-- The unit ball of `Fin 1 → ℝ` *is* the ellipsoid `Ell 1 0`. -/
theorem unit_ball_subset_Ell_one :
    eucBallAt (0 : Fin 1 → ℝ) 1 ⊆ Ell (1 : Matrix (Fin 1) (Fin 1) ℝ) 0 := by
  intro z hz
  rw [mem_eucBallAt_iff] at hz
  have hz0 : z 0 ^ 2 ≤ 1 ^ 2 := by
    simpa only [Pi.zero_apply, sub_zero, Fin.sum_univ_one] using hz
  show ((z - 0) ⬝ᵥ ((1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (z - 0))) ≤ 1
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, Matrix.one_mulVec, dotProduct,
    Fin.sum_univ_one]
  nlinarith [hz0]

/-- **The floor is tight**: at `n = 1`, `A = 1`, `r = 1`, the floor reads `1 · 1 ≤ 1`. -/
theorem floor_tight :
    (1 : ℝ) ^ (2 * 1) * (1 : Matrix (Fin 1) (Fin 1) ℝ).det ≤ 1 :=
  pow_two_mul_det_le_one_of_eucBallAt_subset_Ell
    (A := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (a := 0) (a₀ := 0) Matrix.PosDef.one
    (by norm_num) unit_ball_subset_Ell_one

end QMCLeafB.BallFloor

/-! ## 6. Axiom audit -/

#print axioms QMCLeafB.BallFloor.ball_subset_relaxBody
#print axioms QMCLeafB.BallFloor.body_subset_relaxBody
#print axioms QMCLeafB.BallFloor.abs_qfR_le_of_frobNormSq_le
#print axioms QMCLeafB.BallFloor.abs_frob_le
#print axioms QMCLeafB.BallFloor.eigenvalue_le_one
#print axioms QMCLeafB.BallFloor.det_le_one_of_qf_le
#print axioms QMCLeafB.BallFloor.sq_mul_qfR_le_of_ball
#print axioms QMCLeafB.BallFloor.pow_two_mul_det_le_one_of_ball_subset_Ell
#print axioms QMCLeafB.BallFloor.pow_two_mul_det_le_one_of_eucBallAt_subset_Ell
#print axioms QMCLeafB.BallFloor.pow_le_volPot
#print axioms QMCLeafB.BallFloor.not_volPot_le_of_ball
#print axioms QMCLeafB.BallFloor.not_volPot_le_of_rat_ball
#print axioms QMCLeafB.BallFloor.no_run_of_ball
#print axioms QMCLeafB.BallFloor.qfR_add_vec_add_neg
#print axioms QMCLeafB.BallFloor.bodyLE_subset_relaxBodyLE
#print axioms QMCLeafB.BallFloor.ball_subset_relaxBodyLE
#print axioms QMCLeafB.BallFloor.rpow_le_sqrt_inv
#print axioms QMCLeafB.BallFloor.rpow_le_sqrt_inv_of_ball_subset_Ell
#print axioms QMCLeafB.BallFloor.rpow_le_sqrt_inv_flat
#print axioms QMCLeafB.BallFloor.ballFloorRadius_pos
#print axioms QMCLeafB.BallFloor.cast_ballFloorRadius
#print axioms QMCLeafB.BallFloor.ball_subset_relaxBody_witness
#print axioms QMCLeafB.BallFloor.floor_tight


