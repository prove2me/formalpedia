-- Prove2me | Definitions.Def_QMCLeafB_EngineIterates
-- name    : QMCLeafB_EngineIterates
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:00:11.169192+00:00
-- url     : https://prove2.me/theorems/772b3d76-f50b-48f1-a298-261034ea16b9
-- title:
--   QMCLeafB EngineIterates
-- statement:
--   # leaf B phase 3 — brick `engine-iterates`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
/-
# leaf B phase 3 — brick `engine-iterates`

The rational iterate loop's correctness core for the GLS shallow-cut engine of
`agm_classical_sdp_lower_value_tm2`.

## What the engine holds

Every iterate is a pair `(A, a)` over the space the SDP variable lives in, realized here at an
abstract dimension `n` (the caller instantiates `n` with the flattened matrix dimension).  `A` is
**exactly rational**: no square roots and no approximations enter the state, because the step is
parameterized by the *normalised cut depth* `rho ∈ ℚ` (the quantity the separation oracle reports
as `margin / sqrt sigma`) rather than by the absolute margin.  The cut normal `c` is accompanied by
a rational witness `p` of the linear relation `A p = c` (an exact rational solve, `MatQ`-style), and
`sigma = c ⬝ᵥ p` is then rational.  The **centre** is the one irrational quantity of the GLS step
(it moves by `gamma / sqrt sigma`); it is kept out of the state and lives in the theorem statements
as a real expression of the rational data, which is exactly where the containment invariant needs
it.  `brick-finalization` recovers a rational central point from it by the dyadic enclosure layer.

## What is proved

* `stepShape_posDef`, `stepShape_det`, `step_containment` — one shallow-cut step at rational
  normalised depth `rho ≥ 0` in the `A`-form of `QMCLeafB.EllipsoidStep`, stated with the
  witness `p` in place of `A⁻¹ c` (`scalar_core`, `quad_update_identity`).
* `containment_of_margin` and `margin_le_of_sq_check` — the oracle interface: the absolute margin
  `δ` of the recorded cut, and the engine's exact rational admissibility check `δ² ≤ ρ²σ`
  (no square root), are enough for the containment.
* `rStep_cast` — the step commutes with the cast `ℚ → ℝ`: the engine's exact rational update is
  *literally* the real step, so no approximation error enters the geometry.
* `Aat_posQ`, `Aat_cast_posDef` — positivity of every iterate (i): the rational form of `A_k` is
  symmetric with a strictly positive quadratic form.
* `body_containment` — the containment invariant propagates (ii-a): a body covered by the initial
  ellipsoid and cut by every recorded halfspace stays in every iterate's ellipsoid.
* `Aat_det`, `Aat_logdet_le`, `Aat_det_ge`, `Aat_vol_le`, `Aat_vol_below`,
  `Aat_vol_below_of_halving`, `engine_run`, `engine_run_margin` — the potential bookkeeping (ii-b):
  the determinant telescopes
  *exactly* over the run with the closed-form factor `rho0 rho`, the phase-2 rate
  `log det A_k ≤ log det A_0 + 2k/(n-1)` of `EllipsoidStep.logdet_stepMatrix` is recovered, and in
  the shallow regime the volume potential `1/sqrt(det A_k)` contracts, dropping below any target
  after an explicit number of iterations (`one_lt_rho0R_zero`: `rho n 0 > 1`, so central cuts
  always contract; `Aat_vol_below_central` is the inhabited special case).
* `histW`, `dualAvg`, `dualAvg_test`, `dualAvg_budget`, `histogram_record` — the extraction (iii):
  the recorded cut histogram, as uniform weights over the recorded dual candidates, aggregates to a
  *single* dual candidate which is dual feasible and whose budget is the weighted **average** of the
  recorded budgets.  These are exactly `QMCLeafB.RoundingOut.rounding_out`'s `hypTest` and `hbudget`
  slots at a one-candidate histogram `T = 1` (with `ybar = dualAvg (histW T) y` and
  `gbar = ∑ t, histW T t * g t`); `histogram_budget_le_max` bounds `gbar` by the largest recorded
  budget.

No `sorry`, no `axiom`.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.EngineIterates

variable {n : ℕ}

/-! ## 0.  Quadratic forms and the rational → real cast -/

/-- The rational quadratic form `xᵀ M x` (`= QMCLeafB.RoundingOut.qf = QMCLeafB.CastBridge.qf`,
definitionally). -/
def qf (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ := x ⬝ᵥ (M *ᵥ x)

/-- The real quadratic form. -/
noncomputable def qfR (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

/-- Entrywise cast of a rational matrix. -/
noncomputable def castM (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  M.map (fun q => (q : ℝ))

@[simp] theorem castM_apply (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    castM M i j = (M i j : ℝ) := rfl

theorem qf_eq_sum (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf M x = ∑ j, ∑ i, x i * M i j * x j := by
  rw [qf, dot_mulVec_eq_sum_sum]

theorem qfR_eq_sum (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qfR M x = ∑ j, ∑ i, x i * M i j * x j := by
  rw [qfR, dot_mulVec_eq_sum_sum]

/-- **The cast bridge for the quadratic form**: evaluating the cast matrix at the cast vector is
the cast of the rational value. -/
theorem qfR_cast (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qfR (castM M) (fun i => (x i : ℝ)) = ((qf M x : ℚ) : ℝ) := by
  rw [qfR_eq_sum, qf_eq_sum]
  simp only [castM_apply, Rat.cast_sum, Rat.cast_mul]

/-- Casting is injective on vectors. -/
theorem cast_fun_eq_zero {x : Fin n → ℚ} (h : (fun i => (x i : ℝ)) = 0) : x = 0 := by
  funext i
  simpa using congrFun h i

/-- **Reasoning point for the rational iterates**: symmetry plus a strictly positive quadratic form
on every nonzero rational vector.  This is the rational counterpart of `Matrix.PosDef`; the cast of
a positive definite real matrix satisfies it (`posQ_of_cast`), and it is what the engine checks. -/
def PosQ (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
  Aᵀ = A ∧ ∀ x : Fin n → ℚ, x ≠ 0 → 0 < qf A x

/-- A cast image of a positive definite real matrix is `PosQ`. -/
theorem posQ_of_cast {A : Matrix (Fin n) (Fin n) ℚ} (h : (castM A).PosDef) : PosQ A := by
  have hsymm : (castM A)ᵀ = castM A := by
    have hh := h.isHermitian.eq
    simpa using hh
  have hcast : castM (Aᵀ) = castM A := by
    rw [castM, Matrix.transpose_map, ← castM, hsymm]
  refine ⟨?_, ?_⟩
  · funext i j
    have := congrFun (congrFun hcast i) j
    simp only [castM_apply] at this
    exact Rat.cast_injective this
  · intro x hx
    by_contra hcon
    push Not at hcon
    have hxR : (fun i => (x i : ℝ)) ≠ 0 := fun hz => hx (cast_fun_eq_zero hz)
    have hpos : 0 < qfR (castM A) (fun i => (x i : ℝ)) := h.dotProduct_mulVec_pos hxR
    rw [qfR_cast] at hpos
    have : (0:ℚ) < qf A x := Rat.cast_pos.mp hpos
    linarith

theorem PosQ.symm {A : Matrix (Fin n) (Fin n) ℚ} (h : PosQ A) : Aᵀ = A := h.1

theorem PosQ.qform {A : Matrix (Fin n) (Fin n) ℚ} (h : PosQ A) {x : Fin n → ℚ} (hx : x ≠ 0) :
    0 < qf A x := h.2 x hx

/-! ## 1.  The shallow-cut step at rational normalised depth

Reference form: Grötschel–Lovász–Schrijver, *Geometric Algorithms and Combinatorial Optimization*
(1988), §3.2, in the `A`-form of `QMCLeafB.EllipsoidStep`: the ellipsoid `E(A,a)` carries the
quadratic form `A` itself, `E(A,a) = {x | (x-a)ᵀ A (x-a) ≤ 1}`, so its volume is `vol(ball)/√(det A)`.

The cut is the halfspace `{x | c ⬝ᵥ (x-a) ≥ -δ}`.  Write `σ = c ⬝ᵥ A⁻¹ c` and `r = √σ`; the
*normalised depth* is `δ/r ∈ [0,1]`.  The engine never computes `r` (it is irrational): it carries
the normalised depth `ρ` instead, and it carries a rational witness `p` of `A p = c`, so that
`σ = c ⬝ᵥ p` is rational.  The cut is then recorded at absolute margin `ρ * r`, and the step is

    A' = ((n²-1)/(n+ρ)²) • (A + ((2/(n-1))/σ) • c cᵀ),
    a' = a + ((1-ρ)/(n+1)/r) • p.

The whole point of the parameterization is that `ρ` (not `δ`) is what appears in `A'`: the shape
matrix update is an exact rational operation, and only the centre moves by the irrational `1/r`.
-/

/-- `β = 2/(n-1)` (the central-cut value, held fixed so the step is admissible at every depth). -/
noncomputable def betaR (n : ℕ) : ℝ := 2 / ((n : ℝ) - 1)

/-- `α = (n²-1)/(n+ρ)²`, the volume scaling of the step. -/
noncomputable def alphaR (n : ℕ) (ρ : ℝ) : ℝ := ((n : ℝ) ^ 2 - 1) / ((n : ℝ) + ρ) ^ 2

/-- `γ = (1-ρ)/(n+1)`. -/
noncomputable def gammaR (n : ℕ) (ρ : ℝ) : ℝ := (1 - ρ) / ((n : ℝ) + 1)

/-- `σ = c ⬝ᵥ p`, the squared cut norm in the `A`-metric when `A p = c`. -/
noncomputable def sigmaR (c p : Fin n → ℝ) : ℝ := c ⬝ᵥ p

/-- `r = √σ`. -/
noncomputable def sqrtSigmaR (c p : Fin n → ℝ) : ℝ := Real.sqrt (sigmaR c p)

/-- The ellipsoid `{x | (x-a)ᵀ A (x-a) ≤ 1}`. -/
noncomputable def Ell (A : Matrix (Fin n) (Fin n) ℝ) (a : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | (x - a) ⬝ᵥ (A *ᵥ (x - a)) ≤ 1}

/-- The updated shape matrix `A' = α • (A + (β/σ) • c cᵀ)`. -/
noncomputable def stepShape (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (c p : Fin n → ℝ) (ρ : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  alphaR n ρ • (A + (betaR n / sigmaR c p) • Matrix.vecMulVec c c)

/-- The updated centre `a' = a + (γ/r) • p`. -/
noncomputable def stepCentre (n : ℕ) (a : Fin n → ℝ) (c p : Fin n → ℝ) (ρ : ℝ) : Fin n → ℝ :=
  a + (gammaR n ρ / sqrtSigmaR c p) • p

/-! ### 1.1  Scalar data of the cut -/

theorem isUnit_det_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit

theorem mul_inv_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) : A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (isUnit_det_of_posDef hA)

theorem transpose_of_posDef {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) : Aᵀ = A := by
  have h := hA.isHermitian.eq
  simpa using h

theorem posDef_apply_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {v : Fin n → ℝ}
    (hv : v ≠ 0) : 0 < v ⬝ᵥ (A *ᵥ v) := by
  simpa using hA.dotProduct_mulVec_pos hv

theorem posDef_apply_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ (A *ᵥ v) := by
  rcases eq_or_ne v 0 with h | h
  · simp [h]
  · exact (posDef_apply_pos hA h).le

/-- The witness relation `A p = c` determines `p = A⁻¹ c` (so `σ = c ⬝ᵥ A⁻¹ c`). -/
theorem inv_mulVec_eq_of_mulVec_eq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hAp : A *ᵥ p = c) : A⁻¹ *ᵥ c = p := by
  rw [← hAp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hA),
    Matrix.one_mulVec]

/-- `σ > 0` for a nonzero cut normal. -/
theorem sigmaR_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c p : Fin n → ℝ}
    (hAp : A *ᵥ p = c) (hc : c ≠ 0) : 0 < sigmaR c p := by
  have hp : p ≠ 0 := by
    intro h
    exact hc (by rw [← hAp, h, Matrix.mulVec_zero])
  have h1 : 0 < p ⬝ᵥ (A *ᵥ p) := posDef_apply_pos hA hp
  rw [hAp, dotProduct_comm] at h1
  simpa [sigmaR] using h1

theorem sqrtSigmaR_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c p : Fin n → ℝ}
    (hAp : A *ᵥ p = c) (hc : c ≠ 0) : 0 < sqrtSigmaR c p :=
  Real.sqrt_pos.2 (sigmaR_pos hA hAp hc)

theorem sqrtSigmaR_mul_self {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c p : Fin n → ℝ}
    (hAp : A *ᵥ p = c) (hc : c ≠ 0) : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := by
  rw [sqrtSigmaR, ← pow_two]
  exact Real.sq_sqrt (sigmaR_pos hA hAp hc).le

/-- Cauchy–Schwarz in the `A`-inner product: `(c ⬝ᵥ u)² ≤ (c ⬝ᵥ A⁻¹c)(u ⬝ᵥ Au)`, in the form the
engine has it (with the witness `p` in place of `A⁻¹c`). -/
theorem cauchy_sigmaR {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c p : Fin n → ℝ}
    (hAp : A *ᵥ p = c) (hc : c ≠ 0) (u : Fin n → ℝ) :
    (c ⬝ᵥ u) ^ 2 ≤ sigmaR c p * (u ⬝ᵥ (A *ᵥ u)) := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hsym : Aᵀ = A := transpose_of_posDef hA
  have hpu : p ⬝ᵥ (A *ᵥ u) = c ⬝ᵥ u := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, hAp]
  have hup : u ⬝ᵥ (A *ᵥ p) = c ⬝ᵥ u := by
    rw [hAp, dotProduct_comm]
  have hpp : p ⬝ᵥ (A *ᵥ p) = sigmaR c p := by
    rw [hAp, sigmaR, dotProduct_comm]
  have hquad : ∀ t : ℝ, 0 ≤ u ⬝ᵥ (A *ᵥ u) + 2 * t * (c ⬝ᵥ u) + t ^ 2 * sigmaR c p := by
    intro t
    have h := posDef_apply_nonneg hA (u + t • p)
    have e : (u + t • p) ⬝ᵥ (A *ᵥ (u + t • p))
        = u ⬝ᵥ (A *ᵥ u) + 2 * t * (c ⬝ᵥ u) + t ^ 2 * sigmaR c p := by
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, hpu, hup, hpp, smul_eq_mul]
      ring
    rwa [e] at h
  have h := hquad (-(c ⬝ᵥ u) / sigmaR c p)
  have e2 : u ⬝ᵥ (A *ᵥ u) + 2 * (-(c ⬝ᵥ u) / sigmaR c p) * (c ⬝ᵥ u)
      + (-(c ⬝ᵥ u) / sigmaR c p) ^ 2 * sigmaR c p
      = u ⬝ᵥ (A *ᵥ u) - (c ⬝ᵥ u) ^ 2 / sigmaR c p := by
    field_simp; try ring
  rw [e2] at h
  have h2 : (c ⬝ᵥ u) ^ 2 / sigmaR c p * sigmaR c p = (c ⬝ᵥ u) ^ 2 := by field_simp
  have h3 : (c ⬝ᵥ u) ^ 2 / sigmaR c p ≤ u ⬝ᵥ (A *ᵥ u) := by linarith
  calc (c ⬝ᵥ u) ^ 2 = (c ⬝ᵥ u) ^ 2 / sigmaR c p * sigmaR c p := h2.symm
    _ ≤ (u ⬝ᵥ (A *ᵥ u)) * sigmaR c p := mul_le_mul_of_nonneg_right h3 hσ.le
    _ = sigmaR c p * (u ⬝ᵥ (A *ᵥ u)) := by ring

/-! ### 1.2  Parameter relations and the scalar core of containment -/

theorem natCast_two_le {n : ℕ} (hn : 2 ≤ n) : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn

theorem betaR_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ betaR n := by
  have h : (0:ℝ) < (n:ℝ) - 1 := by have := natCast_two_le hn; linarith
  rw [betaR]; positivity

theorem one_add_betaR {n : ℕ} (hn : 2 ≤ n) :
    (1:ℝ) + betaR n = ((n:ℝ) + 1) / ((n:ℝ) - 1) := by
  have h : ((n:ℝ) - 1) ≠ 0 := by have := natCast_two_le hn; intro h0; linarith
  rw [betaR]; field_simp; ring

theorem one_sub_gammaR {n : ℕ} (ρ : ℝ) : 1 - gammaR n ρ = ((n:ℝ) + ρ) / ((n:ℝ) + 1) := by
  rw [gammaR]; field_simp; ring

theorem gammaR_lt_one {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 ≤ ρ) : gammaR n ρ < 1 := by
  have h2 : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have hn2 := natCast_two_le hn
  rw [gammaR, div_lt_one h2]
  linarith

theorem gammaR_rel {n : ℕ} (hn : 2 ≤ n) (ρ : ℝ) :
    2 * gammaR n ρ * (1 + betaR n) = betaR n * (1 - ρ) := by
  have h : ((n:ℝ) - 1) ≠ 0 := by have := natCast_two_le hn; intro h0; linarith
  have h2 : ((n:ℝ) + 1) ≠ 0 := by positivity
  rw [gammaR, betaR]; field_simp; ring

theorem alphaR_eq {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    alphaR n ρ = 1 / ((1 - gammaR n ρ) ^ 2 * (1 + betaR n)) := by
  have h1 : ((n:ℝ) - 1) ≠ 0 := by have := natCast_two_le hn; intro h0; linarith
  have h2 : ((n:ℝ) + 1) ≠ 0 := by positivity
  have h3 : ((n:ℝ) + ρ) ≠ 0 := by
    have := natCast_two_le hn; intro h0; nlinarith
  rw [alphaR, one_sub_gammaR, one_add_betaR hn]
  field_simp
  ring

/-- **The scalar core of the containment.**  `(q,s)` are the squared `A`-norm and the normalised
height of a point of the initial ellipsoid in the cut direction; the factorisation exhibits the new
ellipsoid's value as `(q-1)` plus a term whose sign is `s ≤ 1` and `s ≥ -ρ`. -/
theorem scalar_core {β γ ρ s q : ℝ} (hβ : 0 ≤ β)
    (hγ : 2 * γ * (1 + β) = β * (1 - ρ))
    (hq : q ≤ 1) (hsq : s ^ 2 ≤ q) (hsδ : -ρ ≤ s) :
    q + β * s ^ 2 - 2 * γ * (1 + β) * s + γ ^ 2 * (1 + β) ≤ (1 - γ) ^ 2 * (1 + β) := by
  have hs1 : s ≤ 1 := by nlinarith [hsq, hq, sq_nonneg (s - 1)]
  have hfac : q + β * s ^ 2 - 2 * γ * (1 + β) * s + γ ^ 2 * (1 + β) - (1 - γ) ^ 2 * (1 + β)
      = (q - 1) + (s - 1) * (β * (s + ρ)) := by
    have h : β * (s + ρ) = β * (s + 1) - 2 * γ * (1 + β) := by linarith
    rw [h]; ring
  have hprod : (s - 1) * (β * (s + ρ)) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by nlinarith)
  linarith [hfac, hprod, hq]

theorem smul_vecMulVec_mulVec {c v : Fin n → ℝ} (s : ℝ) :
    (s • Matrix.vecMulVec c c) *ᵥ v = s • ((c ⬝ᵥ v) • c) := by
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp

/-- **The quadratic-form identity of the step**: the `A'`-norm of the shifted point, expanded. -/
theorem quad_update_identity
    {A : Matrix (Fin n) (Fin n) ℝ} (hAsym : Aᵀ = A) {c p u : Fin n → ℝ} (hAp : A *ᵥ p = c)
    {β γ α r : ℝ} (hr : r * r = sigmaR c p) (hr0 : r ≠ 0) :
    (u - (γ / r) • p) ⬝ᵥ ((α • (A + (β / sigmaR c p) • Matrix.vecMulVec c c)) *ᵥ (u - (γ / r) • p))
      = α * (u ⬝ᵥ (A *ᵥ u) + β * ((c ⬝ᵥ u) / r) ^ 2
          - 2 * γ * (1 + β) * ((c ⬝ᵥ u) / r) + γ ^ 2 * (1 + β)) := by
  have hpu : p ⬝ᵥ (A *ᵥ u) = c ⬝ᵥ u := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hAsym, hAp]
  have hσp : c ⬝ᵥ p = sigmaR c p := rfl
  have hcv : c ⬝ᵥ (u - (γ / r) • p) = c ⬝ᵥ u - (γ / r) * sigmaR c p := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sigmaR]
  have hAexp : (A + (β / sigmaR c p) • Matrix.vecMulVec c c) *ᵥ (u - (γ / r) • p)
      = A *ᵥ u - (γ / r) • c + (β / sigmaR c p) • ((c ⬝ᵥ u - (γ / r) * sigmaR c p) • c) := by
    rw [Matrix.add_mulVec, smul_vecMulVec_mulVec, Matrix.mulVec_sub, Matrix.mulVec_smul, hAp, hcv]
  have hUW : u ⬝ᵥ (A *ᵥ u - (γ / r) • c + (β / sigmaR c p) • ((c ⬝ᵥ u - (γ / r) * sigmaR c p) • c))
      = u ⬝ᵥ (A *ᵥ u) - (γ / r) * (c ⬝ᵥ u)
        + (β / sigmaR c p) * ((c ⬝ᵥ u - (γ / r) * sigmaR c p) * (c ⬝ᵥ u)) := by
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      dotProduct_comm u c]
  have hPW : p ⬝ᵥ (A *ᵥ u - (γ / r) • c + (β / sigmaR c p) • ((c ⬝ᵥ u - (γ / r) * sigmaR c p) • c))
      = c ⬝ᵥ u - (γ / r) * sigmaR c p
        + (β / sigmaR c p) * ((c ⬝ᵥ u - (γ / r) * sigmaR c p) * sigmaR c p) := by
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      hpu, hσp, dotProduct_comm p c]
  have hV : (u - (γ / r) • p) ⬝ᵥ (A *ᵥ u - (γ / r) • c
        + (β / sigmaR c p) • ((c ⬝ᵥ u - (γ / r) * sigmaR c p) • c))
      = u ⬝ᵥ (A *ᵥ u - (γ / r) • c + (β / sigmaR c p) • ((c ⬝ᵥ u - (γ / r) * sigmaR c p) • c))
        - (γ / r) * (p ⬝ᵥ (A *ᵥ u - (γ / r) • c
            + (β / sigmaR c p) • ((c ⬝ᵥ u - (γ / r) * sigmaR c p) • c))) := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hAexp, hV, hUW, hPW, ← hr]
  field_simp
  ring

/-! ### 1.3  Containment of the cut half-ellipsoid -/

/-- **Containment (general shape).**  `E(A,a) ∩ {x | c ⬝ᵥ (x-a) ≥ -δ} ⊆ E(A',a')` where `δ = ρ r`
is the recorded margin and the step is parametrised by the *normalised* depth `ρ`. -/
theorem containment_general {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {c p : Fin n → ℝ}
    (hc : c ≠ 0) (hAp : A *ᵥ p = c) (a : Fin n → ℝ) {ρ β γ : ℝ} (hβ : 0 ≤ β) (hγ1 : γ < 1)
    (hγ : 2 * γ * (1 + β) = β * (1 - ρ)) :
    Ell A a ∩ {x | -(ρ * sqrtSigmaR c p) ≤ c ⬝ᵥ (x - a)} ⊆
      Ell ((1 / ((1 - γ) ^ 2 * (1 + β))) • (A + (β / sigmaR c p) • Matrix.vecMulVec c c))
        (a + (γ / sqrtSigmaR c p) • p) := by
  rintro x ⟨hxE, hxc⟩
  simp only [Ell, Set.mem_ofPred_eq] at hxE hxc ⊢
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hr : 0 < sqrtSigmaR c p := sqrtSigmaR_pos hA hAp hc
  have hrr : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  have hα : (0:ℝ) < 1 / ((1 - γ) ^ 2 * (1 + β)) := by
    have h1 : (0:ℝ) < (1 - γ) ^ 2 := by nlinarith
    have h2 : (0:ℝ) < 1 + β := by linarith
    positivity
  have hx' : x - (a + (γ / sqrtSigmaR c p) • p) = (x - a) - (γ / sqrtSigmaR c p) • p := by abel
  simp only [hx']
  have hqe := quad_update_identity (A := A) (c := c) (p := p) (u := x - a)
    (β := β) (γ := γ) (α := 1 / ((1 - γ) ^ 2 * (1 + β))) (r := sqrtSigmaR c p)
    (transpose_of_posDef hA) hAp hrr (ne_of_gt hr)
  rw [hqe]
  have hsq : ((c ⬝ᵥ (x - a)) / sqrtSigmaR c p) ^ 2 ≤ (x - a) ⬝ᵥ (A *ᵥ (x - a)) := by
    have hcau := cauchy_sigmaR hA hAp hc (x - a)
    have hr2 : sqrtSigmaR c p ^ 2 = sigmaR c p := by rw [pow_two]; exact hrr
    rw [div_pow, hr2, div_le_iff₀ hσ]
    calc (c ⬝ᵥ (x - a)) ^ 2 ≤ sigmaR c p * ((x - a) ⬝ᵥ (A *ᵥ (x - a))) := hcau
      _ = (x - a) ⬝ᵥ (A *ᵥ (x - a)) * sigmaR c p := by ring
  have hsδ : -ρ ≤ (c ⬝ᵥ (x - a)) / sqrtSigmaR c p := by
    have h := div_le_div_of_nonneg_right
      (by linarith : -(ρ * sqrtSigmaR c p) ≤ c ⬝ᵥ (x - a)) hr.le
    have he : -(ρ * sqrtSigmaR c p) / sqrtSigmaR c p = -ρ := by
      rw [div_eq_iff (ne_of_gt hr)]
      ring
    rwa [he] at h
  have hcore := scalar_core hβ hγ hxE hsq hsδ
  calc 1 / ((1 - γ) ^ 2 * (1 + β)) * ((x - a) ⬝ᵥ (A *ᵥ (x - a))
        + β * ((c ⬝ᵥ (x - a)) / sqrtSigmaR c p) ^ 2
        - 2 * γ * (1 + β) * ((c ⬝ᵥ (x - a)) / sqrtSigmaR c p) + γ ^ 2 * (1 + β))
      ≤ 1 / ((1 - γ) ^ 2 * (1 + β)) * ((1 - γ) ^ 2 * (1 + β)) :=
        mul_le_mul_of_nonneg_left hcore hα.le
    _ = 1 := div_mul_cancel₀ 1 (ne_of_gt (mul_pos (by nlinarith : (0:ℝ) < (1 - γ) ^ 2)
        (by linarith : (0:ℝ) < 1 + β)))

/-- **Containment**: one shallow-cut step at normalised depth `ρ ≥ 0` contains the surviving
half-ellipsoid. -/
theorem step_containment {n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) (a : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Ell A a ∩ {x | -(ρ * sqrtSigmaR c p) ≤ c ⬝ᵥ (x - a)} ⊆
      Ell (stepShape n A c p ρ) (stepCentre n a c p ρ) := by
  rw [stepShape, stepCentre, alphaR_eq hn hρ, gammaR]
  exact containment_general hA hc hAp a (betaR_nonneg hn) (gammaR_lt_one hn hρ) (gammaR_rel hn ρ)

/-- **Containment from the oracle's absolute margin.**  If the recorded margin `δ` is at most the
step's normalised depth times the cut norm, the surviving half-ellipsoid is contained: this is the
form in which the separation oracle's output is consumed (the oracle knows `δ`; the engine knows
`ρ` and `σ`). -/
theorem containment_of_margin {n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) (a : Fin n → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {δ : ℝ} (hmargin : δ ≤ ρ * sqrtSigmaR c p) :
    Ell A a ∩ {x | -δ ≤ c ⬝ᵥ (x - a)} ⊆ Ell (stepShape n A c p ρ) (stepCentre n a c p ρ) := by
  refine subset_trans ?_ (step_containment hn hA hc hAp a hρ)
  intro x hx
  have h1 : -(ρ * sqrtSigmaR c p) ≤ -δ := by linarith [hmargin]
  exact ⟨hx.1, le_trans h1 hx.2⟩

/-- **The engine's exact admissibility check.**  Over `ℚ`, `δ² ≤ ρ²σ` (a rational comparison, no
square root) implies the real margin inequality `δ ≤ ρ√σ` that the containment consumes.  This is
how the normalised depth is produced: `ρ` is a rational upper bound of `δ/√σ` (dyadic enclosure of
`√σ`), and the check is exact. -/
theorem margin_le_of_sq_check {δ ρ σ : ℚ} (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (h : δ ^ 2 ≤ ρ ^ 2 * σ) :
    (δ : ℝ) ≤ (ρ : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) := by
  have hcast : ((δ : ℚ) : ℝ) ^ 2 ≤ ((ρ : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
    exact_mod_cast h
  have hσR : (0:ℝ) ≤ ((σ : ℚ) : ℝ) := by exact_mod_cast hσ
  have hsq : (((ρ : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2
      = ((ρ : ℚ) : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hσR]
  have h1 : ((δ : ℚ) : ℝ) ^ 2 ≤ (((ρ : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2 := by
    rw [hsq]; exact hcast
  have hρR : (0:ℝ) ≤ ((ρ : ℚ) : ℝ) := by exact_mod_cast hρ
  have hδR : (0:ℝ) ≤ ((δ : ℚ) : ℝ) := by exact_mod_cast hδ
  calc ((δ : ℚ) : ℝ) = Real.sqrt (((δ : ℚ) : ℝ) ^ 2) := (Real.sqrt_sq hδR).symm
    _ ≤ Real.sqrt ((((ρ : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ((ρ : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) :=
        Real.sqrt_sq (mul_nonneg hρR (Real.sqrt_nonneg _))

/-! ### 1.4  The step keeps the shape matrix positive definite -/

theorem stepShape_isSymm {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ = A) {c p : Fin n → ℝ}
    (ρ : ℝ) : (stepShape n A c p ρ)ᵀ = stepShape n A c p ρ := by
  rw [stepShape, Matrix.transpose_smul, Matrix.transpose_add, hA, Matrix.transpose_smul,
    Matrix.transpose_vecMulVec]

theorem stepShape_qform_pos {n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {ρ : ℝ} (hρ : 0 ≤ ρ) {x : Fin n → ℝ}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ ((stepShape n A c p ρ) *ᵥ x) := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hn2 := natCast_two_le hn
  have hα : 0 < alphaR n ρ := by
    rw [alphaR]
    exact div_pos (by nlinarith) (by positivity)
  have hβ0 : 0 ≤ betaR n / sigmaR c p := div_nonneg (betaR_nonneg hn) hσ.le
  have hAq : 0 < x ⬝ᵥ (A *ᵥ x) := posDef_apply_pos hA hx
  have hexp : x ⬝ᵥ ((A + (betaR n / sigmaR c p) • Matrix.vecMulVec c c) *ᵥ x)
      = x ⬝ᵥ (A *ᵥ x) + (betaR n / sigmaR c p) * (c ⬝ᵥ x) ^ 2 := by
    simp only [Matrix.add_mulVec, smul_vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul, dotProduct_comm x c]
    ring
  rw [stepShape, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hexp]
  have hb : 0 ≤ (betaR n / sigmaR c p) * (c ⬝ᵥ x) ^ 2 := mul_nonneg hβ0 (sq_nonneg _)
  nlinarith

/-- The shallow-cut step keeps `A` positive definite, so the loop can iterate. -/
theorem stepShape_posDef {n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (stepShape n A c p ρ).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · rw [Matrix.isHermitian_iff_isSymm]
    exact stepShape_isSymm (transpose_of_posDef hA) ρ
  · intro x hx
    simpa using stepShape_qform_pos hn hA hc hAp hρ hx

/-! ### 1.5  The determinant of the step and the potential factor -/

/-- The matrix determinant lemma for a rank-one update: `det (A + λ c cᵀ) = det A (1 + λ cᵀA⁻¹c)`. -/
theorem det_add_smul_vecMulVec {A : Matrix (Fin n) (Fin n) ℝ} (hAA : A * A⁻¹ = 1)
    (c : Fin n → ℝ) (lam : ℝ) :
    (A + lam • Matrix.vecMulVec c c).det = A.det * (1 + lam * (c ⬝ᵥ (A⁻¹ *ᵥ c))) := by
  have hv : Matrix.vecMulVec (lam • (A⁻¹ *ᵥ c)) c
      = Matrix.replicateCol Unit (lam • (A⁻¹ *ᵥ c)) * Matrix.replicateRow Unit c := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.replicateCol, Matrix.replicateRow]
  have hfac : A + lam • Matrix.vecMulVec c c
      = A * (1 + Matrix.vecMulVec (lam • (A⁻¹ *ᵥ c)) c) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec, smul_vecMulVec]
  have hsmul : Matrix.vecMulVec (lam • c) c = lam • Matrix.vecMulVec c c := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfac, Matrix.det_mul, hv,
    Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) (lam • (A⁻¹ *ᵥ c)) c,
    dotProduct_smul, smul_eq_mul]

/-- The one-step potential factor: `det A' = rho0 n ρ · det A`. -/
noncomputable def rho0R (n : ℕ) (ρ : ℝ) : ℝ :=
  ((n : ℝ) ^ 2 - 1) ^ n * ((n : ℝ) + 1) / (((n : ℝ) - 1) * ((n : ℝ) + ρ) ^ (2 * n))

theorem rho0R_pos {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < rho0R n ρ := by
  have hn2 := natCast_two_le hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hnd : (0:ℝ) < (n:ℝ) + ρ := by linarith
  have hnp1 : (0:ℝ) < (n:ℝ) + 1 := by linarith
  have hnsq : (0:ℝ) < (n:ℝ) ^ 2 - 1 := by nlinarith
  rw [rho0R]
  exact div_pos (mul_pos (pow_pos hnsq n) hnp1) (mul_pos hn1 (pow_pos hnd (2 * n)))

/-- `rho0 n ρ` is decreasing in the normalised depth `ρ`: a shallower cut is a larger step. -/
theorem rho0R_anti {n : ℕ} (hn : 2 ≤ n) {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (h : ρ ≤ ρ') :
    rho0R n ρ' ≤ rho0R n ρ := by
  have hn2 := natCast_two_le hn
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hbase : (0:ℝ) ≤ (n:ℝ) + ρ := by linarith
  have hmono : ((n : ℝ) + ρ) ^ (2 * n) ≤ ((n : ℝ) + ρ') ^ (2 * n) :=
    pow_le_pow_left₀ hbase (by linarith) _
  have hpos : (0:ℝ) < ((n : ℝ) + ρ) ^ (2 * n) :=
    pow_pos (by linarith : (0:ℝ) < (n:ℝ) + ρ) _
  have hnsq : (0:ℝ) < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hnum : (0:ℝ) ≤ ((n : ℝ) ^ 2 - 1) ^ n * ((n : ℝ) + 1) :=
    (mul_pos (pow_pos hnsq n) (by linarith : (0:ℝ) < (n:ℝ) + 1)).le
  rw [rho0R, rho0R]
  exact div_le_div_of_nonneg_left hnum (mul_pos hn1 hpos)
    (mul_le_mul_of_nonneg_left hmono hn1.le)

/-- **The determinant of one step**, `det A' = rho0 n ρ · det A`. -/
theorem stepShape_det {n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    {c p : Fin n → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) (ρ : ℝ) :
    (stepShape n A c p ρ).det = A.det * rho0R n ρ := by
  have hσ : sigmaR c p ≠ 0 := (sigmaR_pos hA hAp hc).ne'
  have hinv : c ⬝ᵥ (A⁻¹ *ᵥ c) = sigmaR c p := by
    rw [inv_mulVec_eq_of_mulVec_eq hA hAp]; rfl
  rw [stepShape, rho0R, Matrix.det_smul, Fintype.card_fin,
    det_add_smul_vecMulVec (mul_inv_of_posDef hA) c (betaR n / sigmaR c p),
    show (betaR n / sigmaR c p) * (c ⬝ᵥ (A⁻¹ *ᵥ c)) = betaR n from by
      rw [hinv]; exact div_mul_cancel₀ _ hσ,
    one_add_betaR hn, alphaR, div_pow, pow_mul]
  try field_simp
  try ring

/-! ## 2.  The exact rational step

The engine computes with rationals only.  The state matrix `A` and the cut data `(c, p, ρ)` are
rational, and the update

    A' = ((n²-1)/(n+ρ)²) • (A + ((2/(n-1))/(c ⬝ᵥ p)) • c cᵀ)

is a rational matrix — no square root is taken.  `rStep_cast` says the cast of this matrix **is**
`stepShape` at the cast data, so every real-geometry statement of §1 applies verbatim to the
engine's exact iterate, with no approximation error.
-/

/-- `β = 2/(n-1)` over `ℚ`. -/
noncomputable def betaQ (n : ℕ) : ℚ := 2 / ((n : ℚ) - 1)

/-- `α = (n²-1)/(n+ρ)²` over `ℚ`. -/
noncomputable def alphaQ (n : ℕ) (ρ : ℚ) : ℚ := ((n : ℚ) ^ 2 - 1) / ((n : ℚ) + ρ) ^ 2

/-- `σ = c ⬝ᵥ p` over `ℚ` (the engine's exact squared cut norm, `p` being its witness of
`A p = c`). -/
def sigmaQ (c p : Fin n → ℚ) : ℚ := c ⬝ᵥ p

/-- **The rational engine step**: `A ↦ α • (A + (β/σ) • c cᵀ)`. -/
noncomputable def rStep (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (c p : Fin n → ℚ) (ρ : ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  alphaQ n ρ • (A + (betaQ n / sigmaQ c p) • Matrix.vecMulVec c c)

theorem cast_betaQ (n : ℕ) : ((betaQ n : ℚ) : ℝ) = betaR n := by
  rw [betaQ, betaR]
  push_cast
  rfl

theorem cast_alphaQ (n : ℕ) (ρ : ℚ) : ((alphaQ n ρ : ℚ) : ℝ) = alphaR n (ρ : ℝ) := by
  rw [alphaQ, alphaR]
  push_cast
  rfl

theorem cast_sigmaQ (c p : Fin n → ℚ) :
    ((sigmaQ c p : ℚ) : ℝ) = sigmaR (fun i => (c i : ℝ)) (fun i => (p i : ℝ)) := by
  simp only [sigmaQ, sigmaR, dotProduct, Rat.cast_sum, Rat.cast_mul]

/-- **The cast bridge for the engine step**: the exact rational update is the real step. -/
theorem rStep_cast (A : Matrix (Fin n) (Fin n) ℚ) (c p : Fin n → ℚ) (ρ : ℚ) :
    castM (rStep n A c p ρ)
      = stepShape n (castM A) (fun i => (c i : ℝ)) (fun i => (p i : ℝ)) (ρ : ℝ) := by
  have hα := cast_alphaQ n ρ
  have hβ := cast_betaQ n
  have hσ := cast_sigmaQ c p
  ext i j
  simp only [castM_apply, rStep, stepShape, Matrix.smul_apply, Matrix.add_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  push_cast
  rw [hα, hβ, hσ]

/-- The cast of the witness relation: `A p = c` over `ℚ` gives `A p = c` over `ℝ`. -/
theorem cast_mulVec (A : Matrix (Fin n) (Fin n) ℚ) (p : Fin n → ℚ) :
    castM A *ᵥ (fun i => (p i : ℝ)) = fun i => ((A *ᵥ p) i : ℝ) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, castM_apply, Rat.cast_sum, Rat.cast_mul]

/-- `σ` positivity transports from `ℝ` to `ℚ` — this is what makes the rational margin checks
exact (`0 < σ`, `σ ≠ 0`) rather than approximate. -/
theorem sigmaQ_pos_of_cast {c p : Fin n → ℚ}
    (hσ : 0 < sigmaR (fun i => (c i : ℝ)) (fun i => (p i : ℝ))) : 0 < sigmaQ c p := by
  have h : ((sigmaQ c p : ℚ) : ℝ) = sigmaR (fun i => (c i : ℝ)) (fun i => (p i : ℝ)) :=
    cast_sigmaQ c p
  have h' : (0:ℝ) < ((sigmaQ c p : ℚ) : ℝ) := by rw [h]; exact hσ
  exact Rat.cast_pos.mp h'

/-! ## 3.  The iterate loop

A run of the engine is a stream of cut records `(c, p, ρ)`: the direction returned by the separation
oracle, the exact rational witness of `A p = c`, and the normalised depth `ρ ≥ 0` at which the cut
is taken (the oracle's absolute margin is `ρ · √σ`).  `Aat` is the engine's exact rational shape
matrix after `k` steps; `Cat` is the real centre of the `k`-th ellipsoid, written as a real
expression of the rational data (its `1/√σ` factor is the only irrational ingredient, and it is
never needed inside the state).
-/

/-- One recorded cut: normal, exact witness of `A p = c`, and normalised depth. -/
structure CutData (n : ℕ) where
  /-- the cut normal returned by the separation oracle -/
  c : Fin n → ℚ
  /-- the engine's exact witness of `A p = c` (`σ = c ⬝ᵥ p`, no inverse needed) -/
  p : Fin n → ℚ
  /-- the normalised depth `ρ = margin / √σ ∈ [0,1]` -/
  rho : ℚ

/-- The engine's exact rational shape matrix after `k` steps. -/
noncomputable def Aat (n : ℕ) (A0 : Matrix (Fin n) (Fin n) ℚ) (cd : ℕ → CutData n) :
    ℕ → Matrix (Fin n) (Fin n) ℚ
  | 0 => A0
  | (k + 1) => rStep n (Aat n A0 cd k) (cd k).c (cd k).p (cd k).rho

/-- The real centre of the `k`-th ellipsoid, as a real expression of the rational data. -/
noncomputable def Cat (n : ℕ) (a0 : Fin n → ℝ) (cd : ℕ → CutData n) : ℕ → (Fin n → ℝ)
  | 0 => a0
  | (k + 1) =>
      stepCentre n (Cat n a0 cd k) (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ))
        ((cd k).rho : ℝ)

/-- The cast of the `k`-th cut normal. -/
abbrev cutCR (cd : ℕ → CutData n) (k : ℕ) : Fin n → ℝ := fun i => ((cd k).c i : ℝ)

/-- The cast of the `k`-th cut witness. -/
abbrev cutPR (cd : ℕ → CutData n) (k : ℕ) : Fin n → ℝ := fun i => ((cd k).p i : ℝ)

theorem Aat_unfold (A0 : Matrix (Fin n) (Fin n) ℚ) (cd : ℕ → CutData n) (k : ℕ) :
    Aat n A0 cd (k + 1) = rStep n (Aat n A0 cd k) (cd k).c (cd k).p (cd k).rho := rfl

theorem Cat_unfold (a0 : Fin n → ℝ) (cd : ℕ → CutData n) (k : ℕ) :
    Cat n a0 cd (k + 1)
      = stepCentre n (Cat n a0 cd k) (cutCR cd k) (cutPR cd k) ((cd k).rho : ℝ) := rfl

/-- The engine loop under the phase-3 interface name: the rational shape matrix after `k` steps
(`Aat` is the recursion; this is its name in the brick's contract). -/
noncomputable def engineLoop (n : ℕ) (A0 : Matrix (Fin n) (Fin n) ℚ) (cd : ℕ → CutData n) :
    ℕ → Matrix (Fin n) (Fin n) ℚ :=
  Aat n A0 cd

/-- The witness relation casts: `A_k p_k = c_k` over `ℚ` is `A_k p_k = c_k` over `ℝ`. -/
theorem cast_witness {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n}
    (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c) (k : ℕ) :
    castM (Aat n A0 cd k) *ᵥ cutPR cd k = cutCR cd k := by
  rw [cast_mulVec, hwit k]

theorem cast_normal_ne {cd : ℕ → CutData n} {k : ℕ} (hc : (cd k).c ≠ 0) : cutCR cd k ≠ 0 := by
  intro h
  apply hc
  funext i
  simpa using congrFun h i

/-- **(i) The iterates stay positive definite.**  Every iterate's cast is positive definite, hence
every iterate is `PosQ` over `ℚ`: the engine's exact arithmetic reproduces the real GLS step
(`rStep_cast`), and the step preserves positive definiteness (`stepShape_posDef`). -/
theorem Aat_cast_posDef {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) :
    ∀ k, (castM (Aat n A0 cd k)).PosDef
  | 0 => hA0
  | (k + 1) => by
      have hk : (castM (Aat n A0 cd k)).PosDef := Aat_cast_posDef hn hA0 hwit hρ hcne k
      rw [Aat_unfold, rStep_cast]
      refine stepShape_posDef hn hk (cast_normal_ne (hcne k)) (cast_witness hwit k) ?_
      exact_mod_cast hρ k

/-- **(i) in rational form**: every iterate satisfies the engine's rational positivity test. -/
theorem Aat_posQ {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n}
    (hA0 : (castM A0).PosDef) (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) :
    ∀ k, PosQ (Aat n A0 cd k) := fun k =>
  posQ_of_cast (Aat_cast_posDef hn hA0 hwit hρ hcne k)

/-- **(ii-a) The containment invariant propagates.**  A body covered by the initial ellipsoid and
lying in every recorded cut halfspace stays inside *every* iterate's ellipsoid: this is the
invariant the engine's "threshold body" keeps across the whole run. -/
theorem body_containment {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin n → ℝ) (body : (Fin n → ℝ) → Prop)
    (hcover : ∀ z, body z → Ell (castM A0) a0 z)
    (hcut : ∀ k z, body z →
      -(((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)) ≤ cutCR cd k ⬝ᵥ (z - Cat n a0 cd k)) :
    ∀ k z, body z → Ell (castM (Aat n A0 cd k)) (Cat n a0 cd k) z
  | 0 => fun z hz => hcover z hz
  | (k + 1) => by
      intro z hz
      have hk : Ell (castM (Aat n A0 cd k)) (Cat n a0 cd k) z :=
        body_containment hn hA0 hwit hρ hcne a0 body hcover hcut k z hz
      have hstep := step_containment hn (Aat_cast_posDef hn hA0 hwit hρ hcne k)
        (cast_normal_ne (hcne k)) (cast_witness hwit k) (Cat n a0 cd k)
        (by exact_mod_cast hρ k : (0:ℝ) ≤ ((cd k).rho : ℝ))
      rw [Aat_unfold, rStep_cast, Cat_unfold]
      exact hstep ⟨hk, hcut k z hz⟩

/-! ## 4.  The potential: exact determinant telescoping, the phase-2 rate, and contraction

The engine's potential is the ellipsoid volume `Φ_k = 1/√(det A_k)` (`vol E = vol(ball)/√det`).
Because the step is exact, `det A_k` is an **exactly computable rational number** and telescopes
over the run with the closed-form factor `rho0 n ρ_k`.  Two consequences are recorded:

* the phase-2 rate `log det A_k ≤ log det A_0 + 2k/(n-1)` of `EllipsoidStep.logdet_stepMatrix`
  (uniform in the recorded depths) — the ellipsoid can never shrink faster than that per step;
* in the shallow regime `ρ_k ≤ ρmax` with `1 < rho0 n ρmax`, the determinant grows geometrically and
  `Φ_k` contracts by the factor `1/√(rho0 n ρmax) < 1`, so after `K` iterations the potential is
  below any prescribed radius.  `Aat_vol_below_of_halving` turns this into an *explicit* count:
  `K = k₀ · m` where `m` is any halving time of the contraction factor and `2^{k₀}` clears the
  ratio `Φ_0/ε` — the `IterBound` halving shape.
-/

/-- The phase-2 log-rate at zero depth: `log (rho0 n 0) ≤ 2/(n-1)`. -/
theorem log_rho0R_zero_le {n : ℕ} (hn : 2 ≤ n) : Real.log (rho0R n 0) ≤ 2 / ((n : ℝ) - 1) := by
  have h0 : rho0R n 0
      = ((n:ℝ) ^ 2 - 1) ^ n * ((n:ℝ) + 1) / (((n:ℝ) - 1) * (n:ℝ) ^ (2 * n)) := by
    rw [rho0R]; norm_num
  rw [h0]
  have hn2 := natCast_two_le hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hnsq : (0:ℝ) < (n:ℝ) ^ 2 - 1 := by nlinarith
  have hn1' : (0:ℝ) < 1 - 1 / (n:ℝ) ^ 2 := by
    have h : 1 / (n:ℝ) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    linarith
  have hbase : ((n:ℝ) ^ 2 - 1) = (n:ℝ) ^ 2 * (1 - 1 / (n:ℝ) ^ 2) := by
    field_simp; try ring
  have hpow : ((n:ℝ) ^ 2 - 1) ^ n = (n:ℝ) ^ (2 * n) * (1 - 1 / (n:ℝ) ^ 2) ^ n := by
    rw [hbase, mul_pow, pow_mul]
  have hEq : ((n:ℝ) ^ 2 - 1) ^ n * ((n:ℝ) + 1) / (((n:ℝ) - 1) * (n:ℝ) ^ (2 * n))
      = (1 - 1 / (n:ℝ) ^ 2) ^ n * (((n:ℝ) + 1) / ((n:ℝ) - 1)) := by
    rw [hpow]
    field_simp; try ring
  rw [hEq, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hA1 : Real.log (1 - 1 / (n:ℝ) ^ 2) ≤ -(1 / (n:ℝ) ^ 2) := by
    have := Real.log_le_sub_one_of_pos hn1'
    linarith
  have hA2 : Real.log (((n:ℝ) + 1) / ((n:ℝ) - 1)) ≤ 2 / ((n:ℝ) - 1) := by
    have hpos : (0:ℝ) < ((n:ℝ) + 1) / ((n:ℝ) - 1) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have hsub : ((n:ℝ) + 1) / ((n:ℝ) - 1) - 1 = 2 / ((n:ℝ) - 1) := by
      field_simp
      ring
    linarith
  have hmul : (n:ℝ) * Real.log (1 - 1 / (n:ℝ) ^ 2) ≤ (n:ℝ) * (-(1 / (n:ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hA1 hnpos.le
  have hsimp : (n:ℝ) * (-(1 / (n:ℝ) ^ 2)) = -(1 / (n:ℝ)) := by
    field_simp; try ring
  have hinv : (0:ℝ) < 1 / (n:ℝ) := by positivity
  linarith [hmul, hA2, hsimp, hinv]

/-- The phase-2 rate at any recorded depth. -/
theorem log_rho0R_le {n : ℕ} (hn : 2 ≤ n) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Real.log (rho0R n ρ) ≤ 2 / ((n : ℝ) - 1) := by
  have hanti : rho0R n ρ ≤ rho0R n 0 := rho0R_anti hn (le_refl 0) hρ
  calc Real.log (rho0R n ρ) ≤ Real.log (rho0R n 0) := Real.log_le_log (rho0R_pos hn hρ) hanti
    _ ≤ 2 / ((n : ℝ) - 1) := log_rho0R_zero_le hn

/-- **The determinant telescopes exactly** over the run: `det A_k = det A_0 · ∏_{j<k} rho0 n ρ_j`.
Both factors are rational, so the engine can compute and certify this identity in exact
arithmetic. -/
theorem Aat_det {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n}
    (hA0 : (castM A0).PosDef) (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) :
    ∀ k, (castM (Aat n A0 cd k)).det
      = (castM A0).det * ∏ j ∈ Finset.range k, rho0R n ((cd j).rho : ℝ)
  | 0 => by simp [Aat]
  | (k + 1) => by
      have hk := Aat_det hn hA0 hwit hρ hcne k
      rw [Aat_unfold, rStep_cast,
        stepShape_det hn (Aat_cast_posDef hn hA0 hwit hρ hcne k) (cast_normal_ne (hcne k))
          (cast_witness hwit k) ((cd k).rho : ℝ),
        hk, Finset.prod_range_succ]
      ring

/-- **The phase-2 rate**: after `k` recorded cuts the log-determinant has grown by at most
`2k/(n-1)`, uniformly in the depths (the ellipsoid cannot shrink faster than that). -/
theorem Aat_logdet_le {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) :
    ∀ k, Real.log ((castM (Aat n A0 cd k)).det)
      ≤ Real.log ((castM A0).det) + 2 * (k:ℝ) / ((n:ℝ) - 1)
  | 0 => by simp [Aat]
  | (k + 1) => by
      have hpd := Aat_cast_posDef hn hA0 hwit hρ hcne k
      have hdet0 : (0:ℝ) < (castM (Aat n A0 cd k)).det := hpd.det_pos
      have hr0 : (0:ℝ) < rho0R n ((cd k).rho : ℝ) :=
        rho0R_pos hn (by exact_mod_cast hρ k : (0:ℝ) ≤ ((cd k).rho : ℝ))
      have hstep : (castM (Aat n A0 cd (k + 1))).det
          = (castM (Aat n A0 cd k)).det * rho0R n ((cd k).rho : ℝ) := by
        rw [Aat_unfold, rStep_cast,
          stepShape_det hn hpd (cast_normal_ne (hcne k)) (cast_witness hwit k) ((cd k).rho : ℝ)]
      have ih := Aat_logdet_le hn hA0 hwit hρ hcne k
      have hb := log_rho0R_le hn (by exact_mod_cast hρ k : (0:ℝ) ≤ ((cd k).rho : ℝ))
      rw [hstep, Real.log_mul (ne_of_gt hdet0) (ne_of_gt hr0)]
      push_cast
      have harith : 2 * ((k:ℝ) + 1) / ((n:ℝ) - 1)
          = 2 * (k:ℝ) / ((n:ℝ) - 1) + 2 / ((n:ℝ) - 1) := by
        field_simp
      rw [harith]
      linarith

/-- **Determinant growth in the shallow regime**: if every recorded depth is at most `ρmax`, then
`det A_k ≥ det A_0 · (rho0 n ρmax)^k`, exactly. -/
theorem Aat_det_ge {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n}
    (hA0 : (castM A0).PosDef) (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax) (k : ℕ) :
    (castM A0).det * (rho0R n (ρmax : ℝ)) ^ k ≤ (castM (Aat n A0 cd k)).det := by
  rw [Aat_det hn hA0 hwit hρ hcne k]
  have hdet0 : (0:ℝ) ≤ (castM A0).det := hA0.det_pos.le
  have hprod : (∏ j ∈ Finset.range k, rho0R n ((ρmax : ℝ)))
      ≤ ∏ j ∈ Finset.range k, rho0R n ((cd j).rho : ℝ) := by
    refine Finset.prod_le_prod
      (fun j _ => (rho0R_pos hn (by exact_mod_cast hρmax : (0:ℝ) ≤ (ρmax : ℝ))).le)
      (fun j _ => ?_)
    · exact rho0R_anti hn (by exact_mod_cast hρ j : (0:ℝ) ≤ ((cd j).rho : ℝ))
        (by exact_mod_cast hle j : ((cd j).rho : ℝ) ≤ (ρmax : ℝ))
  have hconst : (∏ j ∈ Finset.range k, rho0R n ((ρmax : ℝ))) = (rho0R n (ρmax : ℝ)) ^ k := by
    simp [Finset.prod_const]
  rw [hconst] at hprod
  exact mul_le_mul_of_nonneg_left hprod hdet0

/-- The **volume potential** of the engine's ellipsoid: `1/√(det A)` (`vol E = vol(ball) √(det A)⁻¹`). -/
noncomputable def volPot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) : ℝ :=
  (Real.sqrt (castM A).det)⁻¹

theorem volPot_pos {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : (castM A).PosDef) :
    0 < volPot n A :=
  inv_pos.mpr (Real.sqrt_pos.2 hA.det_pos)

/-- **Volume contraction in the shallow regime**: `Φ_k ≤ (√(rho0 n ρmax))^{-k} Φ_0`. -/
theorem Aat_vol_le {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n}
    (hA0 : (castM A0).PosDef) (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax) (k : ℕ) :
    volPot n (Aat n A0 cd k)
      ≤ (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ k * volPot n A0 := by
  have hspos : (0:ℝ) < rho0R n (ρmax : ℝ) :=
    rho0R_pos hn (by exact_mod_cast hρmax : (0:ℝ) ≤ (ρmax : ℝ))
  have hdet0 : (0:ℝ) < (castM A0).det := hA0.det_pos
  have hdetk : (0:ℝ) < (castM (Aat n A0 cd k)).det :=
    (Aat_cast_posDef hn hA0 hwit hρ hcne k).det_pos
  have hge := Aat_det_ge hn hA0 hwit hρ hcne hρmax hle k
  -- square roots: √(det₀ · sᵏ) = √det₀ · (√s)ᵏ
  have hsqrtpow : ∀ j : ℕ, Real.sqrt ((rho0R n (ρmax : ℝ)) ^ j)
      = (Real.sqrt (rho0R n (ρmax : ℝ))) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, Real.sqrt_mul (le_of_lt (pow_pos hspos i)), ih, pow_succ]
  have hsqrt : Real.sqrt ((castM A0).det * (rho0R n (ρmax : ℝ)) ^ k)
      = Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k := by
    rw [Real.sqrt_mul (le_of_lt hdet0), hsqrtpow]
  have hle' : Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k
      ≤ Real.sqrt ((castM (Aat n A0 cd k)).det) := by
    rw [← hsqrt]
    exact Real.sqrt_le_sqrt hge
  have hpos' : (0:ℝ) < Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k :=
    mul_pos (Real.sqrt_pos.2 hdet0) (pow_pos (Real.sqrt_pos.2 hspos) k)
  have hinv : (Real.sqrt ((castM (Aat n A0 cd k)).det))⁻¹
      ≤ (Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k)⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 hdetk) hpos').mpr hle'
  calc volPot n (Aat n A0 cd k) ≤
        (Real.sqrt ((castM A0).det) * (Real.sqrt (rho0R n (ρmax : ℝ))) ^ k)⁻¹ := hinv
    _ = (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ k * volPot n A0 := by
        rw [mul_inv, inv_pow, volPot]
        ring

/-- **The potential drops below any prescribed radius**: in the shallow regime with a genuine
contraction factor (`1 < rho0 n ρmax`) there is a run length `K` with `Φ_K ≤ ε`. -/
theorem Aat_vol_below {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n}
    (hA0 : (castM A0).PosDef) (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    (hcontract : 1 < rho0R n (ρmax : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, volPot n (Aat n A0 cd K) ≤ ε := by
  have hspos : (0:ℝ) < rho0R n (ρmax : ℝ) := lt_trans one_pos hcontract
  have hsqrts : 1 < Real.sqrt (rho0R n (ρmax : ℝ)) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using hcontract
  have hc1 : (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hsqrts
  have hΦpos : 0 < volPot n A0 := volPot_pos hA0
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (x := ε / volPot n A0)
    (y := (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹) (div_pos hε hΦpos) hc1
  refine ⟨K, ?_⟩
  refine le_trans (Aat_vol_le hn hA0 hwit hρ hcne hρmax hle K) ?_
  refine le_of_lt ?_
  calc (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ K * volPot n A0
      = volPot n A0 * (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ K := by ring
    _ < volPot n A0 * (ε / volPot n A0) := mul_lt_mul_of_pos_left hK hΦpos
    _ = ε := by field_simp

/-- **An explicit count via halving.**  If `m` steps halve the potential factor and `2^K` clears the
ratio `Φ_0/ε`, then `K·m` iterations bring the potential below `ε` — the explicit
`IterBound`-shaped stopping rule, with no logarithms. -/
theorem Aat_vol_below_of_halving {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    {m K : ℕ} (hm : (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    {ε : ℝ} (hK : volPot n A0 * (1 / 2) ^ K ≤ ε) :
    volPot n (Aat n A0 cd (K * m)) ≤ ε := by
  have hc0 : (0:ℝ) ≤ (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ := by positivity
  have h1 := Aat_vol_le hn hA0 hwit hρ hcne hρmax hle (K * m)
  have hpow : (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ (K * m) ≤ (1 / 2) ^ K := by
    rw [Nat.mul_comm, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hc0 m) hm K
  have hΦ0 : (0:ℝ) ≤ volPot n A0 := (volPot_pos hA0).le
  calc volPot n (Aat n A0 cd (K * m))
      ≤ (Real.sqrt (rho0R n (ρmax : ℝ)))⁻¹ ^ (K * m) * volPot n A0 := h1
    _ ≤ (1 / 2) ^ K * volPot n A0 :=
        mul_le_mul_of_nonneg_right hpow hΦ0
    _ = volPot n A0 * (1 / 2) ^ K := by ring
    _ ≤ ε := hK

/-- **The engine run terminates.**  There is a run length `K` at which the threshold body sits in
the `K`-th ellipsoid *and* the volume potential is below `ε`: the body is squeezed into an ellipsoid
of volume at most `ε · vol(ball)`, and the recorded histogram is what the finalization brick consumes
from the last centre. -/
theorem engine_run {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ} {cd : ℕ → CutData n}
    (hA0 : (castM A0).PosDef) (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin n → ℝ) (body : (Fin n → ℝ) → Prop)
    (hcover : ∀ z, body z → Ell (castM A0) a0 z)
    (hcut : ∀ k z, body z →
      -(((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)) ≤ cutCR cd k ⬝ᵥ (z - Cat n a0 cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    (hcontract : 1 < rho0R n (ρmax : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, (∀ z, body z → Ell (castM (Aat n A0 cd K)) (Cat n a0 cd K) z) ∧
      volPot n (Aat n A0 cd K) ≤ ε := by
  obtain ⟨K, hK⟩ := Aat_vol_below hn hA0 hwit hρ hcne hρmax hle hcontract hε
  exact ⟨K, body_containment hn hA0 hwit hρ hcne a0 body hcover hcut K, hK⟩

/-- **The engine run with the oracle's absolute margins.**  The separation oracle reports a cut
normal `c` *and* an absolute margin `δ` (the amount by which the violated halfspace misses the
centre).  The engine chooses a rational normalised depth `ρ` with `δ² ≤ ρ²σ` (`margin_le_of_sq_check`,
an exact rational comparison) and records the cut at depth `ρ`; the surviving body then stays inside
every iterate's ellipsoid and the potential still drops below `ε`.  This is the interface between
`brick-sep-oracle` and the loop. -/
theorem engine_run_margin {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (a0 : Fin n → ℝ) (body : (Fin n → ℝ) → Prop)
    (hcover : ∀ z, body z → Ell (castM A0) a0 z)
    {δ : ℕ → ℚ} (hδ0 : ∀ k, 0 ≤ δ k)
    (hcheck : ∀ k, (δ k) ^ 2 ≤ ((cd k).rho) ^ 2 * sigmaQ (cd k).c (cd k).p)
    (hcutδ : ∀ k z, body z → -(((δ k : ℚ)) : ℝ) ≤ cutCR cd k ⬝ᵥ (z - Cat n a0 cd k))
    {ρmax : ℚ} (hρmax : 0 ≤ ρmax) (hle : ∀ k, (cd k).rho ≤ ρmax)
    (hcontract : 1 < rho0R n (ρmax : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, (∀ z, body z → Ell (castM (Aat n A0 cd K)) (Cat n a0 cd K) z) ∧
      volPot n (Aat n A0 cd K) ≤ ε := by
  have hcut : ∀ k z, body z →
      -(((cd k).rho : ℝ) * sqrtSigmaR (cutCR cd k) (cutPR cd k)) ≤
        cutCR cd k ⬝ᵥ (z - Cat n a0 cd k) := by
    intro k z hz
    have hσR : 0 < sigmaR (cutCR cd k) (cutPR cd k) :=
      sigmaR_pos (Aat_cast_posDef hn hA0 hwit hρ hcne k) (cast_witness hwit k)
        (cast_normal_ne (hcne k))
    have hδle : (((δ k : ℚ)) : ℝ)
        ≤ ((cd k).rho : ℝ) * Real.sqrt ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) :=
      margin_le_of_sq_check (hδ0 k) (hρ k) (sigmaQ_pos_of_cast hσR).le (hcheck k)
    have hσeq : ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) = sigmaR (cutCR cd k) (cutPR cd k) :=
      cast_sigmaQ (cd k).c (cd k).p
    rw [hσeq] at hδle
    exact le_trans (neg_le_neg hδle) (hcutδ k z hz)
  exact engine_run hn hA0 hwit hρ hcne a0 body hcover hcut hρmax hle hcontract hε

/-- **One central cut always makes progress**: a cut taken through the iterate's centre
(`ρ = 0`, the case of exact rational separation, where the violated test vector gives the normal)
multiplies the volume potential by exactly `(√(rho0 n 0))⁻¹ < 1`.  So the engine's stopping rule
("either the centre passes the checks, or a cut is available") always makes progress. -/
theorem central_step_progress {n : ℕ} (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : (castM A).PosDef) {c p : Fin n → ℚ} (hc : c ≠ 0) (hwit : A *ᵥ p = c) :
    volPot n (rStep n A c p 0) ≤ (Real.sqrt (rho0R n 0))⁻¹ * volPot n A := by
  have hApR : castM A *ᵥ (fun i => (p i : ℝ)) = fun i => (c i : ℝ) := by
    rw [cast_mulVec, hwit]
  have hcR : (fun i => (c i : ℝ)) ≠ 0 := fun h => hc (cast_fun_eq_zero h)
  have hspos : (0:ℝ) < rho0R n 0 := rho0R_pos hn le_rfl
  have hdet0 : (0:ℝ) < (castM A).det := hA.det_pos
  have hstep : (castM (rStep n A c p 0)).det = (castM A).det * rho0R n 0 := by
    rw [rStep_cast]
    have h := stepShape_det hn hA hcR hApR ((0 : ℚ) : ℝ)
    simpa using h
  have hpd : (castM (rStep n A c p 0)).PosDef := by
    rw [rStep_cast]
    exact stepShape_posDef hn hA hcR hApR (by norm_num)
  have hle : Real.sqrt ((castM A).det) * Real.sqrt (rho0R n 0)
      ≤ Real.sqrt ((castM (rStep n A c p 0)).det) := by
    rw [hstep, Real.sqrt_mul hdet0.le]
  have hinv : (Real.sqrt ((castM (rStep n A c p 0)).det))⁻¹
      ≤ (Real.sqrt ((castM A).det) * Real.sqrt (rho0R n 0))⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 hpd.det_pos)
      (mul_pos (Real.sqrt_pos.2 hdet0) (Real.sqrt_pos.2 hspos))).mpr hle
  calc volPot n (rStep n A c p 0)
      ≤ (Real.sqrt ((castM A).det) * Real.sqrt (rho0R n 0))⁻¹ := hinv
    _ = (Real.sqrt (rho0R n 0))⁻¹ * volPot n A := by
        simp only [volPot, mul_inv]; ring

/-! ### 4.1  Non-vacuity: central cuts always contract

`ρmax = 0` (a cut through the centre) satisfies the contraction hypothesis for every `n ≥ 2`:
`rho0 n 0 = (1-1/n²)^n (n+1)/(n-1) ≥ (1-1/n)(n+1)/(n-1) = (n+1)/n > 1`. -/

theorem rho0R_zero_eq {n : ℕ} (hn : 2 ≤ n) : rho0R n 0
    = (1 - 1 / (n:ℝ)^2)^n * (((n:ℝ)+1)/((n:ℝ)-1)) := by
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith [natCast_two_le hn]
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith [natCast_two_le hn]
  have hbase : ((n:ℝ)^2 - 1) = (n:ℝ)^2 * (1 - 1/(n:ℝ)^2) := by
    field_simp; try ring
  have hpow : ((n:ℝ)^2-1)^n = (n:ℝ)^(2*n) * (1 - 1/(n:ℝ)^2)^n := by
    rw [hbase, mul_pow, pow_mul]
  have h1 : ((n:ℝ) - 1) ≠ 0 := ne_of_gt hn1
  have h2 : ((n:ℝ))^(2*n) ≠ 0 := ne_of_gt (pow_pos hnpos _)
  simp only [rho0R, add_zero, hpow]
  field_simp; try ring

/-- **Central cuts always contract**: `1 < rho0 n 0` for every `n ≥ 2`. -/
theorem one_lt_rho0R_zero {n : ℕ} (hn : 2 ≤ n) : 1 < rho0R n 0 := by
  rw [rho0R_zero_eq hn]
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith [natCast_two_le hn]
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith [natCast_two_le hn]
  have hbern : (1:ℝ) - 1/(n:ℝ) ≤ (1 - 1/(n:ℝ)^2)^n := by
    have h := one_add_mul_le_pow (a := -(1/(n:ℝ)^2)) (by
      have hpos : (0:ℝ) < 1/(n:ℝ)^2 := by positivity
      have hle : 1/(n:ℝ)^2 ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      linarith) n
    have e1 : (1:ℝ) + (n:ℝ) * (-(1/(n:ℝ)^2)) = 1 - 1/(n:ℝ) := by
      field_simp; try ring
    have e2 : (1:ℝ) + -(1/(n:ℝ)^2) = 1 - 1/(n:ℝ)^2 := by ring
    rw [e1, e2] at h
    exact h
  have hpos2 : (0:ℝ) < ((n:ℝ)+1)/((n:ℝ)-1) := div_pos (by linarith) hn1
  have hmain : (1 - 1/(n:ℝ)) * (((n:ℝ)+1)/((n:ℝ)-1)) = ((n:ℝ)+1)/(n:ℝ) := by
    have e : (1:ℝ) - 1/(n:ℝ) = ((n:ℝ)-1)/(n:ℝ) := by
      field_simp
    rw [e]
    field_simp; try ring
  have hgt : (1:ℝ) < ((n:ℝ)+1)/(n:ℝ) := by
    rw [lt_div_iff₀ hnpos]
    linarith
  have hle := mul_le_mul_of_nonneg_right hbern hpos2.le
  rw [hmain] at hle
  linarith

/-- The engine's stopping theorem at central cuts (`ρmax = 0`), i.e. the contraction hypothesis of
`Aat_vol_below` is *inhabited*: with every recorded cut taken through the centre, the potential
drops below any prescribed radius. -/
theorem Aat_vol_below_central {n : ℕ} (hn : 2 ≤ n) {A0 : Matrix (Fin n) (Fin n) ℚ}
    {cd : ℕ → CutData n} (hA0 : (castM A0).PosDef)
    (hwit : ∀ k, Aat n A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0)
    (hcentral : ∀ k, (cd k).rho ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, volPot n (Aat n A0 cd K) ≤ ε :=
  Aat_vol_below hn hA0 hwit hρ hcne (le_refl 0) hcentral (by simpa using one_lt_rho0R_zero hn) hε

/-! ## 5.  (iii) The histogram extraction

The engine records, at every iteration `t < T`, a cut together with a dual candidate `y t` and a
budget `g t` (the value of the cut's objective at the central point).  `histW` is the uniform
histogram over the record; `dualAvg` is the aggregated dual candidate `ybar = ∑ t, w t • y t`.

The extraction theorem `histogram_record` says the aggregate is **dual feasible** (the rational PSD
test is a nonnegative combination of the per-cut tests) and that its budget is the weighted
*average* `∑ t, w t * g t` of the recorded budgets — per-cut budgets average, they do not add.  These
two conclusions are exactly the `hypTest` and `hbudget` slots of
`QMCLeafB.RoundingOut.rounding_out` (after unfolding `diagonal (dualAvg …) + A`), with the single
aggregated candidate in place of the histogram.
-/

section Histogram

variable {m : ℕ}

theorem qf_add (M N : Matrix (Fin m) (Fin m) ℚ) (x : Fin m → ℚ) :
    qf (M + N) x = qf M x + qf N x := by
  simp [qf, Matrix.add_mulVec, dotProduct_add]

theorem qf_diagonal (e x : Fin m → ℚ) : qf (diagonal e) x = ∑ i, e i * x i ^ 2 := by
  simp only [qf, Matrix.mulVec_diagonal, dotProduct, pow_two]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A diagonal shift of the quadratic form (the shape of the dual slack). -/
theorem qf_diagonal_add (A : Matrix (Fin m) (Fin m) ℚ) (e x : Fin m → ℚ) :
    qf (A + diagonal e) x = qf A x + ∑ i, e i * x i ^ 2 := by
  rw [qf_add, qf_diagonal]

/-- The uniform histogram over `T` recorded cuts. -/
def histW (T : ℕ) [NeZero T] : Fin T → ℚ := fun _ => ((T : ℚ))⁻¹

theorem histW_nonneg (T : ℕ) [NeZero T] (t : Fin T) : 0 ≤ histW T t := by
  simp only [histW]
  exact inv_nonneg.mpr (Nat.cast_nonneg T)

/-- The weights sum to one: the histogram is a probability vector. -/
theorem histW_sum (T : ℕ) [NeZero T] : ∑ t : Fin T, histW T t = 1 := by
  have hT : ((T : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne T)
  simp only [histW, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_cancel₀ hT

/-- The histogram average of the recorded dual candidates. -/
def dualAvg {T : ℕ} (w : Fin T → ℚ) (y : Fin T → Fin m → ℚ) : Fin m → ℚ :=
  fun i => ∑ t, w t * y t i

/-- A convex combination of dual-feasible slacks is dual feasible (symmetry part). -/
theorem dualAvg_symm [Nonempty (Fin m)] {A : Matrix (Fin m) (Fin m) ℚ} (hAsym : Aᵀ = A)
    {T : ℕ} (w : Fin T → ℚ) (y : Fin T → Fin m → ℚ) :
    (diagonal (dualAvg w y) + A)ᵀ = diagonal (dualAvg w y) + A := by
  rw [Matrix.transpose_add, diagonal_transpose, hAsym]

/-- **The quadratic form of the aggregated slack is the histogram average of the recorded ones.** -/
theorem qf_diagonal_dualAvg {A : Matrix (Fin m) (Fin m) ℚ} {T : ℕ} (w : Fin T → ℚ)
    (y : Fin T → Fin m → ℚ) (hw1 : ∑ t, w t = 1) (x : Fin m → ℚ) :
    qf (diagonal (dualAvg w y) + A) x = ∑ t, w t * qf (diagonal (y t) + A) x := by
  have hL : qf (diagonal (dualAvg w y) + A) x = qf A x + ∑ i, (dualAvg w y i) * x i ^ 2 := by
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
theorem dualAvg_test {A : Matrix (Fin m) (Fin m) ℚ} {T : ℕ} {w : Fin T → ℚ}
    {y : Fin T → Fin m → ℚ} (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (htest : ∀ t x, 0 ≤ qf (diagonal (y t) + A) x) :
    ∀ x, 0 ≤ qf (diagonal (dualAvg w y) + A) x := by
  intro x
  rw [qf_diagonal_dualAvg w y hw1 x]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (hw0 t) (htest t x)

/-- The dual objective of the aggregate is the weighted average of the recorded ones. -/
theorem dualAvg_sum {T : ℕ} (w : Fin T → ℚ) (y : Fin T → Fin m → ℚ) :
    (∑ i, dualAvg w y i) = ∑ t, w t * ∑ i, y t i := by
  simp only [dualAvg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]

/-- **The budget of the aggregate**: the recorded per-cut budgets average. -/
theorem dualAvg_budget {A X : Matrix (Fin m) (Fin m) ℚ} {T : ℕ} {w : Fin T → ℚ}
    {y : Fin T → Fin m → ℚ} {g : Fin T → ℚ} (hw0 : ∀ t, 0 ≤ w t) (hw1 : ∑ t, w t = 1)
    (hbudget : ∀ t, (∑ i, y t i) + (A * X).trace ≤ g t) :
    (∑ i, dualAvg w y i) + (A * X).trace ≤ ∑ t, w t * g t := by
  rw [dualAvg_sum]
  have htrw : (A * X).trace = ∑ t, w t * (A * X).trace := by
    rw [← Finset.sum_mul, hw1, one_mul]
  rw [htrw, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t _ => ?_
  have hb := mul_le_mul_of_nonneg_left (hbudget t) (hw0 t)
  calc w t * (∑ i, y t i) + w t * (A * X).trace
      = w t * ((∑ i, y t i) + (A * X).trace) := by ring
    _ ≤ w t * g t := hb

/-- **(iii) The histogram extraction**: the uniform histogram of the engine's record aggregates to a
single dual candidate that is dual feasible and whose budget is the *average* `∑ t, w t g t` of the
recorded budgets.  These are `rounding_out`'s `hypTest`/`hbudget` slots. -/
theorem histogram_record {A X : Matrix (Fin m) (Fin m) ℚ} {T : ℕ} [NeZero T]
    (y : Fin T → Fin m → ℚ) (g : Fin T → ℚ)
    (htest : ∀ t x, 0 ≤ qf (diagonal (y t) + A) x)
    (hbudget : ∀ t, (∑ i, y t i) + (A * X).trace ≤ g t) :
    (∀ x, 0 ≤ qf (diagonal (dualAvg (histW T) y) + A) x) ∧
      (∑ i, dualAvg (histW T) y i) + (A * X).trace ≤ ∑ t, histW T t * g t :=
  ⟨dualAvg_test (fun t => histW_nonneg T t) (histW_sum T) htest,
    dualAvg_budget (fun t => histW_nonneg T t) (histW_sum T) hbudget⟩

/-- The aggregated budget is at most the largest recorded budget (a histogram cannot create
budget, only average it). -/
theorem histogram_budget_le_max {T : ℕ} [NeZero T] {g : Fin T → ℚ} {gmax : ℚ}
    (hmax : ∀ t, g t ≤ gmax) : ∑ t, histW T t * g t ≤ gmax := by
  have h1 : ∀ t : Fin T, histW T t * g t ≤ histW T t * gmax := fun t =>
    mul_le_mul_of_nonneg_left (hmax t) (histW_nonneg T t)
  calc ∑ t, histW T t * g t ≤ ∑ t, histW T t * gmax := Finset.sum_le_sum fun t _ => h1 t
    _ = (∑ t, histW T t) * gmax := by rw [Finset.sum_mul]
    _ = gmax := by rw [histW_sum, one_mul]

end Histogram

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.EngineIterates.central_step_progress

#print axioms QMCLeafB.EngineIterates.engine_run_margin

#print axioms QMCLeafB.EngineIterates.containment_of_margin
#print axioms QMCLeafB.EngineIterates.margin_le_of_sq_check

#print axioms QMCLeafB.EngineIterates.one_lt_rho0R_zero
#print axioms QMCLeafB.EngineIterates.Aat_vol_below_central

#print axioms QMCLeafB.EngineIterates.rStep_cast
#print axioms QMCLeafB.EngineIterates.step_containment
#print axioms QMCLeafB.EngineIterates.stepShape_posDef
#print axioms QMCLeafB.EngineIterates.stepShape_det
#print axioms QMCLeafB.EngineIterates.Aat_posQ
#print axioms QMCLeafB.EngineIterates.body_containment
#print axioms QMCLeafB.EngineIterates.Aat_det
#print axioms QMCLeafB.EngineIterates.Aat_logdet_le
#print axioms QMCLeafB.EngineIterates.Aat_vol_le
#print axioms QMCLeafB.EngineIterates.Aat_vol_below
#print axioms QMCLeafB.EngineIterates.Aat_vol_below_of_halving
#print axioms QMCLeafB.EngineIterates.engine_run
#print axioms QMCLeafB.EngineIterates.histogram_record
#print axioms QMCLeafB.EngineIterates.histogram_budget_le_max


