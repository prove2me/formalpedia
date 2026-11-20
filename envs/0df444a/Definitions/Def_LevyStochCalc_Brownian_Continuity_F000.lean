-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_Continuity_F000
-- name    : LevyStochCalc_Brownian_Continuity_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T08:55:01.88657+00:00
-- url     : https://prove2.me/theorems/d280c8dc-ba51-4b72-8d92-50b8b1066bf6
-- title:
--   Source declarations: LevyStochCalc.Brownian.Continuity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.Continuity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Kolmogorov-Chentsov continuous modification

Mathlib has only `IsKolmogorovProcess` (the *condition*); the modification
result is missing. We port the classical proof (Karatzas-Shreve §2.2 Thm 2.8 /
Le Gall 2016 Thm 2.9):

  *If `(X_t)_{t ≥ 0}` satisfies `𝔼[ |X_t − X_s|^p ] ≤ M · |t − s|^q` for some
  `p, q > 0` with `q > 1` and constant `M`, then there exists a modification
  `X̃` with continuous paths.*

The sub-lemmas of the proof live in two imported modules of the same namespace:
`LevyStochCalc.Brownian.ContinuityDyadicChaining` (Hölder extension from a dense
set, the dyadic rationals, dyadic truncation and the deterministic chaining
bound) and `LevyStochCalc.Brownian.ContinuityKolmogorovBounds` (the Markov tail
bound, the per-level Borel-Cantelli estimates, almost-sure local Hölder
regularity and the modification identity). This module assembles them into
`kolmogorovChentsov_modification` and applies it to Brownian motion, whose
fourth increment moment is computed here from the Gaussian moment generating
function.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Integrability set is `univ` for Gaussian.** `0 ∈ interior (integrableExpSet
id (gaussianReal 0 v))`. -/
lemma zero_mem_interior_integrableExpSet_gaussianReal (v : ℝ≥0) :
    0 ∈ interior
      (ProbabilityTheory.integrableExpSet id (ProbabilityTheory.gaussianReal 0 v)) := by
  rw [ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [interior_univ]
  exact Set.mem_univ 0
/-- **First derivative of `t ↦ exp(c · t²)`.** -/
lemma deriv_exp_quadratic (c : ℝ) :
    deriv (fun t : ℝ => Real.exp (c * t^2)) = fun t => 2 * c * t * Real.exp (c * t^2) := by
  funext t
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_outer : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  rw [h_outer.deriv]
  ring
/-- **First derivative at 0 is 0.** `f'(0) = 2c·0·exp(0) = 0`. -/
lemma iteratedDeriv1_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => Real.exp (c * t^2)) 0 = 0 := by
  rw [iteratedDeriv_one, deriv_exp_quadratic]
  ring
/-- **Second derivative of `t ↦ exp(c · t²)`.** `f''(t) = (2c + 4c²t²) · exp(c·t²)`.

(Equivalently: `f'' = 2c·exp + 4c²·t²·exp`.) -/
lemma deriv2_exp_quadratic (c : ℝ) :
    deriv (deriv (fun t : ℝ => Real.exp (c * t^2)))
      = fun t => (2 * c + 4 * c^2 * t^2) * Real.exp (c * t^2) := by
  rw [deriv_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => 2*c*t * exp(c*t^2)) t = (2c + 4c²t²) exp(c*t²)
  -- Product rule: deriv (g · h) = g' · h + g · h' where g(t) = 2*c*t, h(t) = exp(c*t²).
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  have h_lin : HasDerivAt (fun t : ℝ => 2 * c * t) (2 * c) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * c)
  have h_prod : HasDerivAt (fun t : ℝ => 2 * c * t * Real.exp (c * t^2))
      (2 * c * Real.exp (c * t^2) + 2 * c * t * (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_lin.mul h_exp
  rw [h_prod.deriv]
  ring
/-- **Second derivative at 0 is `2c`.** -/
lemma iteratedDeriv2_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => Real.exp (c * t^2)) 0 = 2 * c := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      deriv2_exp_quadratic]
  simp [Real.exp_zero, mul_comm]
/-- **Third derivative of `t ↦ exp(c · t²)`.**
`f'''(t) = (12c²t + 8c³t³) · exp(c·t²)`. -/
lemma deriv3_exp_quadratic (c : ℝ) :
    deriv (deriv (deriv (fun t : ℝ => Real.exp (c * t^2))))
      = fun t => (12 * c^2 * t + 8 * c^3 * t^3) * Real.exp (c * t^2) := by
  rw [deriv2_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => (2c + 4c²t²) · exp(c*t²)) t = (12c²t + 8c³t³) exp(c*t²)
  -- Use product rule: g(t) := 2c + 4c²t², h(t) := exp(c*t²).
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  have h_quad : HasDerivAt (fun t : ℝ => 2 * c + 4 * c^2 * t^2)
      (4 * c^2 * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (4 * c^2)).const_add (2 * c)
    simpa [pow_one] using this
  have h_prod : HasDerivAt
      (fun t : ℝ => (2 * c + 4 * c^2 * t^2) * Real.exp (c * t^2))
      (4 * c^2 * (2 * t) * Real.exp (c * t^2)
        + (2 * c + 4 * c^2 * t^2) * (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_quad.mul h_exp
  rw [h_prod.deriv]
  ring
/-- **Third derivative at 0 is `0`.** -/
lemma iteratedDeriv3_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => Real.exp (c * t^2)) 0 = 0 := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, deriv3_exp_quadratic]
  ring
/-- **Fourth derivative of `t ↦ exp(c · t²)`.**
`f⁽⁴⁾(t) = (12c² + 48c³t² + 16c⁴t⁴) · exp(c·t²)`. -/
lemma deriv4_exp_quadratic (c : ℝ) :
    deriv (deriv (deriv (deriv (fun t : ℝ => Real.exp (c * t^2)))))
      = fun t => (12 * c^2 + 48 * c^3 * t^2 + 16 * c^4 * t^4) * Real.exp (c * t^2) := by
  rw [deriv3_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => (12c²t + 8c³t³) · exp(c·t²)) t
  --     = (12c² + 48c³t² + 16c⁴t⁴) exp(c·t²)
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  -- Derivative of (12c²t + 8c³t³).
  have h_lin : HasDerivAt (fun t : ℝ => 12 * c^2 * t)
      (12 * c^2) t := by
    simpa using (hasDerivAt_id t).const_mul (12 * c^2)
  have h_cub : HasDerivAt (fun t : ℝ => 8 * c^3 * t^3)
      (8 * c^3 * (3 * t^2)) t := by
    have := (hasDerivAt_pow 3 t).const_mul (8 * c^3)
    simpa using this
  have h_poly : HasDerivAt (fun t : ℝ => 12 * c^2 * t + 8 * c^3 * t^3)
      (12 * c^2 + 8 * c^3 * (3 * t^2)) t := h_lin.add h_cub
  have h_prod : HasDerivAt
      (fun t : ℝ => (12 * c^2 * t + 8 * c^3 * t^3) * Real.exp (c * t^2))
      ((12 * c^2 + 8 * c^3 * (3 * t^2)) * Real.exp (c * t^2)
        + (12 * c^2 * t + 8 * c^3 * t^3) *
          (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_poly.mul h_exp
  rw [h_prod.deriv]
  ring
/-- **Fourth derivative at 0 is `12c²`.** -/
lemma iteratedDeriv4_exp_quadratic_at_zero' (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (c * t^2)) 0 = 12 * c^2 := by
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_succ, iteratedDeriv_one, deriv4_exp_quadratic]
  simp [Real.exp_zero]
/-- **Connection**: rewrite from MGF to exponential at the function level. -/
lemma mgf_id_gaussianReal_eq_exp_quadratic (v : ℝ≥0) :
    ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v)
      = fun t : ℝ => Real.exp ((v : ℝ) / 2 * t^2) := by
  rw [ProbabilityTheory.mgf_id_gaussianReal]
  funext t
  ring_nf
/-- **MGF at 0**: `mgf id (gaussianReal 0 v) 0 = 1`. (`exp(0) = 1`.) -/
lemma mgf_id_gaussianReal_at_zero (v : ℝ≥0) :
    ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v) 0 = 1 := by
  rw [mgf_id_gaussianReal_eq_exp_quadratic]
  simp [Real.exp_zero]
/-- **Fourth derivative of `t ↦ exp(c · t²)` at `t = 0` is `12 c²`.**

Real direct calculation via 4 successive applications of chain + product rule.
Proved via `iteratedDeriv4_exp_quadratic_at_zero'` below. -/
lemma iteratedDeriv4_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (c * t^2)) 0 = 12 * c^2 :=
  iteratedDeriv4_exp_quadratic_at_zero' c
end LevyStochCalc.Brownian.Continuity


