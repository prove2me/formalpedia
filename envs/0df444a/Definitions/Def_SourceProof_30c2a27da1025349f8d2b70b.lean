-- Prove2me | Definitions.Def_SourceProof_30c2a27da1025349f8d2b70b
-- name    : SourceProof_30c2a27da1025349f8d2b70b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:27:37.851788+00:00
-- url     : https://prove2.me/theorems/c8057497-b545-48c0-9a44-d1bcdca6d586
-- title:
--   LevyStochCalc source module: SourceProof_30c2a27da1025349f8d2b70b
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Continuity.gaussianReal_fourth_moment` comes from the `LevyStochCalc.Brownian.Continuity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_Continuity_F000

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


theorem _root_.Prove2MeSourceProof.h_30c2a27da1025349f8d2b70b (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂(ProbabilityTheory.gaussianReal 0 v) = 3 * (v : ℝ)^2 := by
  -- Step 1: ∫ x^4 = iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0
  have h_int := LevyStochCalc.Brownian.Continuity.zero_mem_interior_integrableExpSet_gaussianReal v
  have h_mgf_deriv :=
    ProbabilityTheory.iteratedDeriv_mgf_zero (X := id)
      (μ := ProbabilityTheory.gaussianReal 0 v) h_int 4
  -- h_mgf_deriv : iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0 = μ[id^4]
  -- where μ[id^4] = ∫ x, id x ^ 4 ∂μ = ∫ x, x^4 ∂μ.
  -- Step 2: rewrite mgf using mgf_id_gaussianReal
  have h_mgf : ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v)
      = fun t => Real.exp ((v : ℝ) * t^2 / 2) := by
    rw [ProbabilityTheory.mgf_id_gaussianReal]
    funext t; ring_nf
  -- Step 3: equality of the two functions at the iteratedDeriv level
  have h_funeq : (fun t : ℝ => Real.exp ((v : ℝ) * t^2 / 2))
      = (fun t : ℝ => Real.exp (((v : ℝ) / 2) * t^2)) := by
    funext t; ring_nf
  -- Step 4: apply iteratedDeriv4_exp_quadratic_at_zero with c = v/2
  have h4 := LevyStochCalc.Brownian.Continuity.iteratedDeriv4_exp_quadratic_at_zero ((v : ℝ) / 2)
  -- h4 : iteratedDeriv 4 (fun t => exp((v/2) * t^2)) 0 = 12 * (v/2)^2
  -- Combine
  rw [show ∫ x, x^4 ∂(ProbabilityTheory.gaussianReal 0 v)
      = (ProbabilityTheory.gaussianReal 0 v)[id^4] from by
        simp [Pi.pow_apply]]
  rw [← h_mgf_deriv, h_mgf, h_funeq, h4]
  ring
end LevyStochCalc.Brownian.Continuity


