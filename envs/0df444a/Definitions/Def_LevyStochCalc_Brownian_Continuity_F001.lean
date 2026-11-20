-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_Continuity_F001
-- name    : LevyStochCalc_Brownian_Continuity_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:27:59.852177+00:00
-- url     : https://prove2.me/theorems/2e7ccc69-bdec-4840-9c9e-7f4549f62d46
-- title:
--   Source declarations: LevyStochCalc.Brownian.Continuity
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.Continuity. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001
import Definitions.Def_SourceProof_30c2a27da1025349f8d2b70b

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

/-- **Brownian increment fourth moment.** For a process `X` with Brownian-law
increments, `𝔼[(X_t − X_s)⁴] = 3 (t − s)²` for `s < t`. -/
lemma brownian_increment_fourth_moment
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩)
    {s t : ℝ} (hst : s < t) :
    ∫ ω, (X t ω - X s ω) ^ 4 ∂P = 3 * (t - s) ^ 2 := by
  -- Push to the pushforward measure via integral_map.
  have h_meas_diff : Measurable (fun ω => X t ω - X s ω) :=
    (h_meas t).sub (h_meas s)
  rw [show ∫ ω, (X t ω - X s ω) ^ 4 ∂P
        = ∫ x, x ^ 4 ∂(P.map (fun ω => X t ω - X s ω)) from
    (MeasureTheory.integral_map h_meas_diff.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 4) _)).symm]
  rw [h_increment hst]
  -- Goal: ∫ x, x^4 ∂(gaussianReal 0 ⟨t-s, _⟩) = 3 * (t-s)^2.
  have h := _root_.Prove2MeSourceProof.h_30c2a27da1025349f8d2b70b ⟨t - s, by linarith⟩
  exact h
end LevyStochCalc.Brownian.Continuity


