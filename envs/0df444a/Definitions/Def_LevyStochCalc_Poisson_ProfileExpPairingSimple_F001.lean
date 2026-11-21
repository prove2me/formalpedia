-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairingSimple_F001
-- name    : LevyStochCalc_Poisson_ProfileExpPairingSimple_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:25:36.116589+00:00
-- url     : https://prove2.me/theorems/31e1ec38-3b52-4df9-8a64-864aa2e725d3
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileExpPairingSimple
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileExpPairingSimple. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedCountCharacter_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedProduct_F001
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F000
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F001
import Definitions.Def_LevyStochCalc_Probability_CharacterL2_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated step integral against first- and second-order elements

For a simple mark profile with pairwise disjoint mark sets `B_k` of finite intensity, the
compensated counts `Ñ_k` of the strips `(a, b] × B_k` are independent, so the character
`e^{iuJ_c}` of the compensated step integral `J_c = ∑_k c_k Ñ_k` carried by a coefficient vector
`c` factors over the strips. Each factor pairs with `Ñ_k` and `Ñ_k²` through the identities of
`Poisson/CompensatedCountCharacter.lean`, with `λ_k = (b − a) ν(B_k)`:
`E[e^{isÑ} Ñ] = λ (e^{is} − 1) E[e^{isÑ}]` and
`E[e^{isÑ} Ñ²] = (λ² (e^{is} − 1)² + λ e^{is}) E[e^{isÑ}]`. Summing over the strips gives, for
coefficient vectors `d, d'` on the same mark sets and `γ_k = e^{iuc_k} − 1`,

  `E[e^{iuJ_c} J_d] = (b − a) ∑_k ν(B_k) γ_k d_k · E[e^{iuJ_c}]`,

and the matching second-order identity for `E[e^{iuJ_c} J_d J_{d'}]`. On a common refinement of
finitely many simple profiles these become the pairings of the character of the compensated
integral of one simple profile `G` with the compensated integrals of others, with
`γ = e^{iuG} − 1`:

  `E[e^{iuJ(G)} J(F)] = (b − a) ∫ γ F dν · E[e^{iuJ(G)}]`,
  `E[e^{iuJ(G)} J(F) J(K)]`
  `  = ((b − a)² ∫ γ F dν ∫ γ K dν + (b − a) (∫ γ F K dν + ∫ F K dν)) · E[e^{iuJ(G)}]`.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral_mul_stepIntegral_mul` —
  the first- and second-order pairings on the mark sets of one simple profile.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_compensatedProfile_mul_mul` — the
  first- and second-order pairings at simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.abs_toFun_le` — the function of a simple profile is bounded
  by the sum of the absolute values of its coefficients.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Strips of a simple profile -/

namespace SimpleProfile

/-! ### Pairings on the mark sets of one simple profile -/

/-! ### Simple mark profiles -/

omit [SigmaFinite ν] in
/-- The function of a simple profile is bounded by the sum of the absolute values of its
coefficients. -/
theorem abs_toFun_le (K : SimpleProfile E ν) (e : E) : |K.toFun e| ≤ ∑ k, |K.c k| := by
  rw [SimpleProfile.toFun]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  refine mul_le_of_le_one_right (abs_nonneg _) ?_
  by_cases hk : e ∈ K.B k <;> simp [hk]
end SimpleProfile

end LevyStochCalc.Poisson


