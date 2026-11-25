-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelTupleSumEqRational
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelTupleSumEqRational
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:17:34.603656+00:00
-- url     : https://prove2.me/theorems/662bbc9e-a1c8-4941-9307-a2426a9f785c
-- title:
--   Level Tuple Sum Eq Rational
-- statement:
--   Definitions and structural lemmas for Level Tuple Sum Eq Rational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelTupleSumEqRational.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaNA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
namespace GlobalTheory.LevelTupleSum
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def Gen (Λ : Submodule (𝓞 E) (Fin r → E)) (t : Fin r → Fin r → E) : Prop :=
  (∀ j, (25 : E) • t j ∈ Λ) ∧
    ∀ u ∈ Λ, ∃ c : Fin r → 𝓞 E, ∃ y ∈ Λ, u = ∑ j, (c j : E) • ((25 : E) • t j) + (5 : E) • y
end GlobalTheory.LevelTupleSum


