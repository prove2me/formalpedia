-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:56.820624+00:00
-- url     : https://prove2.me/theorems/061a16b6-fdad-419a-b7cb-c7ed19bba923
-- title:
--   Inc Adj Inclusion
-- statement:
--   Definitions and structural lemmas for Inc Adj Inclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/IncAdjInclusion.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_MulDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GalTorsConj.W
open Polynomial
def incAdj (M M₁ : IntermediateField ℚ ℂ) : M₁ →+* IntermediateField.adjoin M (M₁ : Set ℂ) where
  toFun x := ⟨x, IntermediateField.subset_adjoin M _ x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
end PI.GalTorsConj.W
end


