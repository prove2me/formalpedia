-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:52:07.462045+00:00
-- url     : https://prove2.me/theorems/ad4596ed-50a7-46bc-892c-4b8d3ab2a100
-- title:
--   Tors Vals Finite
-- statement:
--   Definitions and structural lemmas for Tors Vals Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/TorsValsFinite.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
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
open Polynomial Formalism.L2.Th1.F
def rsHom (M : IntermediateField ℚ ℂ) (E : IntermediateField M ℂ) (σ : E →ₐ[M] ℂ) :
    E.restrictScalars ℚ →ₐ[ℚ] ℂ :=
  RingHom.toRatAlgHom
    { toFun := fun z => σ ⟨z, z.2⟩
      map_one' := σ.map_one
      map_mul' := fun a b => σ.map_mul ⟨a, a.2⟩ ⟨b, b.2⟩
      map_zero' := σ.map_zero
      map_add' := fun a b => σ.map_add ⟨a, a.2⟩ ⟨b, b.2⟩ }
end PI.GalTorsConj.W
end


