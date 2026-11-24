-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_TcoordBound
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:40:17.646333+00:00
-- url     : https://prove2.me/theorems/089dcb7e-9b77-4bcd-8668-587c8091b57e
-- title:
--   Tcoord Bound
-- statement:
--   Definitions and structural lemmas for Tcoord Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryClassMass/TcoordBound.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_PHermT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UJClassMass Formalism.HermitianLatticesTheory IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.UnitaryGroupMassFormula.UJClassMass
namespace HX
section T
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def tensA (t : HeightOneSpectrum (𝓞 F)) : AddSubgroup (E ⊗[F] t.adicCompletion F) :=
  AddSubgroup.closure {w | ∃ x ∈ PI.UnitaryApproxDefs.intOE E, ∃ y ∈ t.adicCompletionIntegers F, w = x ⊗ₜ[F] y}
end T
end HX
end PI.UnitaryGroupMassFormula.UJClassMass
end


