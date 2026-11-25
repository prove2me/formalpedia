-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ComponentsOfD1EqZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ComponentsOfD1EqZero
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:01.048956+00:00
-- url     : https://prove2.me/theorems/0de62527-3b9e-4270-b523-a590d9c57b5d
-- title:
--   Components Of D1 Eq Zero
-- statement:
--   Definitions and structural lemmas for Components Of D1 Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ComponentsOfD1EqZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ChiZeroRight
import Theorems.Thm_PI_VolStabSW_locallyCompact_Fv
import Theorems.Thm_PI_VolStabSW_secondCountable_Fv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)
variable [SecondCountableTopology (Fv F v ⊗[F] E)]
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd


