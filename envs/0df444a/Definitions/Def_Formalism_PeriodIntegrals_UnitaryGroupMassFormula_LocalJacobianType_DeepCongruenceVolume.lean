-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_DeepCongruenceVolume
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_DeepCongruenceVolume
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:56.485235+00:00
-- url     : https://prove2.me/theorems/e45616d1-7fc1-5a0f-84e2-79cd0f9a960d
-- title:
--   Deep Congruence Volume
-- statement:
--   Definitions and structural lemmas for Deep Congruence Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/DeepCongruenceVolume.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitScale
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_locallyCompact_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_BM_secondCountable_Fv
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_SD_ext
import Theorems.Thm_PI_VolStabSW_HasDens_sub
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
namespace PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct
attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
attribute [local instance] Sd.finDim
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))
def shearU (ι : Type) :
    ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) ≃ₜ+ ((ι → Fv F v ⊗[F] E) × (ι → Fv F v ⊗[F] E)) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := Prod.ext rfl (by
    show x.1 + y.1 - (x.2 + y.2) = (x.1 - x.2) + (y.1 - y.2)
    abel)
  continuous_toFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
  continuous_invFun := continuous_fst.prodMk (continuous_fst.sub continuous_snd)
end PI.UnitaryGroupMassFormula.LocJacTyp


