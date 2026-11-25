-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitSplit
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:57.443325+00:00
-- url     : https://prove2.me/theorems/7bc0e510-6433-4f10-aad8-52d93647a121
-- title:
--   Kit Split
-- statement:
--   Definitions and structural lemmas for Kit Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/KitSplit.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_RingTopologyInstances
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_EpSelfDualSplit
import Definitions.Def_Formalism_PeriodIntegrals_SplitIntLoc
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SplitIntLoc
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_oev_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_oev_one
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
structure SD where
  e : Fv F v ⊗[F] E
  he : IsIdempotentElem e
  h0 : e ≠ 0
  h1 : e ≠ 1
  hr : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2
  hσ : sigR (Fv F v) σ e = 1 - e
namespace SD
variable {σ v} (D : SD σ v)
def p (i : Fin 2) : (Fv F v ⊗[F] E) →ₐ[Fv F v] Fv F v := PI.LocDualGen.EpS.pr D.hr D.e D.he D.h0 D.h1 i
end SD
def oevSub : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := fun hx hy => oev_mul v hx hy
  one_mem' := oev_one v
  add_mem' := fun hx hy => Sd.oev_add v hx hy
  zero_mem' := Sd.oev_zero v
  neg_mem' := fun hx => Sd.oev_neg v hx
variable {σ v}
namespace SD
variable (D : SD σ v)
end SD
end PI.UnitaryGroupMassFormula.LocJacTyp


