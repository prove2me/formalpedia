-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualContinuity_ContinuousReTupSymm
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualContinuity_ContinuousReTupSymm
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:56:16.384579+00:00
-- url     : https://prove2.me/theorems/5e998a46-1aaa-4c65-b899-db83bc32d7c7
-- title:
--   Continuous Re Tup Symm
-- statement:
--   Definitions and structural lemmas for Continuous Re Tup Symm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualContinuity/ContinuousReTupSymm.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualBridge
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_AdditiveCharacterNontrivial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdDual
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace PI.SelfDualBridge.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain
open PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.Sd PI.OmFibreUniq.W.SdAbs
open PI.VolStabSW PI.VolStabSW.SdUniqW PI.VolStabSW.SdDualW PI.AdicCompletionValuation
open scoped TensorProduct
section Transport
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
end Transport
section Third
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
def trP (ι : Type) [Fintype ι] (x y : ι → Fv F v ⊗[F] E) : Fv F v :=
  ∑ i, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x i * y i)
def reTup (ι : Type) [Fintype ι] :
    (ι → Fv F v ⊗[F] E) ≃+ (Fin (Fintype.card ι) → Fin 1 → Fv F v ⊗[F] E) where
  toFun x p _ := x ((Fintype.equivFin ι).symm p)
  invFun X i := X (Fintype.equivFin ι i) 0
  left_inv x := by funext i; simp
  right_inv X := by
    funext p k
    rw [Subsingleton.elim k 0]
    simp
  map_add' _ _ := rfl
end Third
end PI.SelfDualBridge.W


