-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_IsCompactDbox
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_IsCompactDbox
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:52.465732+00:00
-- url     : https://prove2.me/theorems/7a45ddd0-6971-458a-b668-75ae62435885
-- title:
--   Is Compact Dbox
-- statement:
--   Definitions and structural lemmas for Is Compact Dbox, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/IsCompactDbox.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_DiagonalPhaseFirstVector
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
section Scale
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
end Scale
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)
def Mk (ι : Type) (k : ℕ) : AddSubgroup (ι → Fv F v ⊗[F] E) :=
  (ObS (E := E) v ι).comap (DistribSMul.toAddMonoidHom (ι → Fv F v ⊗[F] E) (piu v ^ k))
variable (hK : OpenKer v ψ) (hnt : ∃ r, psiV F ψ v r ≠ 1)
include hK hnt
end PI.UnitaryGroupMassFormula.LocJacTyp.Sd


