-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExOm
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:37.662316+00:00
-- url     : https://prove2.me/theorems/c50c7fea-33f5-48d0-9e4b-63bb1918a692
-- title:
--   Cay Dens Ex Om
-- statement:
--   Definitions and structural lemmas for Cay Dens Ex Om, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExOm.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
section Lie
variable (P Q : ℕ)
theorem isClosed_lieU : IsClosed ((lieU P Q : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))) := by
  change IsClosed {X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ | Xᴴ * HcS.UG.Jpq P Q + HcS.UG.Jpq P Q * X = 0}
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).add
      (continuous_const.matrix_mul continuous_id)) continuous_const
instance : BorelSpace (lieU P Q) := ⟨rfl⟩
instance : LocallyCompactSpace (lieU P Q) := by
  haveI : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact (isClosed_lieU P Q).isClosedEmbedding_subtypeVal.locallyCompactSpace
instance : SecondCountableTopology (lieU P Q) := by
  haveI : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact IsInducing.subtypeVal.secondCountableTopology
end Lie
end HcInf


