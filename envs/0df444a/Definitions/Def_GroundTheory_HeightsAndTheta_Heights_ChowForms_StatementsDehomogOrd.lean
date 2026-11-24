-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsDehomogOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:46:42.054674+00:00
-- url     : https://prove2.me/theorems/38cd7637-de11-423e-a4a8-7f6252ae1e7f
-- title:
--   Statements Dehomog Ord
-- statement:
--   Definitions and structural lemmas for Statements Dehomog Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsDehomogOrd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def DehomogOrd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsHomogIdeal I → IsHomogIdeal W → I ≤ W → linForm t ∉ W →
    ∀ [(W.map (Ideal.Quotient.mk I)).IsPrime]
      [(W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime]
      (g : MvPolynomial (Fin n) F) (d : ℕ), g.IsHomogeneous d →
      Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk I)))
          (algebraMap _ _ (Ideal.Quotient.mk I g)) =
        Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
          (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) g))
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


