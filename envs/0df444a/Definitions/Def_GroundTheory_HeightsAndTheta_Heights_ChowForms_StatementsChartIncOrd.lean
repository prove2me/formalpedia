-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:26.179747+00:00
-- url     : https://prove2.me/theorems/9e003910-8237-4db4-a2d2-f6b312d0d534
-- title:
--   Statements Chart Inc Ord
-- statement:
--   Definitions and structural lemmas for Statements Chart Inc Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartIncOrd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
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
def ChartIncOrd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
    [(W.map (chartX I t e)).IsPrime]
    [(W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))).IsPrime]
    (x : MvPolynomial (Fin n) F),
    Ring.ord (Localization.AtPrime (W.map (chartX I t e)))
        (algebraMap (ChartInc I t e) _ (chartX I t e x)) =
      Ring.ord (Localization.AtPrime (W.map (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}))))
        (algebraMap _ _ (Ideal.Quotient.mk (I ⊔ Ideal.span {linForm t - 1}) x))
section Inhabitants
def evalPtLine : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℚ := aeval ![0, 1]
def evalIncLine : MvPolynomial (Fin 2 ⊕ Fin 1 × Fin 2) ℚ →ₐ[ℚ] MvPolynomial (Fin 1 × Fin 2) ℚ :=
  aeval (Sum.elim ![0, 1] fun ij => if ij.2 = 0 then X ij else 0)
end Inhabitants
end
end GroundTheory.Heights₂.Heights


