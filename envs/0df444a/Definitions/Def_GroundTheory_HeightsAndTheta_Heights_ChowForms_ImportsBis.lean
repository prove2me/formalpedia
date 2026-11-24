-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:42:46.955493+00:00
-- url     : https://prove2.me/theorems/33eb6288-eeb8-4f37-ba10-41da792a01b9
-- title:
--   Imports Bis
-- statement:
--   Definitions and structural lemmas for Imports Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/ImportsBis.lean

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
def ChartIncDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      IsDomain (ChartInc I t e) ∧ RingHom.ker (chartX I t e) = I ⊔ Ideal.span {linForm t - 1}
def ChartKernel.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    IsProjPrime I → linForm t ∉ I →
      RingHom.ker (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) = incIdeal I e
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


