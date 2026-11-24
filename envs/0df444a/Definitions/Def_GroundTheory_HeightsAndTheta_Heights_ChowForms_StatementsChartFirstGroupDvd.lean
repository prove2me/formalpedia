-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:59.669232+00:00
-- url     : https://prove2.me/theorems/81ea52f1-c746-4a67-bbe6-8b6133b07396
-- title:
--   Statements Chart First Group Dvd
-- statement:
--   Definitions and structural lemmas for Statements Chart First Group Dvd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsChartFirstGroupDvd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroup
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
def ChartFirstGroupDvd.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I →
      (∑ m, X m * C (chartX I t e (X m))) ∣
        map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


