-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:15.22264+00:00
-- url     : https://prove2.me/theorems/405a89f8-a97a-4869-b334-97e2982158e3
-- title:
--   PChart Norm
-- statement:
--   Definitions and structural lemmas for PChart Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartNorm.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormOfDividedForm
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
section Chart
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]
end Chart
end
end GroundTheory.Heights₂.Heights


