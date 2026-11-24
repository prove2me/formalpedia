-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnEvalMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:24.384712+00:00
-- url     : https://prove2.me/theorems/691a8199-efa2-4fcb-874b-785e7bcb8141
-- title:
--   Qn Eval Map
-- statement:
--   Definitions and structural lemmas for Qn Eval Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QnEvalMap.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnFactRowDivDiag
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnPtEmpty
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_CoeffTransposeVariables
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QnInterlacedLowerTri
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
def qn_InZ (n : ℕ) (ν : Fin n → ℕ) (x : MvPolynomial (Fin n × Fin n) ℚ) : Prop :=
  ∃ Y ∈ dualWeyl ℤ n n ν, transposeVariables ℚ n x = map (Int.castRingHom ℚ) Y
end Formalism.InvariantFactorPaths.ColumnFamilies


