-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
-- name    : GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:30.607558+00:00
-- url     : https://prove2.me/theorems/2ec2b279-4e97-4fa8-8555-f83607f79147
-- title:
--   Det Ineq
-- statement:
--   Definitions and structural lemmas for Det Ineq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MatrixCharts/DetIneq.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.MCDet
open Matrix
open scoped MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
end GroundTheory.Heights₂.Heights.MCDet


