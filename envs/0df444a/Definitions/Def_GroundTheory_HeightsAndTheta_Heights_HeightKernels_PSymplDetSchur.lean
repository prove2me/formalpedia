-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetSchur
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplDetSchur
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:13.918499+00:00
-- url     : https://prove2.me/theorems/4c126f95-732f-47ec-9ba2-5d6838be14e1
-- title:
--   PSympl Det Schur
-- statement:
--   Definitions and structural lemmas for PSympl Det Schur, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PSymplDetSchur.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
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
open Matrix
namespace PSymplDetSchur
noncomputable def clearCol {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if j = 0 then -A i 0 / A 0 0 else 0
end PSymplDetSchur
end GroundTheory.Heights₂.Heights


