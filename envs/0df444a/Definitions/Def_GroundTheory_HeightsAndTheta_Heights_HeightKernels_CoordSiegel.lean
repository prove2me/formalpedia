-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordSiegel
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordSiegel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:06.730802+00:00
-- url     : https://prove2.me/theorems/1ed2281b-8d6f-4d96-84e7-ed640f9387f1
-- title:
--   Coord Siegel
-- statement:
--   Definitions and structural lemmas for Coord Siegel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/CoordSiegel.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsMatrix
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
namespace KCoord
variable {m n : Type*} [Fintype m] [Fintype n]
end KCoord
variable {g : ℕ}
namespace KCoord
def unip (X : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks 1 X 0 1
noncomputable def diagInv (Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ :=
  fromBlocks Y⁻¹ 0 0 Y
end KCoord
namespace KCoord
end KCoord
end GroundTheory.Heights₂.Heights


