-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeIsLattice
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGaussLatticeIsLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:39.287969+00:00
-- url     : https://prove2.me/theorems/5570bc29-088c-4f83-916f-e715967ebeb0
-- title:
--   PGauss Lattice Is Lattice
-- statement:
--   Definitions and structural lemmas for PGauss Lattice Is Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGaussLatticeIsLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGauss
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
noncomputable section
namespace PGaussLatticeIsLattice
def colBasis {g : ℕ} (B : Matrix (Fin g) (Fin g) ℝ) (hB : B.det ≠ 0) :
    Module.Basis (Fin g) ℝ (EuclideanSpace ℝ (Fin g)) :=
  (Pi.basisFun ℝ (Fin g)).map
    ((B.toLinearEquiv' (B.invertibleOfIsUnitDet (isUnit_iff_ne_zero.2 hB))).trans
      (WithLp.linearEquiv 2 ℝ (Fin g → ℝ)).symm)
end PGaussLatticeIsLattice
end
end GroundTheory.Heights₂.Heights


