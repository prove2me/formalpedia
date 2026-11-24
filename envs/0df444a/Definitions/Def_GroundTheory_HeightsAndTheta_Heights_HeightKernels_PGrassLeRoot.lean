-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:11:19.527225+00:00
-- url     : https://prove2.me/theorems/7a4368fb-d132-4f52-9ced-bc79512f2ab8
-- title:
--   PGrass Le Root
-- statement:
--   Definitions and structural lemmas for PGrass Le Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassLeRoot.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
namespace GrassmannianRootBound
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def cone {R : Type*} [CommRing R] (y : (Σ k, ι k) → R) : MRing ι →ₐ[ℤ] MvPolynomial K R :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1
end GrassmannianRootBound
end
end GroundTheory.Heights₂.Heights


