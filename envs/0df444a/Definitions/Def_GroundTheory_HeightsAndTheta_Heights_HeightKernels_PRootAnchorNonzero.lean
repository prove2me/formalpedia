-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootAnchorNonzero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:59.188733+00:00
-- url     : https://prove2.me/theorems/c5197a82-3a63-4d16-a5d4-624387b05722
-- title:
--   PRoot Anchor Nonzero
-- statement:
--   Definitions and structural lemmas for PRoot Anchor Nonzero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootAnchorNonzero.lean

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
namespace RootAnchorNonzeroAlt
def homForm {f j m : ℕ} (q : Polynomial ℤ) (τ : Fin f) (I : PlIdx j m) : MRing (plBlocks f j m) :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    C (q.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (q.natDegree - k)
end RootAnchorNonzeroAlt
end
end GroundTheory.Heights₂.Heights


