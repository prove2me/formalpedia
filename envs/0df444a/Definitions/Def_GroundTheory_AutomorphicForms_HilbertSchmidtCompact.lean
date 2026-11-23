-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
-- name    : GroundTheory_AutomorphicForms_HilbertSchmidtCompact
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:45.84065+00:00
-- url     : https://prove2.me/theorems/c30f847f-e421-4d6b-af1a-40f7e9479352
-- title:
--   Hilbert Schmidt Compact
-- statement:
--   Definitions and structural lemmas for Hilbert Schmidt Compact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
def hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K) (F : Finset ι) :
    H →L[𝕜] K :=
  ∑ i ∈ F, (innerSL 𝕜 (b i)).smulRight (T (b i))
end
end GroundTheory.Automorphic


