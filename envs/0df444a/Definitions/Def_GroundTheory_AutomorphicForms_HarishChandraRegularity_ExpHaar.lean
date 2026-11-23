-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
-- name    : GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:28.337479+00:00
-- url     : https://prove2.me/theorems/26af10fb-518f-4c7d-ba37-3eac1699ed9f
-- title:
--   Exp Haar
-- statement:
--   Definitions and structural lemmas for Exp Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/ExpHaar.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ContDiffCompCoordEquiv
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open MeasureTheory Metric Set Filter
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
end IsExpLieAlgebra
end GroundTheory.Automorphic


