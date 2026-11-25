-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
-- name    : GroundTheory_AutomorphicForms_DixmierMalliavin
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:59:21.060802+00:00
-- url     : https://prove2.me/theorems/47d4abc9-6a13-4940-b419-e8493dfb6b00
-- title:
--   Dixmier Malliavin
-- statement:
--   Definitions and structural lemmas for Dixmier Malliavin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavin.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinSeries
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinProducts
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarDensity
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeAlgebra
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
open NormedSpace Set MeasureTheory
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
end IsExpLieAlgebra
end GroundTheory.Automorphic


