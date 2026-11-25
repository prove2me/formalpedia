-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DixmierMalliavin_DecompDirection
-- name    : Development_WeilBound_CoreStatements_AbelianHeightsDuality_DixmierMalliavin_DecompDirection
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:48.607251+00:00
-- url     : https://prove2.me/theorems/09199059-3daa-4b18-a03c-0c67293e0419
-- title:
--   Decomp Direction
-- statement:
--   Definitions and structural lemmas for Decomp Direction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/DixmierMalliavin/DecompDirection.lean

import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PositivityTheory.DM
open GroundTheory.Automorphic GroundTheory.Automorphic.IsExpLieAlgebra
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Metric
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
end PositivityTheory.DM


