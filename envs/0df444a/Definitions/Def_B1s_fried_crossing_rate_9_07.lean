-- Prove2me | Definitions.Def_B1s_fried_crossing_rate_9_07
-- name    : B1s_fried_crossing_rate_9_07
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:38:12.313837+00:00
-- url     : https://prove2.me/theorems/c5dd89ce-38c6-4450-a3ec-8b8d3c052b6e
-- title:
--   fried crossing rate 9 07
-- statement:
--   Definitions and structural lemmas for fried crossing rate 9 07, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_rate_9_07.lean

import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology
namespace TwinRate
def clusterTrace (sStar τ a : ℝ) : ℝ := 2 * sStar + τ * a
def clusterDet (sStar τ a b : ℝ) : ℝ := sStar ^ 2 + sStar * τ * a + τ ^ 2 * b
end TwinRate
namespace Crossing
end Crossing
namespace RateRatio
end RateRatio
namespace Capstone
open TorsionCore OrderCount Crossing RateRatio TwinRate
end Capstone
namespace Saturation
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
end Saturation
end FriedCrossing


