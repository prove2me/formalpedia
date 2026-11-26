-- Prove2me | Definitions.Def_B1s_cluster_from_resolvent_9_11
-- name    : B1s_cluster_from_resolvent_9_11
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:40:41.966262+00:00
-- url     : https://prove2.me/theorems/a47c409e-4022-4bbc-b1fc-08dd6a4fae2f
-- title:
--   cluster from resolvent 9 11
-- statement:
--   Definitions and structural lemmas for cluster from resolvent 9 11, from Ben Lawton (blawton/fried-conj-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Resonance-cluster conditional reduction for a proposed counterexample to Fried's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/cluster_from_resolvent_9_11.lean

import Definitions.Def_B1s_resolvent_scale_9_11
import Definitions.Def_B1s_fried_cluster_matrices_9_10
set_option autoImplicit true
set_option linter.style.header false
namespace FriedCrossing
open Filter Topology ContinuousLinearMap MeasureTheory intervalIntegral Scale
namespace ParamInt
noncomputable def partialX {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (F : E → ℝ → G) (x : E) (t : ℝ) : E →L[ℝ] G :=
  (fderiv ℝ (Function.uncurry F) (x, t)).comp (inl ℝ E ℝ)
end ParamInt
namespace ClusterFrame
open ParamInt
variable {S : BanachScale.{0}} (F : ResolventFamily S Param) (Jc : ComplexStructure S)
variable {k : ℕ}
end ClusterFrame
end FriedCrossing


