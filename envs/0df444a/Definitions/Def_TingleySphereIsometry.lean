-- Prove2me | Definitions.Def_TingleySphereIsometry
-- name    : TingleySphereIsometry
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:32.358001+00:00
-- url     : https://prove2.me/theorems/c1dda11f-e501-452a-b496-8f7015f1a61a
-- statement:
--   The block fixes a real normed space X (and a second one Y, declared but unused here) and defines UnitSphere(X) as the type of vectors x in X with norm exactly 1, viewed as a subtype of X. It then defines normalize(x, hx), which takes a vector x together with a proof hx that x is nonzero and returns the point of the unit sphere obtained by scaling x by the reciprocal of its norm, ‖x‖⁻¹ • x; the proof that this vector has norm 1 is supplied by the Mathlib lemma norm_smul_inv_norm. No isometry statement is made in this block, only the sphere and the normalization map.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TingleySphereIsometry.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TingleySphereIsometry.lean; bytes 97..495
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Topology.MetricSpace.Isometry

namespace OAI

noncomputable section

namespace Tingley

universe u v

abbrev UnitSphere (X : Type u) [NormedAddCommGroup X] := {x : X // ‖x‖ = 1}

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def normalize (x : X) (hx : x ≠ 0) : UnitSphere X :=
  ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx⟩



end Tingley
end
end OAI


