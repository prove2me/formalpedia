-- Prove2me | Definitions.Def_QuinticLienard
-- name    : QuinticLienard
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:13.57858+00:00
-- url     : https://prove2.me/theorems/425726f1-73aa-4cdd-8c2f-e691e54bb70c
-- statement:
--   The block works with planar systems of Liénard type defined by a real polynomial F. Plane is ℝ×ℝ, and vectorField(F) sends a point z=(x,y) to (y−F(x), −x), so the system is x'=y−F(x), y'=−x. IsSolution(F,z) says that a curve z:ℝ→ℝ×ℝ has derivative vectorField(F)(z(t)) at every real time t. IsPeriodicOrbit(F,C) says that a set C of the plane is the range of some solution z for which there is a period T>0 with z(t+T)=z(t) for all t and z is not constant (there exist times s and t with z(s)≠z(t)). IsLimitCycle(F,C) says that C is such a periodic orbit and that there is an open set U containing C such that every periodic orbit of the system contained in U equals C, so C is isolated among periodic orbits. These are definitions only; no bound on the degree of F or on the number of limit cycles is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/QuinticLienard.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/QuinticLienard.lean; bytes 16..1098
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace QuinticLienard

abbrev Plane := ℝ × ℝ

def vectorField (F : Polynomial ℝ) (z : Plane) : Plane :=
  (z.2 - F.eval z.1, -z.1)

def IsSolution (F : Polynomial ℝ) (z : ℝ → Plane) : Prop :=
  ∀ t : ℝ, HasDerivAt z (vectorField F (z t)) t

def IsPeriodicOrbit (F : Polynomial ℝ) (C : Set Plane) : Prop :=
  ∃ (z : ℝ → Plane) (T : ℝ),
    IsSolution F z ∧ 0 < T ∧ Function.Periodic z T ∧
    (∃ s t : ℝ, z s ≠ z t) ∧ C = Set.range z

def IsLimitCycle (F : Polynomial ℝ) (C : Set Plane) : Prop :=
  IsPeriodicOrbit F C ∧
    ∃ U : Set Plane, IsOpen U ∧ C ⊆ U ∧
      ∀ C' : Set Plane, IsPeriodicOrbit F C' → C' ⊆ U → C' = C

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal



end QuinticLienard
end OAI


