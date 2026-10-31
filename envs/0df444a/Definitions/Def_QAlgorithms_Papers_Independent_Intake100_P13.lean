-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13
-- name    : QAlgorithms_Papers_Independent_Intake100_P13
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:08:24.594541+00:00
-- url     : https://prove2.me/theorems/55f9ee1c-3d5c-4012-93df-92d0b9cf2f1e
-- title:
--   Definitions for A complex semigroup approach to group algebras of infinite dimensional Lie groups
-- statement:
--   The objects the formalized statements of *A complex semigroup approach to group algebras of infinite dimensional Lie groups* (arXiv:0709.1062) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `evalInf`: Definition 4.2, PDF pp. 24–25: extended-real infimum of evaluation. The empty set has infimum +infinity and an unbounded-below image has infimum -infinity. The underlying dual consists of continuous functionals.
--   - `boundedBelowDirections`: Definition 4.2, PDF p. 25: the directions with evaluation bounded below, including every direction when the dual set is empty.
--   - `dualPolar`: Lemma 4.5, PDF p. 26: absolute polar for the evaluation pairing, not the positive dual cone denoted by a star in Definition 4.2.
--   - `strictCoordinates`: Definition 2.11, PDF p. 14: coordinates defining the strict topology. Each coordinate records left and right multiplication on a fixed element.
--   - `strictTopology`: Definition 2.11, PDF p. 14: the initial topology for all the left and right norm-evaluation maps. It is the topology defined by the seminorms p_a(m)=norm(ma)+norm(am), with no bounded-subset restriction.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, https://arxiv.org/abs/0709.1062v1

import Mathlib

/-!
Statements from K.-H. Neeb, arXiv:0709.1062v1.
The unavailable semigroup, locally convex Lie, and spectral constructions are
recorded node by node in HARD.md and GAPS.json. No normed-space replacement
for the source's locally convex calculus is made. Compilation is pending.
-/

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

example {V : Type u} [AddCommGroup V] :
    {x : V | ∀ c ∈ ({0} : Set V), c + x ∈ ({0} : Set V)} = {0} := by
  ext x
  simp

section DualGeometry

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- Definition 4.2, PDF pp. 24–25: extended-real infimum of evaluation.
The empty set has infimum +infinity and an unbounded-below image has
infimum -infinity. The underlying dual consists of continuous functionals. -/
def evalInf (C : Set (WeakDual ℝ V)) (x : V) : EReal :=
  sInf ((fun f : WeakDual ℝ V => (f x : EReal)) '' C)

example (x : V) : evalInf (∅ : Set (WeakDual ℝ V)) x = ⊤ := by
  simp [evalInf]

/-- Definition 4.2, PDF p. 25: the directions with evaluation bounded
below, including every direction when the dual set is empty. -/
def boundedBelowDirections (C : Set (WeakDual ℝ V)) : Set V :=
  {x | (⊥ : EReal) < evalInf C x}

example : boundedBelowDirections (∅ : Set (WeakDual ℝ V)) = Set.univ := by
  ext x
  simp [boundedBelowDirections, evalInf]

/-- Lemma 4.5, PDF p. 26: absolute polar for the evaluation pairing,
not the positive dual cone denoted by a star in Definition 4.2. -/
def dualPolar (C : Set (WeakDual ℝ V)) : Set V :=
  {x | ∀ f ∈ C, |f x| ≤ 1}

example : dualPolar (∅ : Set (WeakDual ℝ V)) = Set.univ := by
  ext x
  simp [dualPolar]

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]
variable [LocallyConvexSpace ℝ V] [T2Space V]

end DualGeometry

section Multipliers

variable (A : Type u) [NonUnitalCStarAlgebra A]

/-- Definition 2.11, PDF p. 14: coordinates defining the strict topology.
Each coordinate records left and right multiplication on a fixed element. -/
def strictCoordinates (m : DoubleCentralizer ℂ A) : A → A × A :=
  fun a => (m.fst a, m.snd a)

example : strictCoordinates A (0 : DoubleCentralizer ℂ A) = fun _ => (0, 0) := rfl

/-- Definition 2.11, PDF p. 14: the initial topology for all the left and
right norm-evaluation maps. It is the topology defined by the seminorms
p_a(m)=norm(ma)+norm(am), with no bounded-subset restriction. -/
def strictTopology : TopologicalSpace (DoubleCentralizer ℂ A) :=
  TopologicalSpace.induced (strictCoordinates A) inferInstance

example : strictTopology A =
    TopologicalSpace.induced (fun m : DoubleCentralizer ℂ A =>
      fun a : A => (m.fst a, m.snd a)) inferInstance := rfl

variable {A}

end Multipliers

end

end QAlgorithms.Papers.Independent.Intake100.P13


