-- Prove2me | Definitions.Def_TorsionFreeZeroDivisors
-- name    : TorsionFreeZeroDivisors
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:32.723173+00:00
-- url     : https://prove2.me/theorems/96ddda74-0b9e-4a29-b5e9-a26a917a94ec
-- statement:
--   TorsionFree(G) is the ordinary group-theoretic torsion-freeness of a group G: for every g in G and every positive integer n, g^n = 1 implies g = 1; it does not demand uniqueness of roots. HasFiniteTwoDimensionalClassifyingSpace(G) asserts the existence of a Hausdorff, path-connected topological space X carrying a CW complex structure on the whole space that is finite, has no cells in any dimension above 2, and has at least one 2-cell, together with a basepoint x such that G is isomorphic as a group to the fundamental group of X at x, and a contractible space E with a surjective covering map p : E → X. This is the stated formalization of a connected finite Hausdorff 2-dimensional CW model of K(G,1). MainTheorem is a defined proposition, not an established theorem, asserting the existence of a group G that is finitely presented, torsion-free, and has such a finite 2-dimensional classifying space, and for which the group algebra of G over the field ZMod 2 (two elements) contains nonzero elements α and β with α·β = 0, that is, the group algebra has zero divisors. The source docstring says it includes the "Moreover" clause of the main theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TorsionFreeZeroDivisors.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TorsionFreeZeroDivisors.lean; bytes 16..1461
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace TorsionFreeZeroDivisors

/-- Ordinary group torsion-freeness, without requiring uniqueness of all roots. -/
def TorsionFree (G : Type) [Group G] : Prop :=
  ∀ (g : G) (n : ℕ), 0 < n → g ^ n = 1 → g = 1

/-- A connected finite Hausdorff 2-dimensional CW K(G,1). -/
def HasFiniteTwoDimensionalClassifyingSpace (G : Type) [Group G] : Prop :=
  ∃ (X : Type) (topX : TopologicalSpace X),
    letI : TopologicalSpace X := topX
    ∃ (_hausdorff : T2Space X) (_connected : PathConnectedSpace X)
      (cw : Topology.CWComplex (Set.univ : Set X)),
      letI : Topology.CWComplex (Set.univ : Set X) := cw
      Topology.CWComplex.Finite (Set.univ : Set X) ∧
      (∀ n : ℕ, 2 < n → IsEmpty (Topology.CWComplex.cell (Set.univ : Set X) n)) ∧
      Nonempty (Topology.CWComplex.cell (Set.univ : Set X) 2) ∧
      ∃ (x : X), Nonempty (G ≃* FundamentalGroup X x) ∧
        ∃ (E : Type) (topE : TopologicalSpace E),
          letI : TopologicalSpace E := topE
          ContractibleSpace E ∧
          ∃ p : E → X, IsCoveringMap p ∧ Function.Surjective p

/-- The entire main theorem, including its "Moreover" clause. -/
def MainTheorem : Prop :=
  ∃ (G : Type) (inst : Group G),
    letI : Group G := inst
    Group.IsFinitelyPresented G ∧ TorsionFree G ∧
    HasFiniteTwoDimensionalClassifyingSpace G ∧
    ∃ α β : MonoidAlgebra (ZMod 2) G, α ≠ 0 ∧ β ≠ 0 ∧ α * β = 0



end TorsionFreeZeroDivisors
end OAI


