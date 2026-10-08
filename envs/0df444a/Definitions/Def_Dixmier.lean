-- Prove2me | Definitions.Def_Dixmier
-- name    : Dixmier
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.323415+00:00
-- url     : https://prove2.me/theorems/640ab6fc-53af-4009-bc64-49d7a67de878
-- statement:
--   For a discrete group G, left translation of a bounded complex-valued function f by g is the function x ↦ f(g⁻¹x). The defined proposition Amenable(G) asserts the existence of a complex-linear functional m on bounded continuous complex-valued functions on G that sends the constant function 1 to 1, sends every pointwise nonnegative real-valued function to a nonnegative real number, and is invariant under every left translation. For a representation π of a group G by bounded complex-linear operators on a complex inner-product space H, SimilarToUnitary(π) means that there is an invertible bounded complex-linear operator S with bounded inverse such that ‖Sπ(g)S⁻¹x‖ = ‖x‖ for every g ∈ G and x ∈ H. NonamenableWitness(G) is the proposition that there exists a separable complete complex Hilbert space H and such a representation π with operator norm ‖π(g)‖ ≤ 101 for every g, but with no S satisfying this norm-preservation condition. This witness definition itself imposes no nonamenability assumption on G. Finally, MainTheorem is the defined proposition that every countable discrete group failing Amenable(G) has a NonamenableWitness(G), with the witness space taken in the specified universe; it is not an established theorem in this block.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/Dixmier.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/Dixmier.lean; bytes 149..1813
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete

namespace OAI

noncomputable section
universe u v
namespace Dixmier
open scoped BoundedContinuousFunction

def leftTranslate {G : Type u} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] (g : G) (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  f.compContinuous ⟨fun x => g⁻¹ * x, continuous_of_discreteTopology⟩

/-- A positive normalized left-invariant complex mean. -/
def Amenable (G : Type u) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : Prop :=
  ∃ m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ,
    m (BoundedContinuousFunction.const G 1) = 1 ∧
    (∀ f : G →ᵇ ℂ, (∀ x, 0 ≤ (f x).re ∧ (f x).im = 0) →
      0 ≤ (m f).re ∧ (m f).im = 0) ∧
    ∀ (g : G) (f : G →ᵇ ℂ), m (leftTranslate g f) = m f

def SimilarToUnitary {G : Type u} [Group G]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : G →* (H →L[ℂ] H)) : Prop :=
  ∃ S : H ≃L[ℂ] H, ∀ (g : G) (x : H), ‖S (π g (S.symm x))‖ = ‖x‖

/-- A uniformly 101-bounded nonunitarizable representation on a separable
complete complex Hilbert space, with its universe explicit. -/
def NonamenableWitness (G : Type u) [Group G] : Prop :=
  ∃ (H : Type v) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
    (π : G →* (H →L[ℂ] H)),
    (∀ g : G, ‖π g‖ ≤ 101) ∧ ¬ SimilarToUnitary π

/-- Every countable discrete nonamenable group has a bounded nonunitarizable witness. -/
def MainTheorem : Prop :=
  ∀ (G : Type u) [Group G] [Countable G] [TopologicalSpace G]
    [DiscreteTopology G], ¬ Amenable G → NonamenableWitness.{u, v} G



end Dixmier
end
end OAI


