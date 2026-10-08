-- Prove2me | Definitions.Def_DixmierAllDiscrete
-- name    : DixmierAllDiscrete
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:08.390457+00:00
-- url     : https://prove2.me/theorems/b01d134b-c6b5-44fa-9378-c83732852769
-- statement:
--   For a discrete topological group G and a bounded complex-valued function f on G, left translation by g is the function x ↦ f(g⁻¹x). Amenable(G) is the proposition that there exists a complex-linear functional m on the bounded continuous complex-valued functions on G which sends the constant function 1 to 1, sends every nonnegative real-valued function to a nonnegative real number, and is invariant under every left translation. For a representation π of a group G by bounded complex-linear operators on a complex inner product space H, SimilarToUnitary(π) means that there exists a bounded complex-linear isomorphism S with bounded inverse such that ‖Sπ(g)S⁻¹x‖ = ‖x‖ for every g in G and x in H. Unitarizable(G) means that every uniformly bounded such representation on any complex Hilbert space is similar to a unitary representation in this sense; uniform boundedness means that one real constant C bounds ‖π(g)‖ for all g. CurrentMainTheorem is a defined proposition asserting that every discrete group G is amenable if and only if it is unitarizable, and additionally that, for every ε > 0, each nonamenable G admits a representation π on a complex Hilbert space H with ‖π(g)‖ ≤ 1 + ε for all g which is not similar to a unitary representation. The latter H must be separable whenever G is countable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DixmierAllDiscrete.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DixmierAllDiscrete.lean; bytes 149..1795
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

def Unitarizable (G : Type u) [Group G] : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : G →* (H →L[ℂ] H)),
    (∃ C : ℝ, ∀ g, ‖π g‖ ≤ C) → SimilarToUnitary π

def CurrentMainTheorem : Prop :=
  ∀ (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G],
    (Amenable G ↔ Unitarizable.{u, max u v} G) ∧
    ∀ (ε : ℝ), 0 < ε → ¬ Amenable G →
      ∃ (H : Type (max u v)) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
        (_ : CompleteSpace H) (π : G →* (H →L[ℂ] H)),
        (Countable G → TopologicalSpace.SeparableSpace H) ∧
        (∀ g, ‖π g‖ ≤ 1 + ε) ∧ ¬ SimilarToUnitary π



end Dixmier
end
end OAI


