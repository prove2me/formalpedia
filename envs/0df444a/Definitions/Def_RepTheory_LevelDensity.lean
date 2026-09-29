-- Prove2me | Definitions.Def_RepTheory_LevelDensity
-- name    : RepTheory_LevelDensity
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/d1aca691-cc59-52ff-adc8-298325709b47
-- title:
--   Level-wise dense action of a test module
-- statement:
--   The module fixes a topological group $G$, complex vector spaces $V$ and $S$, a monoid homomorphism $\pi : G \to \operatorname{End}_{\mathbb C}(V)$ into the multiplicative monoid of complex-linear endomorphisms of $V$ (so $V$ is a representation of $G$ without any continuity, admissibility or smoothness assumption), and a complex-linear map $H : S \to \operatorname{End}_{\mathbb C}(V)$, thought of as the action of a test module $S$ on $V$; note that $S$ carries no multiplication and $H$ is required only to be linear, not multiplicative. In this context the single declaration [`TwistedPairing.IsLevelDenseAction`](../def/RepTheory_LevelDensity.html#L20) is the predicate on $H$ (with $\pi$ an explicit argument) asserting the following: for every subgroup $K \le G$ whose underlying subset of $G$ is both compact and open, for every complex-linear functional $\ell : V \to \mathbb C$ that is $K$-invariant in the sense that $\ell(\pi(k)x) = \ell(x)$ for all $k \in K$ and all $x \in V$, and for every vector $x_0 \in V$ fixed by $K$, i.e. $\pi(k)x_0 = x_0$ for all $k \in K$, there exists $\varphi \in S$ with
--   $$H(\varphi)\,x = \ell(x)\,x_0 \qquad\text{for all } x \in V.$$
--   Thus the predicate demands that every rank-$\le 1$ operator of the shape $x \mapsto \ell(x)x_0$ built from a $K$-invariant functional and a $K$-fixed vector, at every compact open level $K$, be realised exactly (not merely approximated) by the action of a single element of $S$. The quantification is over all compact open subgroups of $G$ simultaneously, which is the sense in which the density is 'level-wise'; no topology on $V$ or $S$ is involved, and the conclusion is an identity of operators on all of $V$.
--
--   **Relation to Mathlib.** Mathlib has no notion of this kind; `IsLevelDenseAction` is the project's own predicate, stated using Mathlib's `Module.End`, `Subgroup`, `IsCompact` and `IsOpen`.
--
--   **Where it is used.** The predicate packages, as a hypothesis usable in later statements, the property of a Hecke-type action of a test module $S$ (for instance locally constant compactly supported functions on a totally disconnected group) on a representation $V$ that is needed to produce the rank-one operators $x \mapsto \ell(x)x_0$ at each compact open level. It is consumed by three statement modules of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_LevelDensity.lean

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Compactness.Compact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace TwistedPairing

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [AddCommGroup S] [Module ℂ S]

variable {π : G →* Module.End ℂ V}

section Level

variable [TopologicalSpace G]

variable (π) in

def IsLevelDenseAction (H : S →ₗ[ℂ] Module.End ℂ V) : Prop :=
  ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
    ∀ ℓ : V →ₗ[ℂ] ℂ, (∀ k ∈ K, ∀ x : V, ℓ (π k x) = ℓ x) →
      ∀ x₀ : V, (∀ k ∈ K, π k x₀ = x₀) → ∃ φ : S, ∀ x : V, H φ x = ℓ x • x₀

end Level

end TwistedPairing


