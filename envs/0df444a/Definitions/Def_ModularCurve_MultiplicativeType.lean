-- Prove2me | Definitions.Def_ModularCurve_MultiplicativeType
-- name    : ModularCurve_MultiplicativeType
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/dd372209-3f50-5209-a33c-6b9122000438
-- title:
--   Multiplicative-type action: subgroup acting by a character scalar
-- statement:
--   The module fixes a group $G$, a commutative ring $R$, and an additive commutative group $J$ carrying both an $R$-module structure and a distributive multiplicative $G$-action (no compatibility between the two actions is imposed, and nothing about $J$ beyond these typeclasses is used). Two predicates are defined, both purely pointwise conditions on a chosen subobject.
--
--   [`ModularCurve.MultiplicativeType I χ W`](../def/ModularCurve_MultiplicativeType.html#L9) takes a subgroup $I \le G$, a monoid homomorphism $\chi : G \to R^\times$, and an $R$-submodule $W \subseteq J$, and asserts: for every $\sigma \in I$ and every $x \in W$, $\sigma \cdot x = \chi(\sigma) \cdot x$, where the unit $\chi(\sigma)$ is coerced to $R$ and acts through the module structure. Thus the $G$-action, restricted to $I$ and to vectors of $W$, is scalar multiplication by the character $\chi$. Only the restriction of $\chi$ to $I$ enters, and $G$-stability of $W$ is not a separate hypothesis: it is a consequence pointwise, since $\chi(\sigma)\cdot x$ lies in $W$.
--
--   [`ModularCurve.MultiplicativeTypeNat I n W`](../def/ModularCurve_MultiplicativeType.html#L12) is the ring-free variant: $n$ is an arbitrary function $G \to \mathbb{N}$ (not required to be multiplicative or a homomorphism), $W$ is merely an additive subgroup of $J$, and the condition is that $\sigma \cdot x = n(\sigma) \cdot x$ for all $\sigma \in I$, $x \in W$, with $n(\sigma) \cdot x$ the $\mathbb{N}$-scalar multiple, i.e. the iterated sum $x + \cdots + x$. This version mentions neither $R$ nor the module structure on $J$, so it transports along bare additive maps. Both are predicates on the given data $(I, \chi$ or $n, W)$; neither asserts the existence of such a $W$ or of such a character.
--
--   **Relation to Mathlib.** Mathlib has no predicate for "a subgroup acts on a submodule through a given character"; these are the project's own definitions, stated using Mathlib's `Subgroup`, `Submodule`, `AddSubgroup`, `Module` and `DistribMulAction`. Despite the `ModularCurve` namespace, the definitions are stated for a completely general group action on a module.
--
--   **Where it is used.** These predicates record the behaviour of a decomposition or inertia group on a distinguished part of the torsion of a Jacobian: the condition that inertia at $p$ act on the multiplicative (toric) part through the mod $p$ cyclotomic character, as opposed to acting trivially, which is the form taken by the local condition at primes away from $p$. They are imported by some thirty statement modules of the tree, where they supply the local hypotheses at $p$ in the semistable-reduction package feeding into the level-lowering and Galois-representation arguments; the $\mathbb{N}$-valued variant is used where the comparison is made along an additive map with no module compatibility available.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_MultiplicativeType.lean

import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurve

variable {G : Type*} [Group G] {R : Type*} [CommRing R]
  {J : Type*} [AddCommGroup J] [Module R J] [DistribMulAction G J]

def MultiplicativeType (I : Subgroup G) (χ : G →* Rˣ) (W : Submodule R J) : Prop :=
  ∀ σ ∈ I, ∀ x ∈ W, σ • x = (χ σ : R) • x

def MultiplicativeTypeNat (I : Subgroup G) (n : G → ℕ) (W : AddSubgroup J) : Prop :=
  ∀ σ ∈ I, ∀ x ∈ W, σ • x = n σ • x

end ModularCurve


