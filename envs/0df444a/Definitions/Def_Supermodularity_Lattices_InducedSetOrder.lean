-- Prove2me | Definitions.Def_Supermodularity_Lattices_InducedSetOrder
-- name    : Supermodularity_Lattices_InducedSetOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:22:33.729021+00:00
-- url     : https://prove2.me/theorems/5e0119c3-ad5e-47f5-ae55-e677ca657f42
-- title:
--   The induced set ordering (strong set order) on subsets of a lattice
-- statement:
--   Let $X$ be a **lattice**: a partially ordered set with order relation $\preceq$ in
--   which every pair of elements $x, y \in X$ has a join $x \vee y$ (least upper bound)
--   and a meet $x \wedge y$ (greatest lower bound). For (not necessarily nonempty)
--   subsets $A, B \subseteq X$, the **induced set ordering** $A \sqsubseteq B$ holds if
--
--   $$
--   \forall\, a \in A,\ \forall\, b \in B:\quad a \wedge b \in A \ \text{ and }\ a \vee b \in B.
--   $$
--
--   This is Topkis's induced (also called the Veinott, or strong set) order on subsets of
--   a lattice: it is the natural way to compare two feasible-solution sets or two
--   optimal-solution sets arising from a parameterized optimization problem. When $A$
--   and $B$ are singletons $\{a\}$ and $\{b\}$, $A \sqsubseteq B$ holds exactly when
--   $a \preceq b$, so $\sqsubseteq$ specializes to the ambient order on points.
--
--   On the collection of nonempty sublattices of $X$, $\sqsubseteq$ is a genuine partial
--   order (antisymmetric and transitive); a correspondence (set-valued map) is called
--   *increasing* in a parameter precisely when it is monotone into this order.
--
--   **Formalization Note** The definition is stated for arbitrary sets `A B : Set X`,
--   exactly as Topkis defines the relation on all of $X \setminus \{\emptyset\}$ (indeed
--   even on the full power set, since the defining implication is vacuous whenever $A$ or
--   $B$ is empty); antisymmetry and transitivity require the nonemptiness hypothesis
--   separately, supplied at the point of use.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 32, Section 2.4 (Definition of the induced set ordering)

import Mathlib

namespace Supermodularity.Lattices

/-- The induced (Veinott/strong) set ordering `⊑` on subsets of a lattice `X`:
`InducedSetOrder A B` says `A ⊑ B`. -/
def InducedSetOrder {X : Type*} [Lattice X] (A B : Set X) : Prop :=
  ∀ ⦃a : X⦄, a ∈ A → ∀ ⦃b : X⦄, b ∈ B → a ⊓ b ∈ A ∧ a ⊔ b ∈ B

end Supermodularity.Lattices


