-- Prove2me | Definitions.Def_Supermodularity_Lattices_Subcomplete
-- name    : Supermodularity_Lattices_Subcomplete
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:22:54.967013+00:00
-- url     : https://prove2.me/theorems/8cb163e1-670c-422f-b094-ec71f4c3dd6b
-- title:
--   A subcomplete sublattice of a lattice
-- statement:
--   Let $X$ be a lattice and $S \subseteq X$ a **sublattice** (closed under the binary
--   join $\vee$ and meet $\wedge$ of $X$). $S$ is a **subcomplete sublattice** of $X$ if,
--   for every nonempty subset $U \subseteq S$, the supremum $\sup_X U$ and infimum
--   $\inf_X U$ (computed in the ambient lattice $X$, i.e. the least upper bound and
--   greatest lower bound of $U$ among *all* elements of $X$) both exist and belong to
--   $S$.
--
--   Subcompleteness is strictly stronger than being a sublattice: a sublattice need only
--   be closed under *binary* joins and meets of its own elements, while a subcomplete
--   sublattice must contain the join and meet of *every* (possibly infinite) nonempty
--   subset of itself. Every finite sublattice is automatically subcomplete. A closed
--   interval $[a, b] = \{x \in X : a \preceq x \preceq b\}$ of a complete lattice $X$ is
--   always a subcomplete sublattice of $X$, even though it need not contain the top or
--   bottom element of $X$ itself.
--
--   **Formalization Note** Existence of $\sup_X U$ and $\inf_X U$ is expressed with
--   Mathlib's `IsLUB`/`IsGLB` predicates rather than by assuming `X` is a
--   `CompleteLattice`, since Topkis's definition applies to a subcomplete sublattice of
--   an arbitrary lattice; every use of `Subcomplete` in this mission instantiates `X`
--   with a `CompleteLattice`, where `sSup`/`sInf` always witness these predicates.
-- source:
--   Topkis, Supermodularity and Complementarity, Princeton University Press, 2011, p. 20, Section 2.3

import Mathlib

namespace Supermodularity.Lattices

/-- `Subcomplete S` says the subset `S` of a lattice `X` is a subcomplete sublattice
of `X`: `S` is a sublattice, and every nonempty subset of `S` has a supremum and an
infimum in `X` that both lie in `S`. -/
def Subcomplete {X : Type*} [Lattice X] (S : Set X) : Prop :=
  IsSublattice S ∧
    ∀ ⦃U : Set X⦄, U ⊆ S → U.Nonempty →
      (∃ s : X, IsLUB U s ∧ s ∈ S) ∧ (∃ i : X, IsGLB U i ∧ i ∈ S)

end Supermodularity.Lattices


