-- Prove2me | Definitions.Def_Mathlib_Topology_Algebra_Group_Units
-- name    : Mathlib_Topology_Algebra_Group_Units
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/c2ad8dfd-74e0-577e-a69f-6437f38c21fc
-- title:
--   Openness of the unit group of an open submonoid
-- statement:
--   A single auxiliary lemma of topological algebra. Let $M$ be a monoid carrying a topology, and let $U$ be a submonoid of $M$. Mathlib's `Submonoid.units` attaches to $U$ the subgroup $U^\times$ of the unit group $M^\times$ consisting of those units $u$ for which both $u$ and $u^{-1}$, viewed in $M$, lie in $U$; as a subset of $M^\times$ it is thus the intersection of the preimages of $U$ under the two maps $u \mapsto u$ and $u \mapsto u^{-1}$ from $M^\times$ to $M$. The lemma [`Submonoid.units_isOpen`](../def/Mathlib_Topology_Algebra_Group_Units.html#L5) asserts that if $U$ is open as a subset of $M$, then $U^\times$ is open as a subset of $M^\times$, the latter being given its usual topology as a unit group, for which both coercion maps $M^\times \to M$ are continuous. No separate continuity hypothesis on the multiplication of $M$ is imposed: the statement is purely about openness of an intersection of two preimages of the open set $U$. The typical use is with $M$ a topological ring or a profinite monoid and $U$ an open submonoid, to produce open subgroups of $M^\times$ from open submonoids of $M$, for instance in the construction of neighbourhood bases of the identity in unit groups of topological rings.
--
--   **Relation to Mathlib.** The notions involved ($U^\times$ for a submonoid $U$, and the topology on $M^\times$ with its continuous coercions) are Mathlib's; the lemma itself is of general Mathlib character and is stated here in the `Submonoid` namespace.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/Topology/Algebra/Group/Units.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Ruben Van de Velde). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_Topology_Algebra_Group_Units.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M]
  {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)


