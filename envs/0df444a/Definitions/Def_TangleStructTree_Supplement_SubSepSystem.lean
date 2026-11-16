-- Prove2me | Definitions.Def_TangleStructTree_Supplement_SubSepSystem
-- name    : TangleStructTree_Supplement_SubSepSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:04:59.325198+00:00
-- url     : https://prove2.me/theorems/5ed734ae-0b34-4a1f-a450-d5c264c00df3
-- title:
--   Separation systems inside a universe; submodularity
-- statement:
--   Let $U$ be a separation system, i.e. a partially ordered set with an order-reversing involution $\vec s\mapsto\overleftarrow s$. A **separation system $\vec S\subseteq U$** is a subset of $U$ that is closed under the involution; it carries the order and the involution induced from $U$.
--
--   If $U$ is a lattice (with the order of the separation system), $U$ is called a **universe of separations**, and it is **distributive** if it is distributive as a lattice. A separation system $\vec S\subseteq U$ is **submodular** if for every two elements $\vec r,\vec s\in\vec S$ at least one of $\vec r\wedge\vec s$ and $\vec r\vee\vec s$ (taken in $U$) lies in $\vec S$.
--
--   These are the standing notions of the profile application (Theorem 7.3).
--
--   **Formalization Note** $\vec S$ is a structure with a carrier set and closure under the involution, so that its elements form a type with an induced separation system structure and no side conditions.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.3 (PDF 14): universe of separations, distributive, submodular

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

namespace Supplement

open SepSystem

/-- A separation system `S⃗ ⊆ U` inside a separation system `U`: a subset closed under the
involution, with the induced order and involution (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.3 (PDF 14)). -/
structure SubSepSystem (U : Type*) [PartialOrder U] [SepSystem U] where
  /-- The oriented separations of `S⃗`. -/
  carrier : Set U
  /-- `S⃗` is closed under `∗`. -/
  rev_mem : ∀ x ∈ carrier, rev x ∈ carrier

variable {U : Type*} [PartialOrder U] [SepSystem U]

/-- The elements of `S⃗`, as a type. -/
abbrev SubSepSystem.Carrier (S : SubSepSystem U) : Type _ := {x : U // x ∈ S.carrier}

/-- `S⃗` with the order induced from `U` and the restricted involution. -/
instance instSepSystemCarrier (S : SubSepSystem U) : SepSystem S.Carrier where
  rev x := ⟨rev x.1, S.rev_mem x.1 x.2⟩
  rev_rev x := Subtype.ext (rev_rev x.1)
  rev_le_rev x y h := rev_le_rev x.1 y.1 h

/-- "If a separation system `U` happens to be a lattice [...] we call `U` a universe of separations.
[...] A separation system `S⃗ ⊆ U` is **submodular** if for every two elements of `S⃗` either their
infimum or their supremum in `U` also lies in `S⃗`" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.3 (PDF 14)).

**Formalization Note** The universe is a type `U` with a lattice structure whose order is the
order of the separation system. -/
def IsSubmodular {U : Type*} [Lattice U] [SepSystem U] (S : SubSepSystem U) : Prop :=
  ∀ x ∈ S.carrier, ∀ y ∈ S.carrier, x ⊓ y ∈ S.carrier ∨ x ⊔ y ∈ S.carrier

end Supplement

end TangleStructTree


