-- Prove2me | Definitions.Def_TangleStructTree_SepSystem
-- name    : TangleStructTree_SepSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:51:30.802231+00:00
-- url     : https://prove2.me/theorems/06d6ffb0-cbdc-4183-bc4b-428440f3617b
-- title:
--   Separation system $(\vec S,\le,{}^*)$ and its unoriented separations
-- statement:
--   A **separation system** $(\vec S,\le,{}^*)$ is a set $\vec S$, whose elements are called *oriented separations*, together with a partial order $\le$ on $\vec S$ and an order-reversing involution ${}^*:\vec S\to\vec S$: for all $\vec r,\vec s\in\vec S$,
--   $$
--   (\vec s^{\,*})^{*}=\vec s,\qquad \vec r\le\vec s\ \Longrightarrow\ \vec r^{\,*}\ge\vec s^{\,*}.
--   $$
--   One writes $\overleftarrow{s}:=\vec s^{\,*}$ and calls it the *inverse* of $\vec s$. A separation with $\vec s=\overleftarrow{s}$ is *degenerate*; degenerate separations are allowed.
--
--   The set of **unoriented separations** is
--   $$
--   S:=\{\{\vec s,\overleftarrow{s}\}:\vec s\in\vec S\},
--   $$
--   and $\vec s,\overleftarrow{s}$ are the two *orientations* of $s=\{\vec s,\overleftarrow{s}\}$.
--
--   Separation systems are the abstract setting of tangle theory: graph separations, set bipartitions and many other structures are instances, and every later notion of the mission (orientations, consistency, tangles, separation trees) is defined on them.
--
--   **Formalization Note** $\vec S$ is a type `E` with a `PartialOrder` and an instance `SepSystem E` carrying the involution `rev` (the name `star` is taken in Mathlib). No lattice structure, non-degeneracy or finiteness is assumed. `Unoriented E` is the set of the sets $\{x,x^*\}$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, pp.3–4 (PDF 14–15)

import Mathlib

namespace TangleStructTree

/-- A **separation system** `(S⃗, ≤, ∗)` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version (Part I),
§2, p.3 (PDF 14)): a set `S⃗` of *oriented separations* with a partial ordering `≤` and an
order-reversing involution `∗ : S⃗ → S⃗`. The inverse `s⃗∗` of `s⃗` is written `s⃖`; a separation
with `s⃗ = s⃖` is *degenerate*.

**Formalization Note** `S⃗` is a type `E` with a `PartialOrder`; the involution `∗` is the field
`rev` (the name `star` is taken by Mathlib's `Star` class). Nothing else is assumed: no lattice
structure, no non-degeneracy, no finiteness. -/
class SepSystem (E : Type*) [PartialOrder E] where
  /-- The involution `s⃗ ↦ s⃗∗ = s⃖`. -/
  rev : E → E
  /-- `∗` is an involution. -/
  rev_rev : ∀ x : E, rev (rev x) = x
  /-- `∗` is order-reversing: `r⃗ ≤ s⃗` implies `r⃗∗ ≥ s⃗∗`. -/
  rev_le_rev : ∀ x y : E, x ≤ y → rev y ≤ rev x

/-- The set `S := {{s⃗, s⃖} : s⃗ ∈ S⃗}` of **unoriented separations** of a separation system
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.4 (PDF 15)). An unoriented separation is the
two-element (or, if degenerate, one-element) set of its orientations. -/
def Unoriented (E : Type*) [PartialOrder E] [SepSystem E] : Set (Set E) :=
  Set.range fun x : E => ({x, SepSystem.rev x} : Set E)

end TangleStructTree


