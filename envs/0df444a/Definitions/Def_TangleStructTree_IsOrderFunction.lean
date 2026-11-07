-- Prove2me | Definitions.Def_TangleStructTree_IsOrderFunction
-- name    : TangleStructTree_IsOrderFunction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:08.199212+00:00
-- url     : https://prove2.me/theorems/a899e33c-c430-4d7a-ada7-ba7b26690e12
-- title:
--   Order functions on $S$
-- statement:
--   An **order function** on the unoriented separations $S$ of a separation system is any map $S\to\mathbb R$, $s\mapsto|s|$. It is extended to $\vec S$ by
--   $$
--   |\vec s|:=|\overleftarrow{s}|:=|s| .
--   $$
--   A separation system with an order function is an *ordered separation system*.
--
--   Order functions measure the size of separations (for graphs, the number of vertices in the separator) and drive the construction order of thoroughly ordered trees.
--
--   **Formalization Note** The order function is a map `ord : E → ℝ` on oriented separations with `ord (rev x) = ord x`; such maps are exactly the extensions to $\vec S$ of maps $S\to\mathbb R$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.5 (PDF 16)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- An **order function** on `S` is any map `S → ℝ`, `s ↦ |s|`, extended to `S⃗` by
`|s⃗| := |s⃖| := |s|` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.5 (PDF 16)).

**Formalization Note** The order function is given as a map `ord : E → ℝ` on oriented separations
satisfying `ord (x∗) = ord x`; such maps are exactly the extensions to `S⃗` of maps `S → ℝ`. -/
def IsOrderFunction (ord : E → ℝ) : Prop :=
  ∀ x : E, ord (rev x) = ord x

end TangleStructTree


