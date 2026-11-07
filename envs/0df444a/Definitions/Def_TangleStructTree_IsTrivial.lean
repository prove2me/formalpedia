-- Prove2me | Definitions.Def_TangleStructTree_IsTrivial
-- name    : TangleStructTree_IsTrivial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:11.279563+00:00
-- url     : https://prove2.me/theorems/ea73b2a1-abf4-4c93-80e1-c03a2727b7e3
-- title:
--   Trivial and co-trivial oriented separations
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system. An oriented separation $\vec s$ is **trivial** in $\vec S$ (and $\overleftarrow{s}$ is **co-trivial**) if there is a pair of inverse separations $\vec r,\overleftarrow{r}$ with
--   $$
--   \vec r<\vec s\quad\text{and}\quad\overleftarrow{r}<\vec s .
--   $$
--
--   Co-trivial separations cannot lie in a consistent orientation of $S$; standard sets $\mathcal F$ forbid them explicitly.
--
--   **Formalization Note** $x$ is co-trivial exactly when `IsTrivial (rev x)`.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, pp.3–4 (PDF 14–15)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- `s⃗` is **trivial** in `S⃗` (and `s⃖` is *co-trivial*) if there exists a pair of inverse
separations `r⃗, r⃖ < s⃗` in `S⃗` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, pp.3–4 (PDF 14–15)).

**Formalization Note** `x` is co-trivial exactly when `IsTrivial (rev x)`. -/
def IsTrivial (x : E) : Prop :=
  ∃ r : E, r < x ∧ rev r < x

end TangleStructTree


