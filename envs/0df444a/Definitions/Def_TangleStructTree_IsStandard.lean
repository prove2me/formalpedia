-- Prove2me | Definitions.Def_TangleStructTree_IsStandard
-- name    : TangleStructTree_IsStandard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:06.365869+00:00
-- url     : https://prove2.me/theorems/7a54c220-1cce-4761-87a9-8ad5a0abcc81
-- title:
--   Standard sets $\mathcal F$
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system. A set $\mathcal F$ is **standard** for $\vec S$ if
--   $$
--   \{\overleftarrow{s}\}\in\mathcal F\quad\text{for every } \vec s\in\vec S \text{ that is trivial in } \vec S .
--   $$
--
--   Since no consistent orientation of $S$ contains a co-trivial separation, a standard $\mathcal F$ places no restriction on the $\mathcal F$-tangles of $S$; it is one of the two conditions under which tangle structure trees exist.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §4, p.8 (PDF 19)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsTrivial

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- `ℱ` is **standard** for `S⃗` if `{s⃖} ∈ ℱ` for every `s⃗ ∈ S⃗` that is trivial in `S⃗`
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §4, p.8 (PDF 19)). -/
def IsStandard (ℱ : Set (Set E)) : Prop :=
  ∀ x : E, IsTrivial x → ({rev x} : Set E) ∈ ℱ

end TangleStructTree


