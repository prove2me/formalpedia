-- Prove2me | Definitions.Def_TangleStructTree_IsTangle
-- name    : TangleStructTree_IsTangle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:10.441674+00:00
-- url     : https://prove2.me/theorems/d8c17654-7f99-4491-ba74-739b07e5e29d
-- title:
--   $\mathcal F$-avoiding sets and $\mathcal F$-tangles
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system and $\mathcal F$ any set (of sets of oriented separations). A set $\tau\subseteq\vec S$ **avoids** $\mathcal F$ if no subset of $\tau$ is an element of $\mathcal F$.
--
--   **Definition 2.3.** An **$\mathcal F$-tangle of $S$** is an $\mathcal F$-avoiding consistent orientation of $S$.
--
--   The elements of $\mathcal F$ are the "forbidden" configurations; the choice of $\mathcal F$ recovers graph tangles, $k$-blocks, profiles and cluster tangles as special cases.
--
--   **Formalization Note** $\mathcal F$ is a `Set (Set E)`: elements of $\mathcal F$ that are not subsets of $\vec S$ are never subsets of any $\tau$ and play no role.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.6 (PDF 17), Definition 2.3

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent

namespace TangleStructTree

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- `τ ⊆ S⃗` **avoids** `ℱ` if `τ` has no subset in `ℱ`, i.e. if no subset of `τ` is an element
of `ℱ` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.6 (PDF 17)).

**Formalization Note** `ℱ` is "any set"; it is a `Set (Set E)`, since elements of `ℱ` that are
not subsets of `S⃗` are never subsets of any `τ` and do not matter. -/
def Avoids (ℱ : Set (Set E)) (τ : Set E) : Prop :=
  ∀ σ ∈ ℱ, ¬ σ ⊆ τ

/-- **Definition 2.3** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.6 (PDF 17)): an **ℱ-tangle
of `S`** is an `ℱ`-avoiding consistent orientation of `S`. -/
def IsTangle (ℱ : Set (Set E)) (τ : Set E) : Prop :=
  IsOrientation τ ∧ IsConsistent τ ∧ Avoids ℱ τ

end TangleStructTree


