-- Prove2me | Definitions.Def_TangleStructTree_sepClosure
-- name    : TangleStructTree_sepClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:53:27.963932+00:00
-- url     : https://prove2.me/theorems/cf0255fa-7d6a-46a9-8bd7-a1f3ad142fb7
-- title:
--   Closure $\lfloor\sigma\rfloor$ of a set of oriented separations
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system and $\sigma\subseteq\vec S$. An oriented separation $\vec s$ is **required** by $\sigma$ if $\vec s\notin\sigma$ and $\sigma\cup\{\overleftarrow{s}\}$ is inconsistent. The **closure** of $\sigma$ is
--   $$
--   \lfloor\sigma\rfloor:=\sigma\cup\{\vec s\in\vec S:\vec s\text{ is required by }\sigma\}.
--   $$
--
--   For consistent $\sigma$ the closure adds exactly the separations that every consistent orientation containing $\sigma$ must also contain; tangle structure trees store $\sigma$ along a path and recover the tangle as $\lfloor\sigma\rfloor$.
--
--   **Formalization Note** The paper defines "required" and $\lfloor\sigma\rfloor$ for consistent $\sigma$. The same formula is written here for every $\sigma$ (`Requires`, `sepClosure`); the mission applies it to label sets of separation-tree nodes, and these are consistent in every consistent or thoroughly ordered tree.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.4 (PDF 15)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsConsistent

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- `s⃗` is **required** by `σ` if `s⃗ ∉ σ` and `σ ∪ {s⃖}` is inconsistent (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…),
journal version, §2, p.4 (PDF 15)).

**Formalization Note** The paper makes this definition for consistent `σ`; the formula is
written here for every `σ` and is applied in the mission's statements to the label sets of
separation-tree nodes. -/
def Requires (σ : Set E) (x : E) : Prop :=
  x ∉ σ ∧ ¬ IsConsistent (insert (rev x) σ)

/-- The **closure** `⌊σ⌋ := σ ∪ {s⃗ ∈ S⃗ : s⃗ is required by σ}` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version,
§2, p.4 (PDF 15)).

**Formalization Note** Named `sepClosure` (Mathlib's `closure` is topological). The paper defines
`⌊σ⌋` for consistent `σ`; the same formula is used here for every `σ`. For consistent `σ` it
agrees with the paper's, and the label sets of the nodes of a thoroughly ordered separation tree
are consistent. -/
def sepClosure (σ : Set E) : Set E :=
  σ ∪ {x | Requires σ x}

end TangleStructTree


