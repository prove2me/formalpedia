-- Prove2me | Definitions.Def_TangleStructTree_SepTree_IsTST
-- name    : TangleStructTree_SepTree_IsTST
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:26.487415+00:00
-- url     : https://prove2.me/theorems/4f2628c9-e180-49bc-b942-f895460bf582
-- title:
--   $\mathcal F$-tangle structure trees
-- statement:
--   Let $(T,r,\beta)$ be a separation tree on $\vec S$ and $\mathcal F$ any set.
--
--   1. A leaf $\ell$ is an **$\mathcal F$-tangle leaf** if the closure $\lfloor\beta_\ell\rfloor$ is an $\mathcal F$-tangle of $S$.
--   2. A leaf $\ell$ is **forbidden** (by $\mathcal F$) if $\beta_\ell$ contains an element of $\mathcal F$ as a subset.
--
--   **Definition 3.6.** An **$\mathcal F$-tangle structure tree** of $\vec S$ is a consistent separation tree on $\vec S$ in which every leaf is either a tangle leaf or forbidden, and for every non-leaf node $v$ the set $\beta_v$ has no subset in $\mathcal F$.
--
--   Such a tree displays every $\mathcal F$-tangle of $S$ at a leaf, and certifies at its forbidden leaves why the remaining orientations are not $\mathcal F$-tangles.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §3, p.7 (PDF 18), Definition 3.6

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_Consistent

namespace TangleStructTree

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- A leaf `ℓ` is an **ℱ-tangle leaf** if the closure `⌊β_ℓ⌋` is an `ℱ`-tangle of `S`
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §3, p.7 (PDF 18)). -/
def SepTree.IsTangleLeaf (T : SepTree E) (ℱ : Set (Set E)) (ℓ : List E) : Prop :=
  T.IsLeaf ℓ ∧ IsTangle ℱ (sepClosure (labels ℓ))

/-- A leaf `ℓ` is **forbidden** (by `ℱ`) if `β_ℓ` contains an element of `ℱ` as a subset
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §3, p.7 (PDF 18)). -/
def SepTree.IsForbiddenLeaf (T : SepTree E) (ℱ : Set (Set E)) (ℓ : List E) : Prop :=
  T.IsLeaf ℓ ∧ ¬ Avoids ℱ (labels ℓ)

/-- **Definition 3.6** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, p.7 (PDF 18)): an **ℱ-tangle
structure tree** of `S⃗` is a consistent separation tree on `S⃗` in which every leaf is either a
tangle leaf or forbidden, and for every non-leaf node `v` the set `β_v` has no subset in `ℱ`.

**Formalization Note** A node `v` is a non-leaf iff some `x :: v` is a node (see `SepTree`). -/
def SepTree.IsTST (T : SepTree E) (ℱ : Set (Set E)) : Prop :=
  T.Consistent ∧
    (∀ ℓ : List E, T.IsLeaf ℓ → T.IsTangleLeaf ℱ ℓ ∨ T.IsForbiddenLeaf ℱ ℓ) ∧
    (∀ (v : List E) (x : E), x :: v ∈ T.nodes → Avoids ℱ (labels v))

end TangleStructTree


