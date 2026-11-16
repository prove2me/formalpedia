-- Prove2me | Definitions.Def_TangleStructTree_Supplement_IsIrreducible
-- name    : TangleStructTree_Supplement_IsIrreducible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:06:51.447145+00:00
-- url     : https://prove2.me/theorems/9bd0cbcf-822b-44e0-b4d0-5993bd28d199
-- title:
--   Necessary edges and nodes; irreducible tangle structure trees
-- statement:
--   Let $(T,r,\beta)$ be a consistent separation tree on $\vec S$, let $\mathcal F$ be any set, and let $w$ be a child of the node $v$.
--
--   1. The edge $vw$ is **necessary for a tangle leaf** $\ell\ge_r w$ if $\beta(vw)$ is a $\le$-minimal element of the tangle $\lfloor\beta_\ell\rfloor$.
--   2. The edge $vw$ is **necessary for a forbidden leaf** $\ell\ge_r w$ if every subset of $\beta_\ell$ that lies in $\mathcal F$ contains $\beta(vw)$.
--   3. A node $v$ is **necessary** in $T$ if for every child $w$ of $v$ there is a leaf $\ell\ge_r w$ such that $vw$ is necessary for $\ell$ (leaves are necessary vacuously).
--   4. An $\mathcal F$-tangle structure tree is **irreducible** if every node of $T$ is necessary.
--
--   Irreducible trees have no edge that could be contracted while keeping a tangle structure tree (Lemma 5.4).
--
--   **Formalization Note** Nodes are root-path label lists, newest label first: the child $w$ of $v$ with $\beta(vw)=x$ is the list $x::v$, and $\ell\ge_r w$ is "$w$ is a suffix of $\ell$". Being an $\mathcal F$-tangle structure tree is part of `IsIrreducible`.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §5, pp.13–15 (PDF 24–26): necessary edges, necessary nodes, irreducible

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_IsTST

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- The edge `vw` of `T`, with `w = x :: v` (so `β(vw) = x`), is **necessary** for the leaf
`ℓ ≥_r w` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §5, p.13 (PDF 24)): "the edge `vw` of `T` [is] necessary for a
tangle leaf `ℓ ≥ w` of `T` if `β(vw)` is a `≤`-minimal element of the tangle `⌊β_ℓ⌋` [...]. We
call `vw` necessary for a forbidden leaf `ℓ ≥ w` if every subset of `β_ℓ` in `ℱ` contains
`β(vw)`."

**Formalization Note** Nodes are root-path label lists, newest first; `ℓ ≥_r w` is `w <:+ ℓ`, which
gives `x ∈ β_ℓ ⊆ ⌊β_ℓ⌋`, so minimality is "no element of `⌊β_ℓ⌋` lies strictly below `x`". -/
def NecessaryFor (T : SepTree E) (ℱ : Set (Set E)) (v : List E) (x : E) (ℓ : List E) : Prop :=
  x :: v ∈ T.nodes ∧ T.IsLeaf ℓ ∧ (x :: v) <:+ ℓ ∧
    ((T.IsTangleLeaf ℱ ℓ ∧ ∀ y ∈ sepClosure (labels ℓ), ¬ y < x) ∨
      (T.IsForbiddenLeaf ℱ ℓ ∧ ∀ σ ∈ ℱ, σ ⊆ labels ℓ → x ∈ σ))

/-- A node `v` is **necessary** in `T` "if for every child `w` of `v` there exists a leaf `ℓ ≥ w`
of `T` such that `vw` is necessary for `ℓ`" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §5, p.14 (PDF 25)). Leaves are
necessary vacuously. -/
def IsNecessaryNode (T : SepTree E) (ℱ : Set (Set E)) (v : List E) : Prop :=
  ∀ x : E, x :: v ∈ T.nodes → ∃ ℓ : List E, NecessaryFor T ℱ v x ℓ

/-- "A tangle structure tree `(T, r, β)` is called **irreducible** if every node of `T` is
necessary" (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §5, p.15 (PDF 26)).

**Formalization Note** Being an `ℱ`-tangle structure tree (`T.IsTST ℱ`) is part of the
definition. -/
def IsIrreducible (T : SepTree E) (ℱ : Set (Set E)) : Prop :=
  T.IsTST ℱ ∧ ∀ v ∈ T.nodes, IsNecessaryNode T ℱ v

end Supplement

end TangleStructTree


