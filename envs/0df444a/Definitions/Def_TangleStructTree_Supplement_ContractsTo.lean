-- Prove2me | Definitions.Def_TangleStructTree_Supplement_ContractsTo
-- name    : TangleStructTree_Supplement_ContractsTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:07:15.284768+00:00
-- url     : https://prove2.me/theorems/29f0c295-9b8e-420f-a49d-3a934ff20b29
-- title:
--   The contraction $T_{w\to v}$ and sequences of contractions
-- statement:
--   Let $(T,r,\beta)$ be a separation tree, $v$ a node and $w$ a child of $v$. The tree $T_{w\to v}$ is obtained from $T$ by **contracting the edge $vw$** and deleting every other child $w'$ of $v$ together with the subtree of the nodes $u\ge_r w'$. The new node arising from $vw$ is still called $w$, so $V(T_{w\to v})$ is regarded as a subset of $V(T)$; the labels of the remaining edges are kept, and if $v=r$ the new root is $w$.
--
--   $T'$ is **obtained from $T$ by a sequence of contractions** if there are trees $T=T^1,\dots,T^n=T'$ with $T^{i+1}=T^i_{w\to v}$ for a node $v$ of $T^i$ and a child $w$ of $v$; composing the identifications gives a map $\iota$ identifying the nodes of $T'$ with nodes of $T$.
--
--   This is the operation of Theorem 5.5.
--
--   **Formalization Note** In the root-path list encoding (newest label first), with $w=x::v$, the nodes of $T_{w\to v}$ are the nodes of $T$ that are not $\ge_r v$ together with the lists $p\mathbin{+\!\!+}v$ for every node $p\mathbin{+\!\!+}x::v$ of $T$ (the label $x$ erased); the identification sends $p\mathbin{+\!\!+}v$ back to $p\mathbin{+\!\!+}x::v$ and fixes every other node. `ContractsTo` is the inductive closure under these steps, starting from $T$ itself.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §5, p.13 (PDF 24): T_{w→v} and V(T_{w→v}) ⊆ V(T); p.15 (PDF 26): sequences of contractions (Theorem 5.5)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_SepTree

namespace TangleStructTree

namespace Supplement

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- `T'` is the contraction `T_{w→v}` of `T` along the edge `vw`, `w = x :: v` a child of `v`
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §5, p.13 (PDF 24)): "`T_{w→v}` is obtained from `T` by contracting the edge
`vw` of `T` and deleting any other child `w′` of `v` together with the subtree spanned by the nodes
`u ≥_r w′`. We continue to use ‘`w`’ for the new node constructed from the edge `vw` [...]. If
`v = r` we set `r_{w→v} := w`; otherwise we keep `r_{w→v} := r`."

**Formalization Note** Nodes are root-path label lists, newest first. The nodes of `T_{w→v}` are the
nodes `u` of `T` not `≥_r v` (unchanged), and for every node `p ++ x :: v ≥_r w` of `T` the list
`p ++ v` (its root path with the label `x = β(vw)` erased). The list `v` names the merged node `w`,
and the nodes `≥_r w′` (`w′ = x∗ :: v`) are gone. -/
def IsContraction (T : SepTree E) (v : List E) (x : E) (T' : SepTree E) : Prop :=
  x :: v ∈ T.nodes ∧
    ∀ u : List E, u ∈ T'.nodes ↔
      ((u ∈ T.nodes ∧ ¬ v <:+ u) ∨ ∃ p : List E, u = p ++ v ∧ p ++ x :: v ∈ T.nodes)

open Classical in
/-- The identification of the nodes of `T_{w→v}` (`w = x :: v`) with nodes of `T`
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §5, p.13 (PDF 24): "we [...] think of `V(T_{w→v})` as a subset of `V(T)`"):
a node `p ++ v` of `T_{w→v}` is the node `p ++ x :: v` of `T`; every other node is itself. -/
noncomputable def embed (v : List E) (x : E) (u : List E) : List E :=
  if v <:+ u then u.take (u.length - v.length) ++ x :: v else u

/-- `ContractsTo T T' ι`: `T'` is obtained from `T` by a finite sequence
`T = T^1, …, T^n = T'` with `T^{i+1} = T^i_{w→v}` for a node `v` of `T^i` and a child `w` of `v`
in `T^i` (Theorem 5.5, von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §5, p.15 (PDF 26)), and `ι` is the composite
identification of the nodes of `T'` with nodes of `T` (the convention `V(T_{w→v}) ⊆ V(T)`). -/
inductive ContractsTo (T : SepTree E) : SepTree E → (List E → List E) → Prop
  /-- The empty sequence: `n = 1`, `T' = T`. -/
  | refl : ContractsTo T T id
  /-- One more contraction `T^{i+1} = T^i_{w→v}`, `w = x :: v`. -/
  | step {T₁ T₂ : SepTree E} {ι : List E → List E} {v : List E} {x : E} :
      ContractsTo T T₁ ι → IsContraction T₁ v x T₂ → ContractsTo T T₂ (ι ∘ embed v x)

end Supplement

end TangleStructTree


