-- Prove2me | Definitions.Def_TangleStructTree_Supplement_Bk
-- name    : TangleStructTree_Supplement_Bk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:09:18.261373+00:00
-- url     : https://prove2.me/theorems/ada921f6-f745-47df-a03b-74e0ee026e24
-- title:
--   The set $\mathcal B_k$
-- statement:
--   Let $G$ be a finite graph with vertex set $V$, $S$ the set of its separations and $k\in\mathbb N$. Then
--
--   $$\mathcal B_k:=\Big\{\sigma\subseteq\vec S:\ \Big|\bigcap\{B:(A,B)\in\sigma\}\Big|<k\Big\},$$
--
--   taken on $\vec S_k$ (the separations with $|A\cap B|<k$). The $\mathcal B_k$-tangles of $S_k$ correspond to the $k$-blocks of $G$.
--
--   **Formalization Note** The intersection over $\sigma=\emptyset$ is $V$, so $\emptyset\in\mathcal B_k$ iff $|V|<k$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §7, p.21 (PDF 32)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_Supplement_Sk
import Definitions.Def_TangleStructTree_Supplement_GraphSep

namespace TangleStructTree

namespace Supplement

variable {V : Type} [Fintype V] [DecidableEq V]

/-- "`B_k := {σ ⊆ S⃗ : |⋂{B | (A, B) ∈ σ}| < k}`, where `S` is the set of all separations of `G`"
(von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §7, p.21 (PDF 32)), taken on `S⃗_k` (separations of order `|A ∩ B| < k`).

**Formalization Note**
1. The intersection of the second sides over `σ = ∅` is the whole vertex set `V`.
2. Only the elements of `B_k` that are subsets of `S⃗_k` matter for `S⃗_k`, so `B_k` is defined on
   `S⃗_k = Sk (sepOrder G) k`. -/
def Bk (G : SimpleGraph V) (k : ℕ) : Set (Set (Sk (sepOrder G) (k : ℝ))) :=
  {σ | ({x : V | ∀ a ∈ σ, x ∈ a.1.1.2} : Set V).ncard < k}

end Supplement

end TangleStructTree


