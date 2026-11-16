-- Prove2me | Definitions.Def_PerturbedWF_Supplement_HSTKServer
-- name    : PerturbedWF_Supplement_HSTKServer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:07:03.986194+00:00
-- url     : https://prove2.me/theorems/ca3441e4-a86d-4278-84a8-db93092582fb
-- title:
--   $k$-server on HSTs: edges, the matrix $A_{i,e}=w_e\mathbf 1\{e\in P_i\}$ and equal sibling weights
-- statement:
--   Let $T$ be a $\tau$-HST (a rooted tree with positive edge weights, $w_f\le w_e/\tau$ for consecutive edges $e,f$ on a root-to-leaf path); its points are the leaves and the distance is the weighted path length. Its edges $E$ are identified with their lower endpoints. §8.3 assumes that **all edges incident to the same parent node have the same weight**. The algorithm of §8.3.1 uses the matrix
--   $$A_{i,e}=w_e\,\mathbf 1\{e\in P_i\},$$
--   where $P_i$ is the root-to-leaf path of $i$, so $v_i=\sum_{e\in P_i}w_eq_e$.
--
--   **Formalization Note** The tree is the published `PolylogKServer.HST.WTree`; the edge $(p(u),u)$ is the non-root node $u$, and it lies on $P_i$ exactly when $u$ is an ancestor of $i$.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §8.3 'k-server', p.24 (PDF p.25); §8.3.1 'Algorithm', p.25 (PDF p.26)

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PerturbedWF_Supplement_KServer

namespace PerturbedWF.Supplement

/-!
# k-server on HSTs: edges, the matrix `A` and equal sibling weights (§8.3, §8.3.1)

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §8.3 "k-server", p.24 (PDF p.25), and §8.3.1
"Algorithm", p.25 (PDF p.26).

`T` is a τ-HST (a `PolylogKServer.HST.WTree`; its points are the leaves, the distance is
`treeDist`). Its edges `E` are identified with their lower (non-root) nodes, the edge
`(p(u), u)` with `u`. §8.3 assumes that all edges incident to the same parent node have the same
weight (`SiblingsEqual`). `A ∈ ℝ^{n×E}` has `A_{i,e} = w_e 1{e ∈ P_i}`, `P_i` the root-to-`i` path;
the edge `u` lies on `P_i` exactly when `u` is an ancestor of `i`.
-/

open PolylogKServer.HST

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The edges of `T`, identified with the non-root nodes. -/
abbrev Edge (T : WTree V) : Type := {v : V // v ≠ T.root}

/-- §8.3: all edges incident to the same parent node have the same weight. -/
def SiblingsEqual (T : WTree V) : Prop :=
  ∀ u v, u ≠ T.root → v ≠ T.root → T.parent u = T.parent v → T.W u = T.W v

/-- `A_{i,e} = w_e 1{e ∈ P_i}`: the edge `e` lies on the root-to-leaf path of `i`. -/
noncomputable def hstMatrix (T : WTree V) (i : T.Leaf) (e : Edge T) : ℝ := by
  classical
  exact if T.IsAnc e.1 i.1 then T.W e.1 else 0

end PerturbedWF.Supplement


