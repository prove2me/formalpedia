-- Prove2me | Definitions.Def_MultiStageAlloc_Instance
-- name    : MultiStageAlloc_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:53.144191+00:00
-- url     : https://prove2.me/theorems/39647285-5f67-4d81-a90f-561471868b5f
-- title:
--   Instance of multi-stage vertex weighted matching (§2.1)
-- statement:
--   An instance of the $K$-stage vertex weighted matching model consists of a bipartite graph $G=(U,V,E)$ together with:
--
--   1. a stage $\mathrm{batch}(i)\in\{1,\dots,K\}$ for each online vertex $i\in U$, so that the batches $U_k=\{i:\mathrm{batch}(i)=k\}$ are disjoint and cover $U$;
--   2. a weight $w_j\ge 0$ for each offline vertex $j\in V$;
--   3. a capacity $n_j>0$ for each offline vertex $j\in V$.
--
--   The edges revealed at stage $k$ are $E_k=\{(i,j)\in E:\mathrm{batch}(i)=k\}$. Every statement of the mission is about such an instance.
--
--   **Formalization Note** The source assumes $n_j=1$ without loss of generality; $n_j$ here is any positive real, and $n\equiv 1$ recovers the printed model. Batches may be empty. Weights may be zero.
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, §2.1, p.12

import Mathlib

namespace MultiStageAlloc

/-- **An instance of the multi-stage vertex weighted matching model.** Feng & Niazadeh,
*Batching and Optimal Multi-stage Bipartite Allocations*, arXiv:2211.16581v1, §2.1, p.12: a
bipartite graph `G = (U, V, E)` whose online vertices `U` arrive in `K` stages. Here `batch i` is
the stage at which `i ∈ U` arrives, so the batches `U_k = {i | batch i = k}` are disjoint and cover
`U`; `edge` is `E`; `w j ≥ 0` is the weight of the offline vertex `j`, and `cap j > 0` is its
capacity `n_j`. The edge set of stage `k` is `E_k = {(i, j) ∈ E | batch i = k}`.

**Formalization Note.** The page assumes `n_j = 1` "without the loss of generality"; here `n_j` is
any positive real, and `cap = 1` recovers the printed model. A batch may be empty (the page assumes
`|U_k| ≥ 1`, which nothing uses), and `U`, `V` may be empty. Finiteness of `U` and `V` is a
`Fintype` hypothesis of each statement. -/
structure Instance (U V : Type*) (K : ℕ) where
  /-- The stage at which an online vertex arrives. -/
  batch : U → ℕ
  /-- Stages are numbered `1, …, K`. -/
  batch_mem : ∀ i, batch i ∈ Finset.Icc 1 K
  /-- The edge set `E`. -/
  edge : U → V → Prop
  /-- The weight `w_j` of an offline vertex. -/
  w : V → ℝ
  /-- Weights are non-negative; zero is allowed. -/
  w_nonneg : ∀ j, 0 ≤ w j
  /-- The capacity `n_j` of an offline vertex. -/
  cap : V → ℝ
  /-- Capacities are positive. -/
  cap_pos : ∀ j, 0 < cap j

end MultiStageAlloc


