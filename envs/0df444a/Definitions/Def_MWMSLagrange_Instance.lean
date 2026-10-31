-- Prove2me | Definitions.Def_MWMSLagrange_Instance
-- name    : MWMSLagrange_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:36.7185+00:00
-- url     : https://prove2.me/theorems/4acf4896-3657-477e-8d01-ed4f1e1301fe
-- title:
--   MWMS instance: network $\mathcal M_i$, inventories $C_j$, costs $h_i, b_i, c_{i,j}, w_j$
-- statement:
--   An instance of the $T$-period **Multi-Warehouse Multi-Store (MWMS)** problem has $M$ warehouses $j\in[M]$ and $N$ stores $i\in[N]$, and consists of
--
--   1. a bipartite network: store $i$ can be replenished from the warehouses $j\in\mathcal M_i\subseteq[M]$, and $\mathcal N_j=\{i : j\in\mathcal M_i\}$ is the set of stores that warehouse $j$ can serve;
--   2. initial, non-replenishable warehouse inventories $C_j$;
--   3. unit holding costs $h_i$ and unit lost-sales costs $b_i$ at the stores;
--   4. unit shipping costs $c_{i,j}$ from warehouse $j$ to store $i$;
--   5. unit end-of-horizon costs $w_j\in\mathbb R$ on inventory left in warehouse $j$ ($w_j>0$ a cost, $w_j<0$ a salvage value).
--
--   These are the primitives of the model of §2; every other object of the mission is built from them.
--
--   **Formalization Note** Warehouses and stores are indexed by `Fin M` and `Fin N`; the network is a Boolean matrix `adj i j` ($j\in\mathcal M_i$). The sign conditions are kept separate, in `Instance.Valid`.
-- source:
--   Miao, Jasin, Chao, Asymptotically Optimal Lagrangian Policies for Multi-Warehouse, Multi-Store Systems with Lost Sales, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2, pp.6–7 (model, cost list)

import Mathlib

namespace MWMSLagrange

/-- Miao, Jasin, Chao, *Asymptotically Optimal Lagrangian Policies for Multi-Warehouse,
Multi-Store Systems with Lost Sales*, SSRN 3552995 (manuscript, sha256 1146a7f8…), §2,
pp.6–7: an instance of the T-period Multi-Warehouse Multi-Store (MWMS) problem with `M`
warehouses `j ∈ [M]` and `N` stores `i ∈ [N]`.

* `adj i j = true` iff store `i` can be replenished from warehouse `j`, i.e. `j ∈ 𝓜_i`
  (equivalently `i ∈ 𝓝_j`);
* `C j` is the initial (non-replenishable) inventory `C_j` of warehouse `j`;
* `h i`, `b i` are the unit holding and lost-sales costs of store `i`;
* `c i j` is the unit shipping cost from warehouse `j` to store `i`;
* `w j` is the unit end-of-horizon cost of inventory left in warehouse `j` (any sign).

**Formalization Note.** Indices are `Fin M`, `Fin N` (0-based). The sign conditions of p.7
(`h, b, c ≥ 0`, `C ≥ 0`) are not part of the structure; they are `Instance.Valid`. The values
`c i j` off the network are never used. -/
structure Instance (M N : ℕ) where
  /-- `adj i j = true` iff `j ∈ 𝓜_i` (warehouse `j` can ship to store `i`). -/
  adj : Fin N → Fin M → Bool
  /-- initial inventory `C_j` of warehouse `j` -/
  C : Fin M → ℝ
  /-- unit holding cost `h_i` of store `i` -/
  h : Fin N → ℝ
  /-- unit lost-sales cost `b_i` of store `i` -/
  b : Fin N → ℝ
  /-- unit shipping cost `c_{i,j}` from warehouse `j` to store `i` -/
  c : Fin N → Fin M → ℝ
  /-- unit end-of-horizon cost `w_j` of warehouse `j` -/
  w : Fin M → ℝ

end MWMSLagrange


