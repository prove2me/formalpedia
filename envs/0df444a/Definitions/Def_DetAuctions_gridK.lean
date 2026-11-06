-- Prove2me | Definitions.Def_DetAuctions_gridK
-- name    : DetAuctions_gridK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:08.1622+00:00
-- url     : https://prove2.me/theorems/d8fb36db-471a-4d21-a919-d281ec1d919d
-- title:
--   Unit $K$-grid $I_K$
-- statement:
--   For a positive integer $K$, the **unit $K$-grid** is
--   $$I_K=\{0,\tfrac1K,\tfrac2K,\dots,\tfrac{K-1}K,1\}\subseteq[0,1].$$
--   It is the value space of the discrete auctions on which the paper's master revenue inequality is proved: values are multiples of a minimum currency $1/K$.
--
--   **Formalization Note** A subset of $\mathbb R_{\ge0}$ (the value type of the published model), the range of $k\mapsto k/K$ for $k=0,\dots,K$. It is used only for $K\ge1$.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], §2, p.7 (pdf p.9)

import Mathlib

open scoped NNReal

namespace DetAuctions

/-- The **unit `K`-grid** `I_K = {0, 1/K, 2/K, …, (K−1)/K, 1}`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), §2, p.7: "We use I := [0, 1] to denote the real unit interval and
I_K := {0, 1/K, 2/K, . . . , (K − 1)/K, 1} to denote the unit K-grid, where K is a positive
integer."

**Formalization Note** The grid is a subset of `ℝ≥0` (the value type of the published model
`MultiItemRev.Decomp`), the range of `k ↦ k/K` for `k = 0, …, K`. It is used only for `K ≥ 1`,
which every statement that uses it assumes; at `K = 0` Lean's `x / 0 = 0` gives `{0}`. -/
def gridK (K : ℕ) : Set ℝ≥0 :=
  Set.range (fun k : Fin (K + 1) => ((k : ℕ) : ℝ≥0) / (K : ℝ≥0))

end DetAuctions


