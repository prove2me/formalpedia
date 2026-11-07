-- Prove2me | Definitions.Def_EuclidSPAgg_Q
-- name    : EuclidSPAgg_Q
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:38.091526+00:00
-- url     : https://prove2.me/theorems/37a2f404-4288-471a-9007-71a6b5085760
-- title:
--   Fixed-frame order-statistic rule $Q_{\mathcal B,k}$
-- statement:
--   Let $\mathcal B=(e_1,\dots,e_d)$ be an orthonormal basis of $E$, write $x_{i,j}=\langle e_j,x_i\rangle$ for the $j$-th coordinate of report $i$, and let $x_{(r),j}$ be the $r$-th smallest of $x_{1,j},\dots,x_{n,j}$. For a rank vector $k=(k_1,\dots,k_d)\in[n]^d$, the **fixed-frame order-statistic rule** is
--   $$
--   Q_{\mathcal B,k}(x)=\sum_{j=1}^d x_{(k_j),j}\,e_j .
--   $$
--   In each coordinate of the frame it selects a fixed order statistic of the reported coordinates.
--
--   **Formalization Note** The rank vector is a function from coordinates to $0$-based ranks in $\{0,\dots,n-1\}$; a Lean index $r$ stands for the paper's rank $r+1$. Every rank vector in $[n]^d$ is representable and no rank is out of range. The order statistic $x_{(r),j}$ is the published `ImpactInvesting.Portfolio.orderStat` (the value of $0$-based rank $r$ after sorting with `Tuple.sort`).
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_EuclidSPAgg_Mech
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
open RBMSensitivity (E)
open ImpactInvesting.Portfolio (orderStat)

namespace EuclidSPAgg

/-- The fixed-frame coordinate-wise order-statistic rule
`Q_{B,k}(x) = ∑_{j=1}^d x_{(k_j), j} e_j` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11)), where
`B = (e₁, …, e_d)` is an orthonormal basis, `x_{i,j} = ⟨e_j, x_i⟩`, and `x_{(r),j}` is the `r`-th
smallest of `x_{1,j}, …, x_{n,j}`.

**Formalization Note** The rank vector `k ∈ [n]^d` is `k : Fin d → Fin n` with 0-based ranks:
index `k j` is the paper's rank `k_j = k j + 1`. Every rank vector of `[n]^d` is representable and
no index is out of range. The order statistic is the published
`ImpactInvesting.Portfolio.orderStat`: `orderStat v r = v (Tuple.sort v r)`, the value of 0-based
rank `r` when `v` is sorted increasingly. -/
noncomputable def Q {n d : ℕ} (B : OrthonormalBasis (Fin d) ℝ (E d)) (k : Fin d → Fin n) : Mech n d :=
  fun x => ∑ j, orderStat (fun i => inner ℝ (B j) (x i)) (k j) • B j

end EuclidSPAgg


