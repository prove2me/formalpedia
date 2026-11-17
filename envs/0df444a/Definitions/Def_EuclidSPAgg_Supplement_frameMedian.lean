-- Prove2me | Definitions.Def_EuclidSPAgg_Supplement_frameMedian
-- name    : EuclidSPAgg_Supplement_frameMedian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:43:16.442871+00:00
-- url     : https://prove2.me/theorems/03d86355-8d02-4916-a5a5-1314298d5a79
-- title:
--   Coordinate-wise median $\mathrm{CM}_{\mathcal B}(a,b,c)$ in an orthonormal frame of a subspace
-- statement:
--   Let $W$ be a linear subspace of a real inner product space $V$, let $\mathcal B=(e_1,\dots,e_r)$ be an orthonormal basis of $W$, and let $o\in V$ be an origin. For $a,b,c\in V$ the **coordinate-wise median in the frame $(o,\mathcal B)$** is
--   $$
--   \mathrm{CM}_{\mathcal B}(a,b,c)=o+\sum_{j=1}^{r}\operatorname{med}\big(\langle e_j,a-o\rangle,\langle e_j,b-o\rangle,\langle e_j,c-o\rangle\big)\,e_j ,
--   $$
--   where $\operatorname{med}$ is the median of three real numbers.
--
--   With $W$ the direction space of the affine hull of a convex set $C$ and $o\in C$, this is the operation $\mathrm{CM}_{\mathcal B}$ of Theorem 4.5. Because order statistics commute with translations, the value does not depend on the choice of the origin in $\operatorname{aff}C$.
--
--   **Formalization Note** The median of three reals is the published order statistic `ImpactInvesting.Portfolio.orderStat` at the 0-based rank $1$ (the second smallest of three), the same convention as the base mission's rule $Q_{\mathcal B,k}$.
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11); Theorem 4.5, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_ImpactInvesting_Portfolio_OrderStat
open ImpactInvesting.Portfolio (orderStat)

namespace EuclidSPAgg.Supplement

/-- The coordinate-wise median `CM_B(a, b, c)` of three points in an orthonormal frame `B` of a
subspace `W` with origin `o` (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), Section 2.1, p.9 (PDF p.11), and Theorem 4.5, p.17
(PDF p.19)):
`CM_B(a, b, c) = o + ∑_j med(⟨e_j, a − o⟩, ⟨e_j, b − o⟩, ⟨e_j, c − o⟩) e_j`,
where `B = (e_1, …, e_r)` is an orthonormal basis of `W` and `med` is the median of three reals.

**Formalization Note** `W` is used with `W = (affineSpan ℝ C).direction`, the direction space of
`aff C`, and `o` with a point of `C`. The median of three reals is the published
`ImpactInvesting.Portfolio.orderStat` at the 0-based rank `1 : Fin 3` (the paper's rank 2, as in the
base mission's `Q`). For `o, o' ∈ aff C` the value does not depend on the origin, because
`o − o' ∈ W` and order statistics commute with translations (p.9). -/
noncomputable def frameMedian {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {W : Submodule ℝ V} {r : ℕ} (B : OrthonormalBasis (Fin r) ℝ W) (o a b c : V) : V :=
  o + ∑ j, orderStat ![inner ℝ ((B j : W) : V) (a - o), inner ℝ ((B j : W) : V) (b - o),
      inner ℝ ((B j : W) : V) (c - o)] 1 • ((B j : W) : V)

end EuclidSPAgg.Supplement


