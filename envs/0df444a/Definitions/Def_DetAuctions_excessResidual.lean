-- Prove2me | Definitions.Def_DetAuctions_excessResidual
-- name    : DetAuctions_excessResidual
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:19.733313+00:00
-- url     : https://prove2.me/theorems/9408ed94-b942-4818-987a-6f42137fb7f5
-- title:
--   Residual excess $\sum_j y_j-\max_j y_j$ of values over caps
-- statement:
--   For caps $c=(c_1,\dots,c_m)\in\mathbb R_+^m$ and values $x\in\mathbb R_+^m$, let $y_j=(x_j-c_j)_+$ be the excess of item $j$ over its cap. The **residual excess** is
--   $$\sum_{j=1}^m y_j-\max_{j\in[m]}y_j\ \ge 0 .$$
--   Its expectation $\mathbb E\big[\sum_j Y_j-\max_j Y_j\big]$ with $Y_j=(X_j-c_j)_+$ is the second term of the master revenue inequality (8): only realizations in which at least two items exceed their caps contribute.
--
--   **Formalization Note** On $\mathbb R_{\ge0}$ truncated subtraction is exactly the positive part, and the outer subtraction is exact since a sum of nonnegative terms is at least their maximum. With no items the value is $0$.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Proposition 3.1, Eq. (8), p.12 (pdf p.14)

import Mathlib

open scoped NNReal

namespace DetAuctions

/-- The **residual excess** `Σⱼ yⱼ − maxⱼ yⱼ` at the excesses `yⱼ = (xⱼ − cⱼ)₊` of the values
over the caps.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Proposition 3.1, Eq. (8), p.12: "E[Σ_{j=1}^m Yj − max_{j∈[m]} Yj] …
where … Yj := (Xj − cj)+".

**Formalization Note** On `ℝ≥0` the truncated subtraction `x j - c j` is exactly the positive
part `(xⱼ − cⱼ)₊`. The maximum over the items is `Finset.univ.sup`, which is `0` when there are
no items. The outer truncated subtraction loses nothing: the sum of nonnegative terms is at
least their maximum. -/
def excessResidual {ι : Type*} [Fintype ι] (c x : ι → ℝ≥0) : ℝ≥0 :=
  (∑ j, (x j - c j)) - Finset.univ.sup (fun j => x j - c j)

end DetAuctions


