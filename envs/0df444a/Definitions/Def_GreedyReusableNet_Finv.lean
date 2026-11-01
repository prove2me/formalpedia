-- Prove2me | Definitions.Def_GreedyReusableNet_Finv
-- name    : GreedyReusableNet_Finv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:02.008853+00:00
-- url     : https://prove2.me/theorems/4337d31e-2df9-4879-99ea-3d34f0fe564c
-- title:
--   Quantile function $F_i^{-1}(U;n)$ of the law $F_i(\cdot;n)$
-- statement:
--   For a distribution $F$ on $\mathbb N$ with distribution function $F(x)=\Pr[b\le x]$ and a seed $U$,
--   $$F^{-1}(U)=\inf\{x\in\mathbb N: F(x)\ge U\}.$$
--   For $U$ uniform on $[0,1]$, $F^{-1}(U)\sim F$. This is the realization of blocking times used in the queue coupling.
--
--   **Formalization Note** The infimum is over $\mathbb N$ rather than $\{1,2,\dots\}$ because blocking times may be $0$; for laws on $\{1,2,\dots\}$ the two agree for every $U\in(0,1]$. The set is empty only for a null set of seeds, where Lean's infimum of the empty set gives $0$.
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §3.2, Queue Coupling, p.20

import Mathlib

namespace GreedyReusableNet

/-- **The quantile function of the law `F_i(·; n)` of `b_{t,i}`** (Simchi-Levi, Zheng & Zhu, SSRN 3981123,
§3.2, "Queue Coupling", p.20): `F^{-1}(U; n) = inf{x : F(x; n) ≥ U} ∼ F(·; n)`, where
`F(x) = ℙ(b ≤ x)` for `b ∼ F`.

**Formalization Note** The times `b_{t,i}` take values in `ℕ` (see `ProblemInstance`), so the infimum
is over `x ∈ ℕ` (the paper writes `x ∈ ℤ₊₊`; for a law supported on `ℤ₊₊` the two agree for every
`U ∈ (0, 1]`). For `U` uniform on `[0, 1]` the result has law `F`. The set is empty only on a null
set of seeds (`U = 1` when `F` never reaches `1`, or `U > 1`), where `sInf ∅ = 0`. -/
noncomputable def Finv (F : PMF ℕ) (u : ℝ) : ℕ :=
  sInf {x : ℕ | u ≤ (F.toOuterMeasure (Set.Iic x)).toReal}

end GreedyReusableNet


