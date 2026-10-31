-- Prove2me | Definitions.Def_ForecastAggLearn_hstar
-- name    : ForecastAggLearn_hstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:20.266273+00:00
-- url     : https://prove2.me/theorems/852eec19-1bd0-47be-84a4-f24d65a46434
-- title:
--   Optimal aggregation vector $h^*=A(A^\top A)^{-1}\mathbf 1_m$
-- statement:
--   For an injective $n\times m$ matrix $A$, $A^\top A$ is invertible and $A_l^{-1}=(A^\top A)^{-1}A^\top$ is a left inverse of $A$. The **optimal aggregation vector** is
--
--   $$
--   h^*=(A_l^{-1})^\top\mathbf 1_m=A(A^\top A)^{-1}\mathbf 1_m\in\mathbb R^n .
--   $$
--
--   In log-likelihood space the Bayes-optimal aggregate equals $h^*\cdot\tilde z+\tilde\mu$, where $\tilde z=A\tilde y$ is what the prior-aware aggregator can compute from the experts' forecasts; learning the optimal aggregation amounts to learning $h^*$.
--
--   **Formalization Note** The matrix inverse is Mathlib's, which is $0$ for a singular matrix; the theorems about $h^*$ assume $A$ injective.
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.2.1, p.17

import Mathlib

namespace ForecastAggLearn

/-- **The optimal aggregation vector `h*`.**
Babichenko, Garber, arXiv:1802.07107v1, §4.2.1, p.17: "denoting the left inverse of A by
A_l^{−1} := (A^⊤A)^{−1}A^⊤, [...] h* := 1_m A_l^{−1} ∈ ℝⁿ - the optimal aggregation of z̃".

`h* = (A_l^{−1})^⊤ 1_m = A (A^⊤A)^{−1} 1_m`.

**Formalization Note.** `⁻¹` is Mathlib's matrix inverse, which is `0` when `A^⊤A` is singular;
the theorems about `h*` assume `A` injective, when `A^⊤A` is invertible. -/
noncomputable def hstar {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : Fin n → ℝ :=
  A.mulVec ((A.transpose * A)⁻¹.mulVec (fun _ => 1))

end ForecastAggLearn


