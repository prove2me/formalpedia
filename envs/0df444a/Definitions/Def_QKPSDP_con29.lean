-- Prove2me | Definitions.Def_QKPSDP_con29
-- name    : QKPSDP_con29
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:39.090859+00:00
-- url     : https://prove2.me/theorems/c958fa1f-d555-421a-aa16-eff98eaa6ad4
-- title:
--   Constraint matrix $aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d)$ of the SDP (29)
-- statement:
--   For $v \in \{0,1\}^n$ with $d = 2v - e$ and $\sigma_v$ as above, the constraint matrix of the SDP (29) is
--
--   $$
--   aa^\top - \sigma_v\tau\cdot\operatorname{diag}(a\circ d).
--   $$
--
--   The quadratic constraint $\langle aa^\top - \sigma_v\tau\operatorname{diag}(a\circ d), HH^\top\rangle = 0$ describes the second-order tangent directions of $\mathcal K_{n,r}$ at $R = ve_1^\top$ (Proposition 3.3).
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (29), p.13

import Mathlib
import Definitions.Def_QKPSDP_dvec
import Definitions.Def_QKPSDP_sigmaV

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (29), p.13: the constraint matrix
`aa⊤ − σ_v τ · diag(a ∘ d)` of the SDP (29) attached to `R = ve₁⊤ ∈ N_{n,r}`, with `d = 2v − e`
and `σ_v` as on p.8.

**Formalization Note** `∘` is the entrywise product `*` on `Fin n → ℝ`. -/
noncomputable def con29 {n : ℕ} (a : Fin n → ℝ) (τ : ℝ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  vecMulVec a a - (sigmaV v * τ) • diagonal (a * dvec v)

end QKPSDP


