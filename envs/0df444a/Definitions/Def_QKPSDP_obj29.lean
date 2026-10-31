-- Prove2me | Definitions.Def_QKPSDP_obj29
-- name    : QKPSDP_obj29
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:48:33.76976+00:00
-- url     : https://prove2.me/theorems/33471ea3-d646-4737-83c3-27a036192914
-- title:
--   Cost matrix $2\operatorname{diag}((Cv)\circ d) - C$ of the SDP (29)
-- statement:
--   For $C \in \mathbb S^n$ and $v \in \{0,1\}^n$ with $d = 2v - e$, the cost matrix of the SDP (29) is
--
--   $$
--   2\operatorname{diag}\bigl((Cv)\circ d\bigr) - C ,
--   $$
--
--   where $\circ$ is the entrywise product. It is the second-order term of the objective of (SQKELR) along the curves leaving $R = ve_1^\top$ (Lemma 4.3).
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, (29), p.13

import Mathlib
import Definitions.Def_QKPSDP_dvec

open Matrix

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, (29), p.13: the cost matrix `2diag((Cv) ∘ d) − C` of the SDP
(29) attached to `R = ve₁⊤ ∈ N_{n,r}`, with `d = 2v − e` (p.8).

**Formalization Note** `∘` is the entrywise product, which is `*` on `Fin n → ℝ`; `diag` of a
vector is `diagonal`. -/
noncomputable def obj29 {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • diagonal ((C *ᵥ v) * dvec v) - C

end QKPSDP


