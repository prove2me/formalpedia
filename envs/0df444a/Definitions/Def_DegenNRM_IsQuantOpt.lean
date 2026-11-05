-- Prove2me | Definitions.Def_DegenNRM_IsQuantOpt
-- name    : DegenNRM_IsQuantOpt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:51.053732+00:00
-- url     : https://prove2.me/theorems/ca4c87b0-f467-4f95-ae44-ea8017f7b502
-- title:
--   Optimal solutions of the quantile programs (12) and (13)
-- statement:
--   For capacities $c$ and counts $d\in\mathbb R^n$, the quantile program (12) is
--   $$\max_q\ \sum_{j=1}^n d_j\,G_j(q_j)\quad\text{s.t.}\quad\sum_{j=1}^nd_j\,a_{j,i}\,q_j\le c_i\ \forall i\in[m],\qquad q_j\in[0,1]\ \forall j\in[n],$$
--   with $G_j(q)=\int_{1-q}^1F_j^{-1}$; $q_j$ is the probability of serving a type-$j$ query. A vector $q$ is an **optimal solution** if it is feasible and no feasible $q'$ has a larger objective.
--
--   The ex-ante (fluid) program (13) with $s$ periods left is (12) with $d_j$ replaced by its expectation $p_j s$; Algorithm 2 solves it at every period.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §3.3, (12)–(13), p.14

import Mathlib
import Definitions.Def_DegenNRM_quantile

namespace DegenNRM

/-- **Feasibility in the quantile program (12)** (Jiang, Ma & Zhang, arXiv:2210.07996v5, §3.3,
(12), p.14): `q_j ∈ [0, 1]` for every type and `Σ_j d_j a_{j,i} q_j ≤ c_i` for every resource. -/
def QuantFeasible {m n : ℕ} (inst : Instance m n) (c : Fin m → ℝ) (d : Fin n → ℝ)
    (q : Fin n → ℝ) : Prop :=
  (∀ j, q j ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ i, ∑ j, d j * inst.a j i * q j ≤ c i

/-- The objective of (12): `Σ_j d_j ∫_{1-q_j}^1 F_j⁻¹(q) dq = Σ_j d_j G_j(q_j)`. -/
noncomputable def quantObjective {m n : ℕ} (inst : Instance m n) (d : Fin n → ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ j, d j * Gfun inst j (q j)

/-- **`q` is an optimal solution of (12)** at capacities `c` and counts `d`
(arXiv:2210.07996v5, (12), p.14): `q` is feasible and no feasible `q′` has a larger
objective. -/
def IsQuantOpt {m n : ℕ} (inst : Instance m n) (c : Fin m → ℝ) (d : Fin n → ℝ)
    (q : Fin n → ℝ) : Prop :=
  QuantFeasible inst c d q ∧
    ∀ q', QuantFeasible inst c d q' → quantObjective inst d q' ≤ quantObjective inst d q

/-- **`q` is an optimal solution of the ex-ante (fluid) program (13)** at capacities `c` with
`s` periods left (arXiv:2210.07996v5, (13), p.14). Problem (13) is (12) with the counts `d_j`
replaced by their expectations `p_j · s`. -/
def IsFluidOpt {m n : ℕ} (inst : Instance m n) (c : Fin m → ℝ) (s : ℝ) (q : Fin n → ℝ) : Prop :=
  IsQuantOpt inst c (fun j => inst.p j * s) q

end DegenNRM


