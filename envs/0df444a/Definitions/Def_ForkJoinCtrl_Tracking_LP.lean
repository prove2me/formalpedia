-- Prove2me | Definitions.Def_ForkJoinCtrl_Tracking_LP
-- name    : ForkJoinCtrl_Tracking_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:13:57.696997+00:00
-- url     : https://prove2.me/theorems/0d9a091c-0260-47f9-aa0e-debb5d9fb0c7
-- title:
--   §4.1, pp. 11–12 — the convex problem (17), the LP (18) with optimal value z(b), and the QP (19)
-- statement:
--   For a parameter $b=(q_k, k\in\mathcal K;\ w_i, i\in\mathcal I)\in\mathbb R^{a_2}$, $a_2=I+\sum_j K_j$ (dedicated queue lengths and shared-server workloads), the **LP (18)** has decision variables $(y_j, q_{ij}, j\in\mathcal J, i\in\mathcal I_j)$ and reads
--
--   $$\min \sum_{j\in\mathcal J} h_j y_j\quad\text{s.t.}\quad y_j\ge q_k\ (k\in\mathcal K_j),\quad y_j-q_{ij}\ge 0\ (i\in\mathcal I_j),\quad \sum_{j\in\mathcal J_i}\frac{q_{ij}}{\mu_{ij}}=w_i\ (i\in\mathcal I),\quad q_{ij}\ge 0.$$
--
--   Its **optimal value** $z(b)$ is defined as the infimum of the objective over the feasible set. The **QP (19)** minimizes $\sum_j y_j^2+\sum_j\sum_{i\in\mathcal I_j} q_{ij}^2$ over the LP-feasible points that also satisfy $\sum_j h_j y_j\le z(b)$ (19e), i.e. it selects the LP-optimal solution of smallest Euclidean norm; `QPOpt b x` says that $x$ is an optimal solution of the QP. The **convex problem (17)** minimizes $\sum_j h_j(\max_{k\in\mathcal K_j} q_k\vee\max_{i\in\mathcal I_j} q_{ij})$ over $q\ge 0$ with $\sum_{j\in\mathcal J_i} q_{ij}/\mu_{ij}=w_i$.
--
--   These objects carry the paper's control idea: the policy tracks the LP solution chosen by the QP, and $z$ is the asymptotically optimal cost.
--
--   **Formalization Note** The parameter $b$ is a pair of real vectors; Mathlib's norm $\|b\|$ on it is the maximum of the absolute values of the coordinates, the paper's $|b|_\infty$. Entries $q_{ij}$ of non-incident pairs are not decision variables and are pinned to $0$ in every feasible set, so that uniqueness statements are meaningful. Attainment of the LP minimum is not part of the definition of $z$.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, pp. 11–12, §4.1, (17), (18), (19), Lemma 1

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Network

namespace ForkJoinCtrl.Tracking

open scoped BigOperators

/-!
Özkan, arXiv:2002.01496v1, §4.1, pp. 11–12: the convex problem (17), the LP (18) with its optimal
value `z`, and the QP (19); Lemma 2's "optimal solution process selected by the QP" (p. 13).
-/

variable (N : Network)

/-- The parameter `b = (q_k, j ∈ 𝒥, k ∈ 𝒦_j; w_i, i ∈ ℐ) ∈ ℝ^{a₂}` of the LP (18), `a₂ = I + ∑_j K_j`:
the dedicated-server queue lengths `b.1 k` and the shared-server workloads `b.2 i`.
Mathlib's norm `‖b‖` on this product of finite products is the maximum of the absolute values of
all coordinates, i.e. the paper's `|b|_∞` (p. 5). -/
abbrev LPParam : Type := (Fin N.K → ℝ) × (Fin N.I → ℝ)

/-- `b ∈ ℝ^{a₂}_+`: all coordinates are nonnegative. -/
def LPParam.Nonneg {N : Network} (b : LPParam N) : Prop :=
  (∀ k, 0 ≤ b.1 k) ∧ ∀ i, 0 ≤ b.2 i

/-- A candidate decision vector `(y_j, q_ij)` of the LP (18) and the QP (19). Only the entries
`q i j` with `P_ij = 1` are decision variables; the feasibility predicates pin the other entries
to `0`. -/
structure LPVar where
  y : Fin N.J → ℝ
  q : Fin N.I → Fin N.J → ℝ

/-- The feasible set of the LP (18) at the parameter `b`, constraints (18b)–(18e):
* (18b) `y_j ≥ q_k` for all `j` and `k ∈ 𝒦_j`;
* (18c) `y_j − q_ij ≥ 0` for all `j` and `i ∈ ℐ_j`;
* (18d) `∑_{j ∈ 𝒥_i} q_ij / µ_ij = w_i` for all `i`;
* (18e) `q_ij ≥ 0` for all `j` and `i ∈ ℐ_j`;
and `q_ij = 0` for the non-incident pairs (these are not decision variables). -/
def LPFeasible (b : LPParam N) (x : LPVar N) : Prop :=
  (∀ k : Fin N.K, b.1 k ≤ x.y (N.own k)) ∧
  (∀ i j, N.P i j = true → 0 ≤ x.y j - x.q i j) ∧
  (∀ i, ∑ j ∈ N.Ji i, x.q i j / N.mu i j = b.2 i) ∧
  (∀ i j, N.P i j = true → 0 ≤ x.q i j) ∧
  (∀ i j, N.P i j = false → x.q i j = 0)

/-- The objective (18a) of the LP: `∑_j h_j y_j`. -/
def LPObj (x : LPVar N) : ℝ :=
  ∑ j, N.h j * x.y j

/-- `z(b)`, the optimal objective function value of the LP (18) (Lemma 1 Part 2, p. 12), as the
infimum of the objective over the feasible set. For `b ∈ ℝ^{a₂}_+` the feasible set is nonempty
and the objective is bounded below by `0`; attainment is a statement, not part of this
definition. -/
noncomputable def z (b : LPParam N) : ℝ :=
  sInf (LPObj N '' {x | LPFeasible N b x})

/-- The feasible set of the QP (19): (19b)–(19d), (19f) are (18b)–(18e), and
(19e) `∑_j h_j y_j ≤ z(b)`. -/
def QPFeasible (b : LPParam N) (x : LPVar N) : Prop :=
  LPFeasible N b x ∧ LPObj N x ≤ z N b

/-- The objective (19a) of the QP: `∑_j y_j² + ∑_j ∑_{i ∈ ℐ_j} q_ij²`. -/
def QPObj (x : LPVar N) : ℝ :=
  ∑ j, x.y j ^ 2 + ∑ j, ∑ i ∈ N.Ij j, x.q i j ^ 2

/-- `x` is an optimal solution of the QP (19) at the parameter `b`. -/
def QPOpt (b : LPParam N) (x : LPVar N) : Prop :=
  QPFeasible N b x ∧ ∀ x', QPFeasible N b x' → QPObj N x ≤ QPObj N x'

/-- The feasible set of the convex problem (17) at `b`: (17b) `∑_{j ∈ 𝒥_i} q_ij / µ_ij = w_i` for
all `i`, (17c) `q_ij ≥ 0` for the incident pairs, and `q_ij = 0` for the non-incident pairs. -/
def Feas17 (b : LPParam N) (q : Fin N.I → Fin N.J → ℝ) : Prop :=
  (∀ i, ∑ j ∈ N.Ji i, q i j / N.mu i j = b.2 i) ∧
  (∀ i j, N.P i j = true → 0 ≤ q i j) ∧
  (∀ i j, N.P i j = false → q i j = 0)

/-- The objective (17a): `∑_j h_j (max_{k ∈ 𝒦_j} q_k ∨ max_{i ∈ ℐ_j} q_ij)`. -/
noncomputable def Obj17 (b : LPParam N) (q : Fin N.I → Fin N.J → ℝ) : ℝ :=
  ∑ j, N.h j * N.jobMax j b.1 (fun i => q i j)

end ForkJoinCtrl.Tracking


