-- Prove2me | Definitions.Def_MulticutLShaped_Bound_Masters
-- name    : MulticutLShaped_Bound_Masters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:55:27.924777+00:00
-- url     : https://prove2.me/theorems/6bf047b8-9236-48d5-bf6a-cd06aca781a7
-- title:
--   The multicut master (11)–(13) and the L-shaped master (4)–(6), with feasibility, objective and optimality
-- statement:
--   Cuts are pairs $(D,d)$ or $(E,e)$ with $D,E\in\mathbb R^{n_1}$ and $d,e\in\mathbb R$. Let $F=[(D_1,d_1),\dots,(D_s,d_s)]$ be a list of feasibility cuts.
--
--   **Multicut master (11)–(13).** For each scenario $k=1,\dots,K$ let $C_k$ be a list of optimality cuts $(E_{l(k)},e_{l(k)})$, $l(k)=1,\dots,t(k)$. A point $(x,\theta_1,\dots,\theta_K)$ is feasible when
--   $$Ax=b,\quad x\ge 0,\quad D_l x\ge d_l\ (l=1,\dots,s),\quad E_{l(k)}x+\theta_k\ge e_{l(k)}\ (\text{all } k,\ l(k)).$$
--   Its objective is
--   $$z = cx + \sum_{k\,:\,t(k)\ge 1}\theta_k ,$$
--   since, by the paper's convention, a $\theta_k$ for which no constraint (13) is present is set to $-\infty$ and ignored in the computation. A feasible point is optimal when no feasible point has a smaller objective.
--
--   **L-shaped master (4)–(6).** For a single list $L=[(E_1,e_1),\dots,(E_t,e_t)]$ of optimality cuts, $(x,\theta)$ with $\theta\in\mathbb R$ is feasible when $Ax=b$, $x\ge0$, $D_lx\ge d_l$ and $E_lx+\theta\ge e_l$ for all $l$. Its objective is $cx+\theta$, or $cx$ when $t=0$ ($\theta$ ignored). Optimality is defined in the same way.
--
--   These are the linear programs solved in Step 1 of the two algorithms; they are needed to state the aggregation argument of the Proposition and the multicut algorithm itself.
--
--   **Formalization Note** Optimality is attainment: an optimal solution is a feasible point whose objective is a lower bound over the feasible set. No infimum is taken, so an unbounded or infeasible master simply has no optimal solution.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 386, Section 2 Eqs. (4)-(6), Section 3 Eqs. (11)-(13)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance

namespace MulticutLShaped.Bound

open StochasticProg.Recourse
open scoped Matrix

variable {n1 n2 m1 m2 K : ℕ}

/-- `(x, θ_1, …, θ_K)` is feasible in the multicut master program (11)–(13)
(Birge–Louveaux 1988, p. 386) with feasibility cuts `F = [(D_1, d_1), …, (D_s, d_s)]` and,
for each scenario `k`, optimality cuts `C k = [(E_{1(k)}, e_{1(k)}), …]`:
`A x = b`, `x ≥ 0`, `D_l x ≥ d_l` for all `l` (12), and `E_{l(k)} x + θ_k ≥ e_{l(k)}` for all
`k` and `l(k)` (13). A `θ_k` whose scenario has no cut is unconstrained. -/
def MultiFeasible (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (C : Fin K → List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : Fin K → ℝ) : Prop :=
  x ∈ K1 inst ∧ (∀ c ∈ F, c.2 ≤ c.1 ⬝ᵥ x) ∧ (∀ k, ∀ c ∈ C k, c.2 ≤ c.1 ⬝ᵥ x + θ k)

open Classical in
/-- The multicut master objective (11), `z = c x + Σ_k θ_k`, where — as on p. 386 — a `θ_k`
for which no constraint (13) is present is "set equal to −∞ and ignored in the
computation": the sum runs only over the scenarios `k` with at least one cut. -/
noncomputable def multiObj (inst : Instance n1 n2 m1 m2 K) (C : Fin K → List ((Fin n1 → ℝ) × ℝ))
    (x : Fin n1 → ℝ) (θ : Fin K → ℝ) : ℝ :=
  inst.c ⬝ᵥ x + ∑ k ∈ Finset.univ.filter (fun k => C k ≠ []), θ k

/-- `(x, θ)` is an optimal solution of the multicut master (11)–(13): it is feasible and
its objective (11) is no larger than that of any feasible point. -/
def IsMultiOptimal (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (C : Fin K → List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : Fin K → ℝ) : Prop :=
  MultiFeasible inst F C x θ ∧
    ∀ x' θ', MultiFeasible inst F C x' θ' → multiObj inst C x θ ≤ multiObj inst C x' θ'

/-- `(x, θ)` is feasible in the single-cut L-shaped master (4)–(6) (p. 386) with
feasibility cuts `F` and optimality cuts `L = [(E_1, e_1), …, (E_t, e_t)]`:
`A x = b`, `x ≥ 0`, `D_l x ≥ d_l` (5) and `E_l x + θ ≥ e_l` (6). -/
def LFeasible (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (L : List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  x ∈ K1 inst ∧ (∀ c ∈ F, c.2 ≤ c.1 ⬝ᵥ x) ∧ (∀ c ∈ L, c.2 ≤ c.1 ⬝ᵥ x + θ)

open Classical in
/-- The L-shaped master objective (4), `z = c x + θ`; when no constraint (6) is present,
`θ` is ignored (p. 386) and the objective is `c x`. -/
noncomputable def LObj (inst : Instance n1 n2 m1 m2 K) (L : List ((Fin n1 → ℝ) × ℝ))
    (x : Fin n1 → ℝ) (θ : ℝ) : ℝ :=
  if L = [] then inst.c ⬝ᵥ x else inst.c ⬝ᵥ x + θ

/-- `(x, θ)` is an optimal solution of the L-shaped master (4)–(6). -/
def IsLOptimal (inst : Instance n1 n2 m1 m2 K) (F : List ((Fin n1 → ℝ) × ℝ))
    (L : List ((Fin n1 → ℝ) × ℝ)) (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  LFeasible inst F L x θ ∧
    ∀ x' θ', LFeasible inst F L x' θ' → LObj inst L x θ ≤ LObj inst L x' θ'

end MulticutLShaped.Bound


