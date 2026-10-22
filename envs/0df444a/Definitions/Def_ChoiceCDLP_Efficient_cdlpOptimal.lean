-- Prove2me | Definitions.Def_ChoiceCDLP_Efficient_cdlpOptimal
-- name    : ChoiceCDLP_Efficient_cdlpOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T07:12:09.58112+00:00
-- url     : https://prove2.me/theorems/355a9c93-7942-44bb-a067-cdcfaa03476a
-- title:
--   The choice-based deterministic LP (CDLP) (2): feasibility, objective and optimal solutions
-- statement:
--   **The choice-based deterministic linear program (CDLP).** Let $\lambda$ be the arrival probability per period, $c \in \mathbb{R}^m$ the leg capacities and $\tau$ the length of the horizon (the paper's $T$). The decision variable $t(S) \ge 0$ is the total (continuous) time during which offer set $S$ is offered. The CDLP is
--   $$V^{\mathrm{CDLP}} = \max \sum_{S \subseteq N} \lambda R(S)\, t(S) \quad\text{s.t.}\quad \sum_{S\subseteq N} \lambda Q(S)\, t(S) \le c,\qquad \sum_{S\subseteq N} t(S) \le \tau,\qquad t(S) \ge 0 \ \ \forall S \subseteq N .$$
--   A vector $t$ is **feasible** if it satisfies the three constraints (the first componentwise), and it is an **optimal solution** if it is feasible and its objective value is at least that of every feasible vector.
--
--   The CDLP replaces the stochastic demand of the network problem by its mean, with the offer times as decision variables; it has one variable per offer set.
--
--   **Formalization Note.** The horizon is named $\tau$ to avoid a clash with an offer set named $T$. `IsCDLPOptimal` says "$t$ is *an* optimal solution": several optimal solutions may exist, and none of them is required to be basic. The value $V^{\mathrm{CDLP}}$ is not defined separately; an optimal solution is characterized by comparison with every feasible vector.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 293, §3.2, CDLP (2)

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork

namespace ChoiceCDLP.Efficient

variable {m n : ℕ}

/-- Feasibility for the choice-based deterministic LP (CDLP) (2) (Liu–van Ryzin 2008, p. 293)
with arrival probability `lam`, capacity vector `c` and horizon `τ`:
`∑_S lam Q(S) t(S) ≤ c`, `∑_S t(S) ≤ τ`, `t(S) ≥ 0` for every `S ⊆ N`. -/
def IsCDLPFeasible (N : ChoiceNetwork m n) (lam : ℝ) (c : Fin m → ℝ) (τ : ℝ)
    (t : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ t S) ∧
  (∑ S, (lam * t S) • consumption N S) ≤ c ∧
  (∑ S, t S) ≤ τ

/-- The CDLP objective `∑_S lam R(S) t(S)` of (2). -/
def cdlpObjective (N : ChoiceNetwork m n) (lam : ℝ) (t : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S, lam * revenue N S * t S

/-- `t` is an optimal solution of the CDLP (2): it is feasible and its objective is at least that
of every feasible `t'`. -/
def IsCDLPOptimal (N : ChoiceNetwork m n) (lam : ℝ) (c : Fin m → ℝ) (τ : ℝ)
    (t : Finset (Fin n) → ℝ) : Prop :=
  IsCDLPFeasible N lam c τ t ∧
  ∀ t', IsCDLPFeasible N lam c τ t' → cdlpObjective N lam t' ≤ cdlpObjective N lam t

end ChoiceCDLP.Efficient


