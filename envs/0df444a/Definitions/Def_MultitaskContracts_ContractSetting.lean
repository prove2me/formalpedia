-- Prove2me | Definitions.Def_MultitaskContracts_ContractSetting
-- name    : MultitaskContracts_ContractSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:30:45.549539+00:00
-- url     : https://prove2.me/theorems/fa898d54-95e6-46d6-a2d1-1fc7b89862d9
-- title:
--   Finite hidden-action principal–agent setting: best response, $\mathrm{OPT}_{\mathrm{FixedBudget}}$, $\mathrm{OPT}_{\mathrm{MinPay}}$, $\mathrm{OPT}_{\mathrm{MinBudget}}$
-- statement:
--   A **hidden-action principal–agent setting** consists of a set $A$ of actions, a finite set $\Omega$ of outcomes, outcome weights $P_a(\omega)$ for each action $a$ (the probability of outcome $\omega$ when the agent takes action $a$) and a cost $c(a)$ for each action. A **contract** is a payment scheme $t:\Omega\to\mathbb R$; under action $a$ its expected payment is $\mathbb E_{\omega\sim P_a}[t(\omega)]=\sum_\omega P_a(\omega)\,t(\omega)$.
--
--   1. A contract $t$ **implements** an action $a$ if $a$ maximizes the agent's expected utility, i.e. for every action $a'$,
--   $$\mathbb E_{P_a}[t]-c(a)\ \ge\ \mathbb E_{P_{a'}}[t]-c(a').$$
--   Ties are broken in favour of the principal, so $a$ only needs to be one of the maximizers.
--   2. For a class $\mathcal T$ of contracts, a target action $a$ and a budget $B$, the **Budgeted Min-Pay optimum** is
--   $$\mathrm{OPT}^{\mathcal T}_{\mathrm{FixedBudget}}(B)=\min\bigl\{\mathbb E_{P_a}[t]\ :\ t\in\mathcal T,\ t \text{ implements } a,\ t(\omega)\le B\ \forall\omega\bigr\},$$
--   with value $\infty$ when no contract is feasible.
--   3. The **Min-Pay optimum** is $\mathrm{OPT}^{\mathcal T}_{\mathrm{MinPay}}=\lim_{B\to\infty}\mathrm{OPT}^{\mathcal T}_{\mathrm{FixedBudget}}(B)$.
--   4. The **Min-Budget optimum** is $\mathrm{OPT}^{\mathcal T}_{\mathrm{MinBudget}}=\min\{B\ge 0:\mathrm{OPT}^{\mathcal T}_{\mathrm{FixedBudget}}(B)<\infty\}$.
--
--   This is the general contract-design layer of the mission; the multitask model specializes it with strategies and performances being subsets of the task set.
--
--   **Formalization Note** Optima take values in $[0,\infty]$ (`ℝ≥0∞`). The Budgeted Min-Pay optimum is the infimum of the expected payments over the feasible contracts (the minimum whenever it exists, $\infty$ on an empty feasible set); expected payments are embedded by `ENNReal.ofReal`, which loses nothing for nonnegative contracts and weights. Because $B\mapsto\mathrm{OPT}_{\mathrm{FixedBudget}}(B)$ is antitone, the limit defining Min-Pay is the infimum over budgets $B\ge0$, which is how it is defined. The Min-Budget optimum is the infimum in $[0,\infty]$ of the feasible budgets $B\ge0$ ($\infty$ if there is none). No assumption on $P$ or $c$ is bundled.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §2, eqs. (4)–(7), p.7 (PDF p.9)

import Mathlib

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- A **finite hidden-action principal–agent setting**: an agent picks an action `a : A` at cost
`cost a`, which induces the outcome weights `P a ω` on a finite outcome space `Ω`; the principal
observes only the outcome and pays according to a contract `t : Ω → ℝ`.
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), §2, pp.6–7 (PDF 8–9), the general form of the
best response (4) and of the program (5)–(7).

**Formalization Note.** This is the general object; the multitask model `Instance` (strategies
and performances `Finset K`) specializes it. No assumption is bundled: `P a` is a probability
distribution and costs are as the multitask model requires only through the fields of
`Instance`. -/
structure ContractSetting (A Ω : Type*) [Fintype Ω] where
  /-- `P a ω`: probability of outcome `ω` under action `a`. -/
  P : A → Ω → ℝ
  /-- `cost a`: the agent's cost of action `a`. -/
  cost : A → ℝ

namespace ContractSetting

variable {A Ω : Type*} [Fintype Ω] (M : ContractSetting A Ω)

/-- Expected payment `E_{ω∼P_a}[t(ω)] = ∑_ω P_a(ω) t(ω)` of contract `t` under action `a`. -/
def expect (a : A) (t : Ω → ℝ) : ℝ :=
  ∑ ω, M.P a ω * t ω

/-- `t` **implements** `a` (eq. (4), p.7): `a` maximizes the agent's expected utility
`E_{P_{a'}}[t] − cost a'` over all actions `a'`. Ties are broken in favour of the principal, so
`a` only needs to be *a* maximizer; this is the (IC) constraint of (5) for target `a`. -/
def Implements (t : Ω → ℝ) (a : A) : Prop :=
  ∀ a', M.expect a' t - M.cost a' ≤ M.expect a t - M.cost a

/-- `OPT^T_FixedBudget(B)` (program (5), p.7) for target action `a`: the least expected payment
`E_{P_a}[t]` over contracts `t ∈ T` that implement `a` (IC) and pay at most `B` on every outcome
(BC); `∞` when there is no such contract.

**Formalization Note.** The value is in `ℝ≥0∞`: the infimum of `ENNReal.ofReal (E_{P_a}[t])` over
the feasible set, which is `⊤` exactly when (5) is infeasible and equals the minimum of (5)
whenever that minimum exists. For the classes of the paper (`T ⊆ ℝ^Ω_{≥0}`) and nonnegative
`P a`, `E_{P_a}[t] ≥ 0`, so `ofReal` loses nothing. -/
noncomputable def optFixedBudget (T : Set (Ω → ℝ)) (a : A) (B : ℝ) : ℝ≥0∞ :=
  ⨅ t ∈ {t : Ω → ℝ | t ∈ T ∧ M.Implements t a ∧ ∀ ω, t ω ≤ B}, ENNReal.ofReal (M.expect a t)

/-- `OPT^T_MinPay := lim_{B→∞} OPT^T_FixedBudget(B)` (eq. (6), p.7).

**Formalization Note.** `B ↦ OPT^T_FixedBudget(B)` is antitone (a larger budget enlarges the
feasible set), so the limit exists in `ℝ≥0∞` and equals the infimum over budgets `B ≥ 0`; that
infimum is the definition. -/
noncomputable def optMinPay (T : Set (Ω → ℝ)) (a : A) : ℝ≥0∞ :=
  ⨅ (B : ℝ) (_ : 0 ≤ B), M.optFixedBudget T a B

/-- `OPT^T_MinBudget := min {B ≥ 0 : OPT^T_FixedBudget(B) < ∞}` (eq. (7), p.7).

**Formalization Note.** The value is the infimum in `ℝ≥0∞` of the budgets `B ≥ 0` (embedded by
`ofReal`) at which (5) is feasible; it equals the minimum whenever the minimum exists and is `⊤`
when no budget is feasible. -/
noncomputable def optMinBudget (T : Set (Ω → ℝ)) (a : A) : ℝ≥0∞ :=
  sInf {x : ℝ≥0∞ | ∃ B : ℝ, 0 ≤ B ∧ x = ENNReal.ofReal B ∧ M.optFixedBudget T a B < ⊤}

end ContractSetting

end MultitaskContracts


