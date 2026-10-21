-- Prove2me | Definitions.Def_CommittedLiquidity_BreakEven_Model
-- name    : CommittedLiquidity_BreakEven_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:45.56879+00:00
-- url     : https://prove2.me/theorems/24574482-2bde-42dc-b08d-ce90cb13d409
-- title:
--   §2.1, §3.1 and §3.3 — two-bank parameters, equilibrium prices and committed liquidity support
-- statement:
--   The paper considers two banks and two aggregate states, good $G$ and bad $B$. Each bank has equity $E$, retail deposits $F$, and wholesale debt $1-E-F$. Wholesale creditors receive the gross rate $r_D$ at maturity and the fraction $q r_D$ upon early withdrawal. Set
--
--   $$D_1=(1-E-F)q r_D,\qquad D_2=(1-E-F)r_D+F,\qquad \underline P=(\underline\theta_B+D_2)/2.$$
--
--   In state $s$, each bank's cash flow has the uniform law on $(\underline\theta_s,\bar\theta)$; the good-state prior is $\alpha$. The standing parameter range consists of $1-E-F>0$, $r_D>1$, $q<1$, $0<\underline\theta_B<\underline\theta_G$, $0<\alpha<1$, assumptions (1)–(3), and the upper-bound condition in footnote 29.
--
--   The limiting critical cash flow, posterior state weights, buyers' profit, regulator payoff and systemic-failure probability are the closed forms in §3.1 and §3.3. In particular, $V_A(P)$ is the state and run-count sum (22), and $\mathrm{SYS}(P)$ evaluates the paper's systemic-failure formula at $\theta^*(P)$.
--
--   These definitions supply a common statement layer for the market-price lemmas and Proposition 3.
--
--   **Formalization Note** The model represents the $\epsilon,\eta\to0$ regime directly. The global game is outside this definition. `IsBreakEven` includes $P\in[\underline P,qD_2)$ from Lemma 1. Uniform probabilities are unclipped and used on the economically valid interval. The extra positive-wholesale-debt condition makes the implicit financing convention explicit. At $P=0$ or $P=qD_1$, Lean's total real division gives a junk value; every theorem uses prices in the valid interval.
-- source:
--   Li & Ma, Contagious Bank Runs and Committed Liquidity Support, author's accepted manuscript (28 Oct 2021; WRAP 165968; published Management Science 2022, doi:10.1287/mnsc.2021.4258), pp. 6–7, 12–13, 15, 25–27 (PDF 7–8, 13–14, 16, 26–28), §2.1, (1)–(3), (6), (7), (20)–(23), footnote 29

import Mathlib

namespace CommittedLiquidity.BreakEven

/-- The two aggregate cash-flow states, §2.1. -/
inductive State | G | B
  deriving DecidableEq

instance : Fintype State := ⟨{.G, .B}, by intro x; cases x <;> simp⟩

/-- The primitive parameters of the two-bank model, §2.1. -/
structure Params where
  E : ℝ
  F : ℝ
  rD : ℝ
  q : ℝ
  θB : ℝ
  θG : ℝ
  θbar : ℝ
  α : ℝ

namespace Params

variable (p : Params)

/-- Total early repayment if all wholesale creditors withdraw. -/
def D1 : ℝ := (1 - p.E - p.F) * p.q * p.rD

/-- Total maturity repayment if no wholesale creditors withdraw. -/
def D2 : ℝ := (1 - p.E - p.F) * p.rD + p.F

/-- The lowest candidate break-even asset price. -/
noncomputable def Plow : ℝ := (p.θB + p.D2) / 2

def lower : State → ℝ
  | .G => p.θG
  | .B => p.θB

def prior : State → ℝ
  | .G => p.α
  | .B => 1 - p.α

/-- Model restrictions (1)–(3), the ranges in §2.1, footnote 29, and positive wholesale debt. -/
def Standing : Prop :=
  0 < 1 - p.E - p.F ∧ 1 < p.rD ∧ p.q < 1 ∧
  0 < p.θB ∧ p.θB < p.θG ∧ 0 < p.α ∧ p.α < 1 ∧
  (∀ s, p.lower s < p.D2) ∧
  p.D1 < p.F ∧
  1 / 2 + p.θG / (2 * p.D2) < p.q ∧
  p.F / (1 - p.D1 / p.Plow) < p.θbar

/-- The critical cash flow at committed asset price P in the ε, η → 0 limit. -/
noncomputable def θstar (P : ℝ) : ℝ :=
  (p.D2 - p.D1) / (1 - p.q * p.D1 / P)

/-- Prior and uniform-density factor in the buyers' posterior (6). -/
noncomputable def κ : ℝ :=
  p.α / (1 - p.α) * ((p.θbar - p.θB) / (p.θbar - p.θG)) ^ 2

/-- Posterior probability of aggregate state B after M bank runs, (6). -/
noncomputable def ωB (M : ℕ) (t : ℝ) : ℝ :=
  (t - p.θB) ^ M / ((t - p.θB) ^ M + p.κ * (t - p.θG) ^ M)

/-- Posterior probability of aggregate state G after M bank runs, (6). -/
noncomputable def ωG (M : ℕ) (t : ℝ) : ℝ :=
  p.κ * (t - p.θG) ^ M / ((t - p.θB) ^ M + p.κ * (t - p.θG) ^ M)

/-- Expected value of one unit of bank assets to the regulator in state s. -/
noncomputable def πs (s : State) (P : ℝ) : ℝ :=
  (p.lower s + p.θstar P) / 2 - P

/-- Buyers' expected profit for a given number M of runs, §3.3. -/
noncomputable def Pi (M : ℕ) (P : ℝ) : ℝ :=
  p.ωB M (p.θstar P) * p.πs .B P + p.ωG M (p.θstar P) * p.πs .G P

/-- A price in the equilibrium interval at which buyers observing M runs break even. -/
def IsBreakEven (M : ℕ) (P : ℝ) : Prop :=
  p.Plow ≤ P ∧ P < p.q * p.D2 ∧ p.Pi M P = 0

/-- Uniform conditional probability Pr(θ < t | s), used on the model's interior range. -/
noncomputable def probBelow (s : State) (t : ℝ) : ℝ :=
  (t - p.lower s) / (p.θbar - p.lower s)

/-- Expected regulator payoff, exactly the state/run-count sum (22). -/
noncomputable def VA (P : ℝ) : ℝ :=
  ∑ s : State, p.prior s * ∑ M ∈ Finset.Icc 1 2,
    p.probBelow s (p.θstar P) ^ M *
      (1 - p.probBelow s (p.θstar P)) ^ (2 - M) *
      (Nat.choose 2 M : ℝ) * (M : ℝ) * (p.D1 / P) * p.πs s P

/-- Systemic-failure probability when the critical cash flow is t. -/
noncomputable def sysOfTheta (t : ℝ) : ℝ :=
  p.α * ((t - p.θG) / (p.θbar - p.θG)) ^ 2 +
    (1 - p.α) * ((t - p.θB) / (p.θbar - p.θB)) ^ 2

/-- Systemic-failure probability at a committed asset price, §3.3. -/
noncomputable def SYS (P : ℝ) : ℝ := p.sysOfTheta (p.θstar P)

end Params

end CommittedLiquidity.BreakEven


