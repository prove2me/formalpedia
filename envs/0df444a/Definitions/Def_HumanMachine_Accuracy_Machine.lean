-- Prove2me | Definitions.Def_HumanMachine_Accuracy_Machine
-- name    : HumanMachine_Accuracy_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:23:49.99329+00:00
-- url     : https://prove2.me/theorems/4e712255-c671-45ca-a6c6-19298f03de4a
-- title:
--   §3.2, §5.1 — the machine's information $X_1$, the Bayes-updated beliefs $\mu^x$ and the machine-assisted accuracy $A^\star_m$ and value $V^\star_m$
-- statement:
--   The information relevant to the state is aggregated into two binary random variables: $X_1$, which both the machine and the DM can evaluate, and $X_2$, which only the DM can assess. Their realizations are $x_1,x_2\in\{-,+\}$, and the state is good if and only if both are positive: $\omega=g\iff x_1=x_2=+$. The DM's **prior** on $(X_1,X_2)$ is a probability distribution $\pi(x_1,x_2)$ with $\pi(x_1,x_2)>0$ for all four realizations, so that her prior belief in the good state is $\mu=\pi(+,+)$.
--
--   The machine reveals $x_1$ at no cognitive cost. For each output $x\in\{-,+\}$ the DM's **updated belief** is given by Bayes' rule,
--   $$\mu^x=P(\omega=g\mid X_1=x)=\frac{P(\omega=g,\,X_1=x)}{P(X_1=x)},\qquad P(X_1=x)=\pi(x,+)+\pi(x,-).$$
--   After observing $x$ the DM solves her decision problem with prior $\mu^x$. The **machine-assisted accuracy** and **expected value** are the ex-ante expectations over the machine's output,
--   $$A^\star_m=\sum_{x\in\{-,+\}}P(X_1=x)\,A^\star(\mu^x),\qquad V^\star_m=\sum_{x\in\{-,+\}}P(X_1=x)\,V^\star(\mu^x).$$
--
--   These are the quantities that Lemma 2 rewrites and that Proposition 1 compares with $A^\star(\mu)$ and $V^\star(\mu)$.
--
--   **Formalization Note** $-$ and $+$ are `false` and `true`; the prior is a function `π : Bool → Bool → ℝ` (no `open Real`, so `π` is a variable, not the circle constant). The beliefs $\mu^x$ are defined by Bayes' rule, not by the formulas $\mu^-=0$, $\mu^+=\mu/(\mu+\pi(+,-))$ of (3), which are a theorem; the posterior is $0$ when $P(X_1=x)=0$, a case a positive prior excludes. $A^\star_m$ and $V^\star_m$ are defined as expectations, not by the right-hand sides of Lemma 2.
-- source:
--   Boyacı, Canyakmaz & de Véricourt, Human and Machine: The Impact of Machine Input on Decision-Making Under Cognitive Limitations, ESMT Working Paper 20-02 (Nov. 30, 2020), p. 10, §3.2; p. 17, §5.1

import Mathlib
import Definitions.Def_HumanMachine_Accuracy_DecisionModel

namespace HumanMachine.Accuracy

/-- A prior `π` on the realizations `(x₁, x₂) ∈ {−, +}²` of the machine-observable information
`X₁` and the DM-only information `X₂` (§3.2, p. 10), encoded with `true = +` and `false = −`:
every entry is positive and the four entries sum to one. -/
def IsPrior (π : Bool → Bool → ℝ) : Prop :=
  (∀ x₁ x₂, 0 < π x₁ x₂) ∧ π true true + π true false + π false true + π false false = 1

/-- The state of the world is good iff all information is positive: `ω = g ⇔ x₁ = x₂ = +`. -/
def isGood (x₁ x₂ : Bool) : Bool := x₁ && x₂

/-- The DM's prior belief that the state is good, `μ = P(ω = g) = π(+, +)` in general form
`∑_{x₁, x₂ : ω = g} π(x₁, x₂)`. -/
noncomputable def priorGood (π : Bool → Bool → ℝ) : ℝ :=
  ∑ x₁ : Bool, ∑ x₂ : Bool, if isGood x₁ x₂ then π x₁ x₂ else 0

/-- The probability `P(X₁ = x)` that the machine outputs `x`. -/
noncomputable def probOut (π : Bool → Bool → ℝ) (x : Bool) : ℝ := ∑ x₂ : Bool, π x x₂

/-- The joint probability `P(ω = g, X₁ = x)`. -/
noncomputable def jointGood (π : Bool → Bool → ℝ) (x : Bool) : ℝ :=
  ∑ x₂ : Bool, if isGood x x₂ then π x x₂ else 0

/-- The DM's updated belief `μ^x = P(ω = g | X₁ = x)` after the machine outputs `x`, by Bayes'
rule (§3.2, p. 10). (`0` if `P(X₁ = x) = 0`, which a positive prior excludes.) -/
noncomputable def posterior (π : Bool → Bool → ℝ) (x : Bool) : ℝ :=
  jointGood π x / probOut π x

/-- `A⋆_m`: the DM's ex-ante decision accuracy in the presence of the machine (§3.2, §5.1):
the expectation over the machine output `x` of the optimal accuracy `A⋆(μ^x)` at the updated
belief, `P(X₁ = +) A⋆(μ⁺) + P(X₁ = −) A⋆(μ⁻)`. -/
noncomputable def AStarM (lam : ℝ) (π : Bool → Bool → ℝ) : ℝ :=
  probOut π true * AStar lam (posterior π true) + probOut π false * AStar lam (posterior π false)

/-- `V⋆_m`: the DM's ex-ante optimal expected value in the presence of the machine (§3.2, §5.1),
`P(X₁ = +) V⋆(μ⁺) + P(X₁ = −) V⋆(μ⁻)`. -/
noncomputable def VStarM (lam : ℝ) (π : Bool → Bool → ℝ) : ℝ :=
  probOut π true * VStar lam (posterior π true) + probOut π false * VStar lam (posterior π false)

end HumanMachine.Accuracy


