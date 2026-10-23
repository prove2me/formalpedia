-- Prove2me | Definitions.Def_InfoNudge_Cutoff_Model
-- name    : InfoNudge_Cutoff_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:10:00.742628+00:00
-- url     : https://prove2.me/theorems/7b29717d-d070-48af-8565-d7518dd98f0f
-- title:
--   §2.1–3.4.2, eqs. (1)–(16), pp. 7–16 — present-biased consumer, persuasion mechanisms, incentive compatibility (6)–(7), objective (8), cutoff mechanisms (10)
-- statement:
--   This file fixes the model of Mariotti, Schweizer, Szech and von Wangenheim, *Information Nudges and Self-Control*.
--
--   **Parameters.** A decision maker has present-bias parameter $\beta\in(0,1)$, per-period discount factor $\delta\in(0,1]$ and faces a cost $C$ with $\beta\delta^2C>1$. His risk type $\theta$ is distributed according to a prior $P$, a probability distribution over $[0,1]$, with cumulative distribution function $F(t)=P[\theta\le t]$ and left limits $F(t^-)=P[\theta<t]$. These are the standing assumptions of §2.
--
--   **Payoffs and cutoffs.** For consumption decisions $x_0,x_1\in\{0,1\}$ the date-0 and date-1 utilities are
--   $$U_0(x_0,x_1,\theta)=x_0(1-\beta\delta^2\theta C)+x_1\beta\delta(1-\delta^2\theta C),\qquad U_1(x_0,x_1,\theta)=-x_0\beta\delta\theta C+x_1(1-\beta\delta^2\theta C),$$
--   and the two cutoffs are
--   $$t^a=\frac{1}{\beta\delta^2C},\qquad t^h=\frac{1+\beta\delta}{1+\delta}\,t^a.$$
--
--   **The intrapersonal game.** Given a mean posterior belief $\hat\theta$, the date-0 self chooses $x_0$ and the date-1 self, having observed $x_0$, chooses $x_1$; payoffs are $U_0,U_1$ evaluated at $\hat\theta$. A (pure-strategy) subgame-perfect equilibrium is a pair $(a_0,s_1)$ where $s_1(x_0)$ maximizes $U_1(x_0,\cdot,\hat\theta)$ at both nodes and $a_0$ maximizes $U_0(x_0,s_1(x_0),\hat\theta)$. It is *efficient* if no other subgame-perfect equilibrium gives both selves at least as much and one of them strictly more.
--
--   **Mechanisms and incentive compatibility.** A persuasion mechanism is a measurable $\pi:\mathbb R\to[0,1]$, the probability of recommending to consume. It is incentive-compatible if
--   $$\frac{E[\theta\pi(\theta)]}{E[\pi(\theta)]}<t^a\quad(6),\qquad \frac{E[\theta(1-\pi(\theta))]}{E[1-\pi(\theta)]}\ge t^a\quad(7),$$
--   where a constraint whose denominator vanishes is emptily satisfied. The design objective (8) is $t^hE[\pi(\theta)]-E[\theta\pi(\theta)]$, and $\pi$ is *optimal* if it is an incentive-compatible mechanism whose objective is at least that of every incentive-compatible mechanism.
--
--   **Cutoff mechanisms.** For $\gamma\in[0,1)$ let $t_\gamma=\inf\{\theta:F(\theta)>\gamma\}$ and
--   $$\pi^*_\gamma(\theta)=1_{\{\theta<t_\gamma\}}+\frac{\gamma-F(t_\gamma^-)}{F(t_\gamma)-F(t_\gamma^-)}\,1_{\{\theta=t_\gamma\}}\qquad(10)$$
--   with $0/0=1$; for $\gamma\ge1$, $\pi^*_\gamma\equiv1$ (the convention $\inf\emptyset=\infty$).
--
--   **Conditions.** Assumption 1 is $P[\theta\le t^h]>0$ and $P[\theta>t^a]>0$. Condition (15) is $E[\theta\mid\theta>t^h]\ge t^a$; equation (16) for $\pi^*_\gamma$ is $E[\theta(1-\pi^*_\gamma(\theta))]/E[1-\pi^*_\gamma(\theta)]=t^a$. The left-hand side of (12) is $E[\theta(1-\pi^*_\gamma(\theta))]/(1-\gamma)$, and $\bar\theta$ is the supremum of the support of $P$, i.e. the least $t$ with $P[\theta>t]=0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Types are real numbers and $P$ is a measure on $\mathbb R$ (with $P([0,1]^c)=0$); mechanisms are defined on all of $\mathbb R$ rather than on the support $\Theta$, which changes nothing since values off $[0,1]$ carry no mass. Expectations are Bochner integrals. Constraints (6), (7), condition (15) and equation (16) are stored cross-multiplied (by $E[\pi]$, $E[1-\pi]$, $P[\theta>t^h]$, $E[1-\pi^*_\gamma]$), so no division by a possibly zero quantity occurs; "$\pi=0$ $P$-a.s." is encoded as $E[\pi]=0$, which is equivalent because $\pi\ge0$. Strategies in the intrapersonal game are pure, and payoffs are evaluated at the mean belief $\hat\theta$, which is exact because $U_0,U_1$ are affine in $\theta$.
-- source:
--   Mariotti, Schweizer, Szech & von Wangenheim, Information Nudges and Self-Control, KIT Working Paper Series in Economics No. 119 (November 2018), pp. 7–16, §2.1–2.4, §3.2–3.4.2, eqs. (1)–(16), Assumption 1

import Mathlib

namespace InfoNudge.Cutoff

open MeasureTheory

/-- The data of the model of §2 (pp. 7–8): the present-bias parameter `β`, the per-period
discount factor `δ`, the cost `C`, and the prior `P` of the risk type `θ`. -/
structure Params where
  β : ℝ
  δ : ℝ
  C : ℝ
  P : Measure ℝ

/-- Standing assumptions of §2.1–2.2 (p. 7): `β ∈ (0,1)`, `δ ∈ (0,1]`, `βδ²C > 1`, and the prior
`P` is a probability distribution over `[0,1]`. -/
def Standing (M : Params) : Prop :=
  0 < M.β ∧ M.β < 1 ∧ 0 < M.δ ∧ M.δ ≤ 1 ∧ 1 < M.β * M.δ ^ 2 * M.C ∧
    IsProbabilityMeasure M.P ∧ M.P (Set.Icc (0 : ℝ) 1)ᶜ = 0

/-- The cutoff `tᵃ = 1/(βδ²C)` of (3). -/
noncomputable def ta (M : Params) : ℝ := 1 / (M.β * M.δ ^ 2 * M.C)

/-- The cutoff `tʰ = (1 + βδ)/(1 + δ) · tᵃ` of (4). -/
noncomputable def th (M : Params) : ℝ := (1 + M.β * M.δ) / (1 + M.δ) * ta M

/-- The date-0 utility (1): `U₀(x₀, x₁, θ) = x₀(1 − βδ²θC) + x₁βδ(1 − δ²θC)`. -/
def U0 (M : Params) (x0 x1 θ : ℝ) : ℝ :=
  x0 * (1 - M.β * M.δ ^ 2 * θ * M.C) + x1 * (M.β * M.δ * (1 - M.δ ^ 2 * θ * M.C))

/-- The date-1 utility (2): `U₁(x₀, x₁, θ) = −x₀βδθC + x₁(1 − βδ²θC)`. -/
def U1 (M : Params) (x0 x1 θ : ℝ) : ℝ :=
  -(x0 * (M.β * M.δ * θ * M.C)) + x1 * (1 - M.β * M.δ ^ 2 * θ * M.C)

/-- A consumption decision as a number: `true` (consume) is `1`, `false` (abstain) is `0`. -/
def act (b : Bool) : ℝ := if b then 1 else 0

/-- Pure-strategy subgame-perfect equilibrium of the intrapersonal game of §2.4 at mean posterior
belief `θh`: the date-0 self plays `a0`, the date-1 self plays `s1 x0` after observing `x0`.
The date-1 self best-responds at both of its decision nodes, and the date-0 self best-responds
to `s1`. -/
def IsSPE (M : Params) (θh : ℝ) (a0 : Bool) (s1 : Bool → Bool) : Prop :=
  (∀ x0 x1 : Bool, U1 M (act x0) (act x1) θh ≤ U1 M (act x0) (act (s1 x0)) θh) ∧
    ∀ x0 : Bool, U0 M (act x0) (act (s1 x0)) θh ≤ U0 M (act a0) (act (s1 a0)) θh

/-- An efficient subgame-perfect equilibrium: an SPE whose equilibrium payoff pair `(U₀, U₁)` is
not Pareto-dominated by the payoff pair of any other SPE. -/
def IsEfficientSPE (M : Params) (θh : ℝ) (a0 : Bool) (s1 : Bool → Bool) : Prop :=
  IsSPE M θh a0 s1 ∧
    ¬ ∃ (b0 : Bool) (r1 : Bool → Bool), IsSPE M θh b0 r1 ∧
      U0 M (act a0) (act (s1 a0)) θh ≤ U0 M (act b0) (act (r1 b0)) θh ∧
      U1 M (act a0) (act (s1 a0)) θh ≤ U1 M (act b0) (act (r1 b0)) θh ∧
      (U0 M (act a0) (act (s1 a0)) θh < U0 M (act b0) (act (r1 b0)) θh ∨
        U1 M (act a0) (act (s1 a0)) θh < U1 M (act b0) (act (r1 b0)) θh)

/-- A persuasion mechanism (5): a measurable map `π` giving, for each type `θ`, the probability
`π θ ∈ [0,1]` of recommending to consume. -/
def IsMechanism (π : ℝ → ℝ) : Prop :=
  Measurable π ∧ ∀ θ, π θ ∈ Set.Icc (0 : ℝ) 1

/-- Incentive compatibility (6)–(7), cross-multiplied, with the convention that an undefined
constraint (`π = 0` resp. `π = 1` `P`-a.s.) is emptily satisfied:
(6) `E[θπ(θ)] < tᵃ E[π(θ)]` unless `E[π(θ)] = 0`;
(7) `E[θ(1 − π(θ))] ≥ tᵃ E[1 − π(θ)]` unless `E[1 − π(θ)] = 0`. -/
def IC (M : Params) (π : ℝ → ℝ) : Prop :=
  ((∫ θ, π θ ∂M.P) = 0 ∨ (∫ θ, θ * π θ ∂M.P) < ta M * ∫ θ, π θ ∂M.P) ∧
    ((∫ θ, (1 - π θ) ∂M.P) = 0 ∨ ta M * (∫ θ, (1 - π θ) ∂M.P) ≤ ∫ θ, θ * (1 - π θ) ∂M.P)

/-- The objective of (8): `tʰ E[π(θ)] − E[θπ(θ)]`. -/
noncomputable def objective (M : Params) (π : ℝ → ℝ) : ℝ :=
  th M * (∫ θ, π θ ∂M.P) - ∫ θ, θ * π θ ∂M.P

/-- `π` solves the optimal-design problem (8): it is an incentive-compatible mechanism whose
objective is at least that of every incentive-compatible mechanism. -/
def IsOptimal (M : Params) (π : ℝ → ℝ) : Prop :=
  IsMechanism π ∧ IC M π ∧ ∀ π' : ℝ → ℝ, IsMechanism π' → IC M π' → objective M π' ≤ objective M π

/-- The cumulative distribution function `F(t) = P[θ ≤ t]`. -/
noncomputable def F (M : Params) (t : ℝ) : ℝ := M.P.real (Set.Iic t)

/-- The left limit `F(t⁻) = P[θ < t]`. -/
noncomputable def Fminus (M : Params) (t : ℝ) : ℝ := M.P.real (Set.Iio t)

/-- The cutoff `t_γ = inf {θ : F(θ) > γ}` of Lemma 2 (used for `γ < 1`, where the set is
nonempty and bounded below). -/
noncomputable def tGamma (M : Params) (γ : ℝ) : ℝ := sInf {θ : ℝ | γ < F M θ}

/-- The cutoff mechanism (10):
`π*_γ(θ) = 1{θ < t_γ} + (γ − F(t_γ⁻))/(F(t_γ) − F(t_γ⁻)) · 1{θ = t_γ}`, with `0/0 = 1`, and
`π*_γ ≡ 1` when `γ ≥ 1` (the convention `inf ∅ = ∞`). -/
noncomputable def cutoffMech (M : Params) (γ : ℝ) (θ : ℝ) : ℝ :=
  if 1 ≤ γ then 1
  else (if θ < tGamma M γ then 1 else 0) +
    (if θ = tGamma M γ then
      (if F M (tGamma M γ) = Fminus M (tGamma M γ) then 1
        else (γ - Fminus M (tGamma M γ)) / (F M (tGamma M γ) - Fminus M (tGamma M γ)))
    else 0)

/-- Assumption 1 (p. 13): `P[θ ≤ tʰ] > 0` and `P[θ > tᵃ] > 0`. -/
def Assumption1 (M : Params) : Prop :=
  0 < M.P.real (Set.Iic (th M)) ∧ 0 < M.P.real (Set.Ioi (ta M))

/-- Condition (15), `E[θ | θ > tʰ] ≥ tᵃ`, multiplied through by `P[θ > tʰ]`:
`tᵃ P[θ > tʰ] ≤ E[θ 1{θ > tʰ}]`. -/
def Cond15 (M : Params) : Prop :=
  ta M * M.P.real (Set.Ioi (th M)) ≤ ∫ θ in Set.Ioi (th M), θ ∂M.P

/-- Equation (16) for the cutoff mechanism `π*_γ`, cross-multiplied:
`E[θ(1 − π*_γ(θ))] = tᵃ E[1 − π*_γ(θ)]`. -/
def Eq16 (M : Params) (γ : ℝ) : Prop :=
  (∫ θ, θ * (1 - cutoffMech M γ θ) ∂M.P) = ta M * ∫ θ, (1 - cutoffMech M γ θ) ∂M.P

/-- The left-hand side of (12), `E[θ(1 − π*_γ(θ))] / (1 − γ)`, the mean type given a
recommendation to abstain (meaningful for `γ < 1`). -/
noncomputable def abstainMean (M : Params) (γ : ℝ) : ℝ :=
  (∫ θ, θ * (1 - cutoffMech M γ θ) ∂M.P) / (1 - γ)

/-- `θ̄`, the supremum of the support of `P`: the least `t` with `P[θ > t] = 0`. -/
noncomputable def thetaBar (M : Params) : ℝ := sInf {t : ℝ | M.P (Set.Ioi t) = 0}

end InfoNudge.Cutoff


