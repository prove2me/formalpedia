-- Prove2me | Definitions.Def_LaborWelfare_PoolSize_Setting
-- name    : LaborWelfare_PoolSize_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:20.567255+00:00
-- url     : https://prove2.me/theorems/5e45b71d-0ab3-47cc-9f09-f3cd9205a737
-- title:
--   §3, pp. 7–10 — agent best response (1), labor supply (2), uniform demand (3), delay (4), platform problem (7), effective wage, utilization, LW, N̲; p(D,S) (8), Π(D,S) (9), L(D,S)
-- statement:
--   This file sets up the on-demand service platform model of Benjaafar, Ding, Kong and Taylor (§3) and the reduced objects of their online appendix.
--
--   **Model.** The parameters are the maximum customer valuation $\bar v>0$ (valuations are uniform on $[0,\bar v]$, with cdf $G(x)=\max\{0,\min\{1,x/\bar v\}\}$), the market size $\Lambda>0$, the delay sensitivity $h\ge 0$, the delay exponent $\beta\ge 1$, and the distribution $F$ of the agents' opportunity-cost parameter $a$, a probability measure carried by $[\underline a,\bar a]$ with $0<\underline a\le\bar a$. Write $E[1/a]=\int a^{-1}\,dF(a)$. The labor pool size $N$ is a real number (the mass of a continuum of agents).
--
--   **Agents.** At wage $w$, demand $D$ and supply $S$, an agent with parameter $a$ supplies $x^*(a)=wD/(2aS)$, display (1); aggregating gives the labor supply equation (2),
--   $$S=\sqrt{wDN\,E[1/a]/2}.$$
--
--   **Customers and delay.** The delay is $W=(D/S)^\beta/(S-D)$, display (4), and demand is $D=\Lambda[1-G(p+hW)]$, display (3). A (strictly positive) **market equilibrium** at price $p$ and wage $w$ is a pair $(D,S)$ with $D>0$, $S>0$, (2), (3)–(4), and $D<S$ when $h>0$ (p. 9), resp. $D\le S$ when $h=0$ (the benchmark of p. 10, where demand is $\Lambda[1-G(p)]$).
--
--   **Platform.** An outcome $(p,w,D,S)$ is feasible if $p\ge 0$, $w\ge 0$ and $(D,S)$ is a market equilibrium at $(p,w)$; it is optimal if it maximizes the profit $(p-w)D$, problem (7), over all feasible outcomes. The effective wage is $w_e=wD/S$ and the agent utilization is $\rho=D/S$. Total labor welfare is
--   $$LW=N\int\Big[\frac{wD}{S}x^*(a)-a\,x^*(a)^2\Big]dF(a),$$
--   and average labor welfare is $\overline{LW}=LW/N$. The lower end of the labor-pool regime is $\underline N=0$ for $\beta>1$ and $\underline N=8h/(\bar v^2E[1/a])$ for $\beta=1$ (p. OA3).
--
--   **Reduced objects (online appendix).** $p(D,S)=\bar v-\bar vD/\Lambda-h(D/S)^\beta/(S-D)$, display (8); $\Pi(D,S)=p(D,S)D-2S^2/(NE[1/a])$, display (9); $L(D,S)=\bar v-2\bar vD/\Lambda-h(D/S)^\beta((\beta+1)S-\beta D)/(S-D)^2$, the partial derivative $\partial\Pi/\partial D$ (p. OA2); and a function $\tilde D$ is a revenue-maximizing demand if, for every $S>0$, $\tilde D(S)\in[0,S)$ maximizes $\Pi(\cdot,S)$ over $[0,S)$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Λ is `Lam`, β is `beta`, $\underline a,\bar a$ are `alo`, `ahi`. The density $f$ of the page is not required: only $E[1/a]$ enters any result, and $\underline a>0$ (implicit on the page, since $x^*(a)$ and $E[1/a]$ need it) is part of the standing assumptions `Model.Std`. Powers $(D/S)^\beta$ are real powers (`Real.rpow`). The case $h=0$ selects the benchmark capacity constraint $D\le S$ (with $D<S$ nothing would be optimal there). The page's optimum $(p^*,w^*,D^*,S^*)$ is not defined by choice; statements quantify over optimal outcomes.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), §3, pp. 7–10 (displays (1)–(4), (7), LW, LW̄), and Online Appendix Part A, pp. OA1–OA3 ((8), (9), D̃(S), L(D,S), N̲)

import Mathlib

namespace LaborWelfare.PoolSize

open MeasureTheory

/-- The model primitives of §3 (pp. 7–10): the maximum valuation `vbar` (v̄), the market size `Lam` (Λ),
the delay sensitivity `h`, the delay exponent `beta` (β), the bounds `alo`, `ahi` (a̲, ā) of the
opportunity-cost parameter, and its distribution `F`. -/
structure Model where
  vbar : ℝ
  Lam : ℝ
  h : ℝ
  beta : ℝ
  alo : ℝ
  ahi : ℝ
  F : Measure ℝ

/-- The standing assumptions of §3: v̄ > 0, Λ > 0, h ≥ 0, β ≥ 1, `F` a probability measure carried
by `[a̲, ā]` with `0 < a̲ ≤ ā`. -/
def Model.Std (M : Model) : Prop :=
  0 < M.vbar ∧ 0 < M.Lam ∧ 0 ≤ M.h ∧ 1 ≤ M.beta ∧ IsProbabilityMeasure M.F ∧
    0 < M.alo ∧ M.alo ≤ M.ahi ∧ M.F (Set.Icc M.alo M.ahi)ᶜ = 0

/-- `E[1/a]`. -/
noncomputable def Einv (M : Model) : ℝ := ∫ a, a⁻¹ ∂M.F

/-- The cdf of the uniform distribution on `[0, v̄]`. -/
noncomputable def G (M : Model) (x : ℝ) : ℝ := max 0 (min 1 (x / M.vbar))

/-- The delay measure (4): `W = (D/S)^β / (S - D)`. -/
noncomputable def delay (M : Model) (D S : ℝ) : ℝ := (D / S) ^ M.beta / (S - D)

/-- The agent's best response (1): `x*(a) = w D / (2 a S)`. -/
noncomputable def xstar (w D S a : ℝ) : ℝ := w * D / (2 * a * S)

/-- A strictly positive equilibrium in demand and labor supply `(D, S)` at price `p`, wage `w` and
labor pool size `N`: (2), (3) with (4), and `D < S` for `h > 0` (p. 9); for `h = 0` (p. 10) the
conditions are (2), `D = Λ[1 - G(p)]` and `D ≤ S`. -/
noncomputable def IsMarketEq (M : Model) (N p w D S : ℝ) : Prop :=
  0 < D ∧ 0 < S ∧ (if M.h = 0 then D ≤ S else D < S) ∧
    S = Real.sqrt (w * D * N * Einv M / 2) ∧
    D = M.Lam * (1 - G M (p + M.h * delay M D S))

/-- An outcome: price, wage, demand, labor supply. -/
structure Outcome where
  p : ℝ
  w : ℝ
  D : ℝ
  S : ℝ

/-- Feasibility for the platform's problem (7): `p ≥ 0`, `w ≥ 0`, and a market equilibrium. -/
def IsFeasible (M : Model) (N : ℝ) (o : Outcome) : Prop :=
  0 ≤ o.p ∧ 0 ≤ o.w ∧ IsMarketEq M N o.p o.w o.D o.S

/-- The platform's profit (7): `(p - w) D`. -/
def profit (o : Outcome) : ℝ := (o.p - o.w) * o.D

/-- An optimal outcome of the platform's problem (7). -/
def IsOptimal (M : Model) (N : ℝ) (o : Outcome) : Prop :=
  IsFeasible M N o ∧ ∀ o' : Outcome, IsFeasible M N o' → profit o' ≤ profit o

/-- The effective wage `w_e = w D / S`. -/
noncomputable def effWage (o : Outcome) : ℝ := o.w * o.D / o.S

/-- Agent utilization `ρ = D / S`. -/
noncomputable def util (o : Outcome) : ℝ := o.D / o.S

/-- Total labor welfare (p. 10): `LW = N ∫ [(w D/S) x*(a) - a x*(a)²] dF(a)`. -/
noncomputable def laborWelfare (M : Model) (N : ℝ) (o : Outcome) : ℝ :=
  N * ∫ a, (effWage o * xstar o.w o.D o.S a - a * (xstar o.w o.D o.S a) ^ 2) ∂M.F

/-- Average labor welfare `LW̄ = LW / N`. -/
noncomputable def avgLaborWelfare (M : Model) (N : ℝ) (o : Outcome) : ℝ :=
  laborWelfare M N o / N

/-- The lower end `N̲` of the labor-pool regime (p. OA3): `0` for `β > 1`, `8h/(v̄² E[1/a])` for `β = 1`. -/
noncomputable def Nlow (M : Model) : ℝ :=
  if M.beta = 1 then 8 * M.h / (M.vbar ^ 2 * Einv M) else 0

/-- The price as a function of demand and supply (8). -/
noncomputable def priceDS (M : Model) (D S : ℝ) : ℝ :=
  M.vbar - M.vbar * D / M.Lam - M.h * delay M D S

/-- The platform's profit as a function of demand and supply (9). -/
noncomputable def PiDS (M : Model) (N D S : ℝ) : ℝ :=
  priceDS M D S * D - 2 * S ^ 2 / (N * Einv M)

/-- `L(D, S) = ∂Π(D, S)/∂D` as printed on p. OA2. -/
noncomputable def Lfoc (M : Model) (D S : ℝ) : ℝ :=
  M.vbar - 2 * M.vbar * D / M.Lam -
    M.h * (D / S) ^ M.beta * ((M.beta + 1) * S - M.beta * D) / (S - D) ^ 2

/-- `Dt` is a revenue-maximizing demand `D̃(S) ∈ arg max_{D ∈ [0, S)} Π(D, S)` for every `S > 0`. -/
def IsDtilde (M : Model) (N : ℝ) (Dt : ℝ → ℝ) : Prop :=
  ∀ S, 0 < S → Dt S ∈ Set.Ico 0 S ∧ ∀ D ∈ Set.Ico 0 S, PiDS M N D S ≤ PiDS M N (Dt S) S

end LaborWelfare.PoolSize


