-- Prove2me | Definitions.Def_DemandResponse_SecondBest_Hamiltonian
-- name    : DemandResponse_SecondBest_Hamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:25:13.011953+00:00
-- url     : https://prove2.me/theorems/52ba70b9-ea78-4ab5-b5a5-f7e72c68ef59
-- title:
--   Model parameters, effort boxes $A$, $B$, costs $c_1$, $c_2$, Hamiltonians $H_m$, $H_v$ (2.9), best responses $\hat a$, $\hat b$, $f_0$ (A.10) and $F_0$
-- statement:
--   This file fixes the deterministic data of the electricity demand-response model of Aïd, Possamaï and Touzi.
--
--   **Parameters.** Integers $N, d \ge 0$ count the consumer's usages for the mean effort and for the volatility effort. The model carries cost parameters $\mu\in(0,\infty)^N$, $\lambda\in(0,\infty)^d$, nominal volatilities $\sigma\in(0,\infty)^d$, effort bounds $A_{\max}>0$ and $0<\varepsilon\le 1$, risk aversions $r>0$ (consumer) and $p>0$ (producer), a marginal cost of volatility $h>0$, marginal energy value and cost $\kappa,\theta\in\mathbb R$, a horizon $T>0$, an initial consumption $X_0\in\mathbb R$ and a reservation utility $R_0<0$. Write $\bar\mu:=\mu\cdot\mathbf 1=\sum_i\mu_i$, $\delta:=\kappa-\theta$ and $x^-:=0\vee(-x)$.
--
--   **Efforts and costs.** The effort sets are the boxes
--   $$A:=[0,\mu_1A_{\max}]\times\cdots\times[0,\mu_NA_{\max}],\qquad B:=[\varepsilon,1]^d,$$
--   and the costs are
--   $$c_1(a):=\frac12\sum_{i=1}^N\frac{a_i^2}{\mu_i},\qquad c_2(b):=\sum_{j=1}^d\frac{\sigma_j^2}{\lambda_j}\big(b_j^{-1}-1\big),\qquad |\sigma(b)|^2:=\sum_{j=1}^d\sigma_j^2b_j .$$
--
--   **Hamiltonians (2.9).** For payment rates $z,\gamma\in\mathbb R$,
--   $$H_m(z):=-\inf_{a\in A}\{a\cdot\mathbf 1\,z+c_1(a)\},\qquad H_v(\gamma):=-\frac12\inf_{b\in B}\{c_2(b)-\gamma|\sigma(b)|^2\}.$$
--
--   **Best responses (Prop. 2.1).** $\hat a_i(z):=\mu_i(z^-\wedge A_{\max})$, and $\hat b_j(\gamma):=(1\wedge(\lambda_j\gamma^-)^{-1/2})\vee\varepsilon$, which equals $1$ when $\lambda_j\gamma^-\le 1$ (with $0^{-1/2}=+\infty$) and $\max(\varepsilon,(\lambda_j\gamma^-)^{-1/2})$ otherwise. Further $\hat c_2(\gamma):=c_2(\hat b(\gamma))$ and $|\hat\sigma(\gamma)|^2:=|\sigma(\hat b(\gamma))|^2$.
--
--   **Producer's volatility cost (A.10) and Lemma A.1.** $f_0(q,\gamma):=q|\hat\sigma(\gamma)|^2+\hat c_2(\gamma)$ and $F_0(q):=\inf_{\gamma\le 0}f_0(q,\gamma)$.
--
--   These objects are used by every statement of the mission: the closed forms of the consumer's best response, the producer's scalar optimisation, and the second-best value.
--
--   **Formalization Note.** Indices are `Fin N` and `Fin d`; $N=0$ or $d=0$ is allowed. All hypotheses are fields of the structure `Params`. Two are added to the paper's: $\varepsilon\le1$, so that $B$ is non-empty, and $R_0<0$, read from "$R_0\in\mathbb R_-$" and needed for $\log(-R_0)$. $H_m$ and $H_v$ are defined by their infima (real `sInf` of the image of a non-empty compact box under a continuous map, hence a genuine minimum), not by their closed forms. $\hat b$ is defined piecewise because Lean's `rpow` gives $0^{-1/2}=0$. $F_0$ is a real infimum over a non-empty index set of a function bounded below ($\hat c_2\ge0$, $0\le|\hat\sigma|^2\le|\sigma|^2$).
-- source:
--   Aïd, Possamaï, Touzi, Optimal Electricity Demand Response Contracting with Responsiveness Incentives, arXiv:1810.09063v3, Section 2.1 (pp. 7-8), (2.8)-(2.9) and Proposition 2.1 (p. 9), (3.1) (p. 10), (A.10) and Lemma A.1 (p. 29)

import Mathlib

namespace DemandResponse.SecondBest

/-- The parameters of the demand-response model of Aïd–Possamaï–Touzi (arXiv:1810.09063v3, §2.1–2.2,
pp. 7–9, and (3.1), p. 10), together with the standing hypotheses of the paper.  `N` and `d` are the
numbers of usages for the mean effort and for the volatility effort.

Added (disclosed) hypotheses: `ε ≤ 1` (so that `B = [ε,1]^d` is non-empty) and `R₀ < 0` (the page writes
`R₀ ∈ ℝ₋`, and `L₀ = -(1/r) log(-R₀)` needs `-R₀ > 0`). -/
structure Params (N d : ℕ) where
  /-- cost parameters of the mean effort, `μ ∈ (0,∞)^N` -/
  μ : Fin N → ℝ
  /-- cost parameters of the volatility effort, `λ ∈ (0,∞)^d` -/
  lam : Fin d → ℝ
  /-- nominal volatilities `σ ∈ (0,∞)^d` -/
  σ : Fin d → ℝ
  /-- bound on the mean effort -/
  Amax : ℝ
  /-- lower bound of the volatility effort -/
  ε : ℝ
  /-- consumer's absolute risk aversion -/
  r : ℝ
  /-- producer's absolute risk aversion -/
  p : ℝ
  /-- marginal cost of volatility -/
  h : ℝ
  /-- marginal value of energy for the consumer, `f(x) = κ x` -/
  κ : ℝ
  /-- marginal generation cost of the producer, `g(x) = θ x` -/
  θ : ℝ
  /-- horizon -/
  T : ℝ
  /-- initial consumption -/
  X0 : ℝ
  /-- reservation utility of the consumer -/
  R0 : ℝ
  hμ : ∀ i, 0 < μ i
  hlam : ∀ j, 0 < lam j
  hσ : ∀ j, 0 < σ j
  hAmax : 0 < Amax
  hε : 0 < ε
  hε1 : ε ≤ 1
  hr : 0 < r
  hp : 0 < p
  hh : 0 < h
  hT : 0 < T
  hR0 : R0 < 0

variable {N d : ℕ}

/-- Negative part `x⁻ := 0 ∨ (-x)` (p. 9). -/
def negp (x : ℝ) : ℝ := max 0 (-x)

/-- `μ̄ := μ · 1 = ∑ᵢ μᵢ`. -/
def muBar (P : Params N d) : ℝ := ∑ i, P.μ i

/-- Energy value discrepancy `δ := κ - θ`, so that `(f - g)(x) = δ x` ((3.1), p. 10). -/
def delta (P : Params N d) : ℝ := P.κ - P.θ

/-- The mean-effort box `A := [0, μ₁ A_max] × ⋯ × [0, μ_N A_max]` (p. 8). -/
def EffA (P : Params N d) : Set (Fin N → ℝ) := {a | ∀ i, 0 ≤ a i ∧ a i ≤ P.μ i * P.Amax}

/-- The volatility-effort box `B := [ε, 1]^d` (p. 8). -/
def EffB (P : Params N d) : Set (Fin d → ℝ) := {b | ∀ j, P.ε ≤ b j ∧ b j ≤ 1}

/-- `c₁(a) := ½ ∑ᵢ aᵢ² / μᵢ` (p. 8). -/
noncomputable def c1 (P : Params N d) (a : Fin N → ℝ) : ℝ := (1 / 2) * ∑ i, a i ^ 2 / P.μ i

/-- `c₂(b) := ∑ⱼ (σⱼ² / λⱼ) (bⱼ⁻¹ - 1)` (p. 8). -/
noncomputable def c2 (P : Params N d) (b : Fin d → ℝ) : ℝ := ∑ j, P.σ j ^ 2 / P.lam j * ((b j)⁻¹ - 1)

/-- `|σ(b)|² = ∑ⱼ σⱼ² bⱼ`, where `σ(b) := (σ₁ √b₁, …, σ_d √b_d)` ((2.1), p. 7). -/
def sigmaSq (P : Params N d) (b : Fin d → ℝ) : ℝ := ∑ j, P.σ j ^ 2 * b j

/-- Drift component of the consumer's Hamiltonian, by its defining infimum (2.9):
`H_m(z) := - inf_{a ∈ A} { a·1 z + c₁(a) }`. -/
noncomputable def Hm (P : Params N d) (z : ℝ) : ℝ :=
  - sInf ((fun a : Fin N → ℝ => (∑ i, a i) * z + c1 P a) '' EffA P)

/-- Volatility component of the consumer's Hamiltonian, by its defining infimum (2.9):
`H_v(γ) := -½ inf_{b ∈ B} { c₂(b) - γ |σ(b)|² }`. -/
noncomputable def Hv (P : Params N d) (γ : ℝ) : ℝ :=
  -(1 / 2) * sInf ((fun b : Fin d → ℝ => c2 P b - γ * sigmaSq P b) '' EffB P)

/-- Consumer's best response on the drift, `âᵢ(z) := μᵢ (z⁻ ∧ A_max)` (Prop. 2.1, p. 9). -/
def ahat (P : Params N d) (z : ℝ) : Fin N → ℝ := fun i => P.μ i * min (negp z) P.Amax

/-- Consumer's best response on the volatilities, `b̂ⱼ(γ) := (1 ∧ (λⱼ γ⁻)^{-1/2}) ∨ ε`
(Prop. 2.1, p. 9), with the paper's reading `0^{-1/2} = +∞`: when `λⱼ γ⁻ ≤ 1` the value is `1`. -/
noncomputable def bhat (P : Params N d) (γ : ℝ) : Fin d → ℝ := fun j =>
  if P.lam j * negp γ ≤ 1 then 1 else max P.ε ((P.lam j * negp γ) ^ (-(1 / 2 : ℝ)))

/-- `ĉ₂(γ) := c₂(b̂(γ))` (p. 9). -/
noncomputable def c2hat (P : Params N d) (γ : ℝ) : ℝ := c2 P (bhat P γ)

/-- `|σ̂(γ)|² := |σ(b̂(γ))|²` (p. 9). -/
noncomputable def sigmaHatSq (P : Params N d) (γ : ℝ) : ℝ := sigmaSq P (bhat P γ)

/-- `f₀(q, γ) := q |σ̂(γ)|² + ĉ₂(γ)` ((A.10), p. 29). -/
noncomputable def f0 (P : Params N d) (q γ : ℝ) : ℝ := q * sigmaHatSq P γ + c2hat P γ

/-- `F₀(q) := inf_{γ ≤ 0} f₀(q, γ)` (Lemma A.1, p. 29). The index set is non-empty and the function is
bounded below (`ĉ₂ ≥ 0`, `0 ≤ |σ̂|² ≤ |σ|²`), so the real infimum is a genuine infimum. -/
noncomputable def F0 (P : Params N d) (q : ℝ) : ℝ := ⨅ γ : {γ : ℝ // γ ≤ 0}, f0 P q γ

end DemandResponse.SecondBest


