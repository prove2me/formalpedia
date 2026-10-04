-- Prove2me | Definitions.Def_DemandResponse_FirstBest_Hamiltonian
-- name    : DemandResponse_FirstBest_Hamiltonian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:38:18.692862+00:00
-- url     : https://prove2.me/theorems/723af2e9-605b-4e45-b938-edd7932a41f9
-- title:
--   Model parameters, effort boxes A and B, costs c₁, c₂, the consumer's Hamiltonians H_m, H_v (2.9) and best responses â, b̂
-- statement:
--   This file fixes the deterministic data of the electricity demand-response model of Aïd, Possamaï and Touzi (§2.1–2.3) and the consumer's Hamiltonian.
--
--   **Parameters.** Integers $N,d\ge 0$ (numbers of usages for the mean effort and for the volatility effort); cost parameters $\mu\in(0,\infty)^N$, $\lambda\in(0,\infty)^d$; nominal volatilities $\sigma\in(0,\infty)^d$; effort bounds $A_{\max}>0$ and $0<\varepsilon\le 1$; risk-aversion coefficients $r>0$ (consumer) and $p>0$ (producer); the marginal cost of volatility $h>0$; the slopes $\kappa,\theta\in\mathbb R$ of the consumption value $f(x)=\kappa x$ and of the generation cost $g(x)=\theta x$; a horizon $T>0$; the initial consumption $X_0\in\mathbb R$; and the reservation utility $R_0<0$. Write $\bar\mu:=\sum_i\mu_i$, $x^-:=0\vee(-x)$, $\delta:=\kappa-\theta$ (so $(f-g)(x)=\delta x$), $\rho:=\frac{rp}{r+p}$, $L_0:=-\frac1r\log(-R_0)$ and $U(x):=-e^{-px}$.
--
--   **Efforts and costs.** The effort sets are
--   $$A:=[0,\mu_1A_{\max}]\times\cdots\times[0,\mu_NA_{\max}],\qquad B:=[\varepsilon,1]^d,$$
--   with costs $c_1(a):=\frac12\sum_i a_i^2/\mu_i$, $c_2(b):=\sum_j\frac{\sigma_j^2}{\lambda_j}(b_j^{-1}-1)$ and total cost $c(a,b):=c_1(a)+\frac12c_2(b)$. The volatility vector is $\sigma(b):=(\sigma_1\sqrt{b_1},\dots,\sigma_d\sqrt{b_d})$, so $|\sigma(b)|^2=\sum_j\sigma_j^2b_j$.
--
--   **Hamiltonians (2.9).**
--   $$H_m(z):=-\inf_{a\in A}\{a\cdot\mathbf 1\,z+c_1(a)\},\qquad H_v(\gamma):=-\frac12\inf_{b\in B}\{c_2(b)-\gamma|\sigma(b)|^2\}.$$
--
--   **Best responses (Prop. 2.1).** $\hat a_i(z):=\mu_i(z^-\wedge A_{\max})$ and $\hat b_j(\gamma):=(1\wedge(\lambda_j\gamma^-)^{-1/2})\vee\varepsilon$, with $(\lambda_j\gamma^-)^{-1/2}=+\infty$ when $\gamma^-=0$.
--
--   These objects are shared by every statement of the mission: the Hamiltonians govern both the consumer's optimal effort and the closed form of the first-best value.
--
--   **Formalization Note** The parameters and all standing hypotheses are the fields of one structure `Params N d`. Two hypotheses are added to the page: $\varepsilon\le1$, so that $B$ is nonempty, and $R_0<0$ (the page writes $R_0\in\mathbb R_-$; $L_0$ needs $\log$ of a positive number). $H_m$ and $H_v$ are defined by their infima, as real `sInf` of the image of a nonempty compact box under a continuous map, which is bounded below and attained, so the `sInf` is not a junk value. $\hat b_j$ is written with a case split: if $\lambda_j\gamma^-\le1$ the value is $1$, otherwise $\max(\varepsilon,(\lambda_j\gamma^-)^{-1/2})$; this matches the paper's reading of $(\lambda_j\cdot0)^{-1/2}$ as $+\infty$, which Lean's `0 ^ (-1/2) = 0` would not.
-- source:
--   arXiv:1810.09063v3, Section 2.1 (pp. 7-8: A, B, c₁, c₂, c, σ(b), L₀), (2.4) (p. 8), (2.8)-(2.9) and Proposition 2.1 (p. 9), (3.1) (p. 10), ρ (p. 26)

import Mathlib

namespace DemandResponse.FirstBest

/-- The parameters of the demand-response model of Aïd, Possamaï and Touzi (arXiv:1810.09063v3,
§2.1–2.2, pp. 7–9, and (3.1), p. 10), with every standing hypothesis of the paper as a field.

* `N`, `d` : numbers of usages for the mean effort and for the volatility effort;
* `μ i`, `lam j` : cost parameters, `σ j` : nominal volatilities, all positive;
* `Amax`, `ε` : effort bounds, `A = Π i [0, μ i Amax]`, `B = [ε, 1]^d`;
* `r`, `p` : CARA coefficients of the consumer and of the producer;
* `h` : marginal cost of volatility;
* `κ`, `θ` : `f(x) = κ x` (value of consumption) and `g(x) = θ x` (generation cost);
* `T` : horizon, `X₀` : initial consumption, `R₀` : reservation utility.

Added (disclosed): `ε ≤ 1` (so that `B` is nonempty) and `R₀ < 0` (the page writes
`R₀ ∈ ℝ₋`; `L₀ = -(1/r) log(-R₀)` needs `-R₀ > 0`). -/
structure Params (N d : ℕ) where
  μ : Fin N → ℝ
  lam : Fin d → ℝ
  σ : Fin d → ℝ
  Amax : ℝ
  ε : ℝ
  r : ℝ
  p : ℝ
  h : ℝ
  κ : ℝ
  θ : ℝ
  T : ℝ
  X₀ : ℝ
  R₀ : ℝ
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
  hR₀ : R₀ < 0

variable {N d : ℕ}

/-- The negative part `x⁻ := 0 ∨ (-x)` (p. 9). -/
def xneg (x : ℝ) : ℝ := max 0 (-x)

/-- `μ̄ := μ · 1 = Σ i μ i`. -/
def muBar (P : Params N d) : ℝ := ∑ i, P.μ i

/-- Energy value discrepancy `δ := κ - θ`, so that `(f - g)(x) = δ x` (3.1). -/
def delta (P : Params N d) : ℝ := P.κ - P.θ

/-- `ρ := r p / (r + p)`, i.e. `1/ρ = 1/r + 1/p` (p. 26). -/
noncomputable def rho (P : Params N d) : ℝ := P.r * P.p / (P.r + P.p)

/-- Certainty equivalent of the reservation utility, `L₀ := -(1/r) log(-R₀)` (p. 8). -/
noncomputable def L0 (P : Params N d) : ℝ := -(1 / P.r) * Real.log (-P.R₀)

/-- The producer's utility `U(x) := -e^{-p x}` (2.4). -/
noncomputable def U (P : Params N d) (x : ℝ) : ℝ := -Real.exp (-P.p * x)

/-- The mean-effort box `A := [0, μ₁ Amax] × ⋯ × [0, μ_N Amax]` (p. 8). -/
def effortA (P : Params N d) : Set (Fin N → ℝ) :=
  {a | ∀ i, 0 ≤ a i ∧ a i ≤ P.μ i * P.Amax}

/-- The volatility-effort box `B := [ε, 1]^d` (p. 8). -/
def effortB (P : Params N d) : Set (Fin d → ℝ) :=
  {b | ∀ j, P.ε ≤ b j ∧ b j ≤ 1}

/-- `c₁(a) := ½ Σ i a_i² / μ_i` (p. 8). -/
noncomputable def c1 (P : Params N d) (a : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ i, a i ^ 2 / P.μ i

/-- `c₂(b) := Σ j (σ_j² / λ_j) (b_j⁻¹ - 1)` (p. 8). -/
noncomputable def c2 (P : Params N d) (b : Fin d → ℝ) : ℝ :=
  ∑ j, P.σ j ^ 2 / P.lam j * ((b j)⁻¹ - 1)

/-- The effort cost `c(a, b) := c₁(a) + ½ c₂(b)` (p. 8). -/
noncomputable def cost (P : Params N d) (a : Fin N → ℝ) (b : Fin d → ℝ) : ℝ :=
  c1 P a + (1 / 2) * c2 P b

/-- `|σ(b)|² = Σ j σ_j² b_j`, where `σ(b) := (σ₁ √b₁, …, σ_d √b_d)` (2.1). -/
def sigSq (P : Params N d) (b : Fin d → ℝ) : ℝ := ∑ j, P.σ j ^ 2 * b j

/-- `H_m(z) := - inf_{a ∈ A} { a · 1 z + c₁(a) }` (2.9). The infimum is the real `sInf` of the
image of the nonempty compact box `A` under a continuous map, so it is attained. -/
noncomputable def Hm (P : Params N d) (z : ℝ) : ℝ :=
  -sInf ((fun a => (∑ i, a i) * z + c1 P a) '' effortA P)

/-- `H_v(γ) := -½ inf_{b ∈ B} { c₂(b) - γ |σ(b)|² }` (2.9). The infimum is the real `sInf` of
the image of the nonempty compact box `B ⊆ (0, ∞)^d` under a continuous map, so it is
attained. -/
noncomputable def Hv (P : Params N d) (γ : ℝ) : ℝ :=
  -(1 / 2) * sInf ((fun b => c2 P b - γ * sigSq P b) '' effortB P)

/-- The consumer's best response on the drift, `â_i(z) := μ_i (z⁻ ∧ Amax)` (Prop. 2.1). -/
def aHat (P : Params N d) (z : ℝ) : Fin N → ℝ :=
  fun i => P.μ i * min (xneg z) P.Amax

/-- The consumer's best response on the volatilities, `b̂_j(γ) := (1 ∧ (λ_j γ⁻)^{-1/2}) ∨ ε`
(Prop. 2.1, with `j = 1, …, d`). For `λ_j γ⁻ ≤ 1`, in particular for `γ⁻ = 0` where the paper
reads `(λ_j γ⁻)^{-1/2} = +∞`, the minimum with `1` is `1`; the case split avoids Lean's
`0 ^ (-1/2) = 0`. -/
noncomputable def bHat (P : Params N d) (γ : ℝ) : Fin d → ℝ :=
  fun j => if P.lam j * xneg γ ≤ 1 then 1 else max P.ε ((P.lam j * xneg γ) ^ (-(1 / 2 : ℝ)))

end DemandResponse.FirstBest


