-- Prove2me | Definitions.Def_SmoothCCP_Feasibility_Setting
-- name    : SmoothCCP_Feasibility_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:42:35.48974+00:00
-- url     : https://prove2.me/theorems/5a3416c4-3213-4d2a-9e24-121c83b13e6d
-- title:
--   pp. 6–11 — Γ_ε (2.2), admissible γ_ε, F, F_ε (3.1), F^N_ε (2.1), X_α, X^{N,t}_{ε,δ} (3.2), M_x (Assumption 3.7)
-- statement:
--   This module fixes the objects of the smooth sample-based approximation of a chance-constrained program. Decisions are vectors $x\in\mathbb R^n$, $X\subseteq\mathbb R^n$ is the deterministic feasible region, $\xi$ is a random vector with law $\mathbb P_\xi$ on a measurable space $\Xi$, and $C(x,\xi)\in\mathbb R$ is the scalar constraint function (in the paper $C(x,\xi)=\max_j c_j(x,\xi)$). The chance constraint is $\mathbb P(C(x,\xi)\le 0)\ge 1-\alpha$.
--
--   1. **Smoothed indicator** (2.2). For $\varepsilon>0$ and $\gamma_\varepsilon:[-\varepsilon,\varepsilon]\to[0,1]$,
--   $$\Gamma_\varepsilon(y)=\begin{cases}1 & y\le-\varepsilon,\\ \gamma_\varepsilon(y) & -\varepsilon<y<\varepsilon,\\ 0 & y\ge\varepsilon.\end{cases}$$
--   2. **Admissible $\gamma_\varepsilon$** (p. 7). $\gamma_\varepsilon$ is *admissible* when $\varepsilon>0$, $\gamma_\varepsilon$ maps $[-\varepsilon,\varepsilon]$ into $[0,1]$, is strictly decreasing there, is symmetric in the sense $\gamma_\varepsilon(-y)=1-\gamma_\varepsilon(y)$ (the form of symmetry the paper uses on p. 13), and makes $\Gamma_\varepsilon$ differentiable on $\mathbb R$.
--   3. **True cdf** (p. 9). $F(t;x)=\mathbb P(C(x,\xi)\le t)$.
--   4. **Smoothed cdf** (3.1). $F_\varepsilon(t;x)=\int_\Xi \Gamma_\varepsilon(C(x,\xi)-t)\,d\mathbb P_\xi$.
--   5. **Smoothed sample cdf** (2.1). For sample values $\xi_1,\dots,\xi_N$, $F^N_\varepsilon(t;x)=\frac1N\sum_{i=1}^N\Gamma_\varepsilon(C(x,\xi_i)-t)$.
--   6. **True feasible set** (p. 9). $X_\alpha=\{x\in X\mid F(0;x)\ge 1-\alpha\}$.
--   7. **Shifted sample feasible set** (3.2). $X^{N,t}_{\varepsilon,\delta}=\{x\in X\mid F^N_\varepsilon(-t;x)\ge 1-\delta\}$.
--   8. **Margin** (Assumption 3.7). $M_x=F(0;x)-F_\varepsilon(-t;x)+(\alpha-\delta)$.
--
--   These are the objects in which every statement of the mission is phrased: the main results compare the random set $X^{N,t}_{\varepsilon,\delta}$ with $X_\alpha$.
--
--   **Formalization Note** Decisions live in `Fin n → ℝ`, whose Mathlib norm is the sup norm $\|\cdot\|_\infty$ used in Assumption 3.12 and Theorem 3.13. By (2.2), $\Gamma_\varepsilon(-\varepsilon)=1$ and $\Gamma_\varepsilon(\varepsilon)=0$, so $\Gamma_\varepsilon$ reads $\gamma_\varepsilon$ only on the open interval $(-\varepsilon,\varepsilon)$. Continuity of $\Gamma_\varepsilon$ (implied by differentiability), strict decrease on the closed interval and values in $[0,1]$ together force $\gamma_\varepsilon(-\varepsilon)=1$ and $\gamma_\varepsilon(\varepsilon)=0$. For $y\in[-\varepsilon,\varepsilon]$ the condition $\gamma_\varepsilon(-y)=1-\gamma_\varepsilon(y)$ is then equivalent to the identity $1-\Gamma_\varepsilon(y)=\Gamma_\varepsilon(-y)$ for all real $y$. The sample-based objects take the sample *values* $\xi_1,\dots,\xi_N$; the random versions are obtained by plugging in $\xi_i(\omega)$. $F$ is `Measure.real` of the event and $F_\varepsilon$ is a Bochner integral; theorems that use them assume $C(x,\cdot)$ measurable and $\mathbb P_\xi$ a probability measure, so that $F$ is the cdf of the law of $C(x,\xi)$ and $F_\varepsilon$ is a genuine integral of a bounded measurable function. On $N=0$ samples $F^N_\varepsilon$ is the junk value $0$, so theorems assume $N\ge1$. The parameters $t,\delta$ are unconstrained here; each theorem imposes the paper's ranges ($\delta\in[0,1]$ in (3.2), $\delta\in[0,\alpha]$ in Assumption 3.7). The quartic kernel (2.6) is admissible for every $\varepsilon>0$ (checked at $\varepsilon=1$ in a sorry-free sanity file).
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, pp. 6–11: (2.1) p. 6, (2.2) and γ_ε pp. 6–7, symmetry 1 − Γ_ε(y) = Γ_ε(−y) p. 13, X_α, F, (3.1), (3.2) p. 9, Assumption 3.7 p. 11

import Mathlib
open MeasureTheory

namespace SmoothCCP.Feasibility

/-- (2.2), pp. 6–7: the smoothed indicator Γ_ε built from γ on [−ε, ε]. -/
noncomputable def Gam (ε : ℝ) (γ : ℝ → ℝ) (y : ℝ) : ℝ :=
  if y ≤ -ε then 1 else if y < ε then γ y else 0

/-- p. 7: "γ_ε : [−ε, ε] → [0, 1] is a symmetric and strictly decreasing function such that it makes
Γ_ε differentiable"; "symmetric" is pinned on p. 13 as 1 − Γ_ε(y) = Γ_ε(−y). -/
structure AdmissibleGamma (ε : ℝ) (γ : ℝ → ℝ) : Prop where
  pos : 0 < ε
  mapsTo : ∀ y ∈ Set.Icc (-ε) ε, γ y ∈ Set.Icc (0 : ℝ) 1
  strictAnti : StrictAntiOn γ (Set.Icc (-ε) ε)
  symm : ∀ y ∈ Set.Icc (-ε) ε, γ (-y) = 1 - γ y
  differentiable : Differentiable ℝ (Gam ε γ)

/-- p. 9: F(t; x) = ℙ(C(x, ξ) ≤ t). -/
noncomputable def cdf {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ)
    (C : (Fin n → ℝ) → Ξ → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  Pξ.real {s | C x s ≤ t}

/-- (3.1), p. 9: F_ε(t; x) = ∫ Γ_ε(C(x, ξ) − t) dℙ_ξ. -/
noncomputable def smoothCdf {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ)
    (C : (Fin n → ℝ) → Ξ → ℝ) (ε : ℝ) (γ : ℝ → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ s, Gam ε γ (C x s - t) ∂Pξ

/-- (2.1), p. 6: F^N_ε(t; x) = (1/N) Σᵢ Γ_ε(C(x, ξᵢ) − t), on sample values `ξs`. -/
noncomputable def sampleCdf {n N : ℕ} {Ξ : Type} (C : (Fin n → ℝ) → Ξ → ℝ) (ε : ℝ) (γ : ℝ → ℝ)
    (ξs : Fin N → Ξ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, Gam ε γ (C x (ξs i) - t)

/-- p. 9: X_α = {x ∈ X | F(0; x) ≥ 1 − α}. -/
def trueFeasible {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ)
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (α : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ X ∧ 1 - α ≤ cdf Pξ C 0 x}

/-- (3.2), p. 9: X^{N,t}_{ε,δ} = {x ∈ X | F^N_ε(−t; x) ≥ 1 − δ}. -/
def sampleFeasible {n N : ℕ} {Ξ : Type} (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ))
    (ε : ℝ) (γ : ℝ → ℝ) (ξs : Fin N → Ξ) (t δ : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ X ∧ 1 - δ ≤ sampleCdf C ε γ ξs (-t) x}

/-- Assumption 3.7, p. 11: M_x = F(0; x) − F_ε(−t; x) + (α − δ). -/
noncomputable def margin {n : ℕ} {Ξ : Type} [MeasurableSpace Ξ] (Pξ : Measure Ξ)
    (C : (Fin n → ℝ) → Ξ → ℝ) (ε : ℝ) (γ : ℝ → ℝ) (t α δ : ℝ) (x : Fin n → ℝ) : ℝ :=
  cdf Pξ C 0 x - smoothCdf Pξ C ε γ (-t) x + (α - δ)

end SmoothCCP.Feasibility


