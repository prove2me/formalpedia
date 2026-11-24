-- Prove2me | Definitions.Def_TwoSidedGrowth_Balance_Supplement_Stationary
-- name    : TwoSidedGrowth_Balance_Supplement_Stationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:31:14.470085+00:00
-- url     : https://prove2.me/theorems/7091690e-28c1-43b8-85a7-98af03a851e6
-- title:
--   §4.2 — stationary maximum-principle equations, balance selector, welfare, and Cobb–Douglas formulas
-- statement:
--   Let $M$ be the published two-sided growth model, with output $g(\gamma,x)=x^\alpha h(\gamma)$. Set $b(\gamma)=\beta^s_0\gamma+\beta^d_0(1-\gamma)$ and let $\pi$ be the platform margin. Define
--   $$
--   V(x,\gamma,\pi)=-b(\gamma)x+(v-c-\pi)g(\gamma,x),\qquad
--   H(x,\pi,\gamma,\psi)=\pi g(\gamma,x)+\psi V(x,\gamma,\pi).
--   $$
--   A stationary state $(x,\gamma,\pi,\psi)$ has $x>0$, $\gamma\in[0,1]$, $V=0$, $H_\pi=0$, $\rho\psi-H_x=0$, and maximizes $H$ over balances in $[0,1]$ with the other coordinates fixed. Stationarity is defined by these equations, independently of the formulas Theorem 2 must establish.
--
--   The stationary state is chosen from these equations, with zero coordinates as the fallback if none exists. The balance $\gamma^*(x)$ is separately chosen from the published clamped-inverse predicate (14), with fallback zero when it has no solution. Theorem 2 and the published goal rule out these fallbacks on their stated domains. Define $x^*$ as the stationary state's size and $W(x)=G(\gamma^*(x),x)$; neither is defined by a desired extremum or curvature property.
--
--   For the specialization $g(s,d)=A s^{a_s}d^{a_d}$ on the nonnegative quadrant, require $A,a_s,a_d>0$ and $\alpha=a_s+a_d$. Put $D=a_s(\rho+\beta^d_0)+a_d(\rho+\beta^s_0)$. The named closed forms are
--   $$
--   x_{\rm CD}=\left\{\frac{A(v-c)(\beta^s_1)^{a_s}(\beta^d_1)^{a_d}a_s^{a_s}a_d^{a_d}}{(\rho+\beta^d_0)^{1-a_s}(\rho+\beta^s_0)^{1-a_d}}\right\}^{1/(1-\alpha)}D,\qquad
--   \gamma_{\rm CD}=\frac{a_s(\rho+\beta^d_0)}{D}.
--   $$
--   These definitions provide one stationary pair shared by all three companions. Theorem 2 proves existence, uniqueness and the closed forms.
--
--   **Formalization Note** The published coefficient names are `bs0 bd0 bs1 bd1`. The derivative $H_\pi$ is the actual derivative, without the spurious factor $\pi$ printed on p. 51. Maximization uses $\le$ for all competing balances, including the chosen balance itself. Theorem 2 supplies the strict inequality for distinct balances where used.
-- source:
--   Lian, van Ryzin, Optimal Growth in Two-Sided Markets, SSRN working paper 3310559 (version of 2020-01-16), pp. 20–21, 51–53, Theorem 2 and (47)–(48)

import Mathlib
import Definitions.Def_TwoSidedGrowth_Balance_Setting

namespace TwoSidedGrowth.Balance.Supplement

noncomputable section
open Classical

/-- Attrition in (12); ASCII coefficients retain the published setting's names. -/
def attrition (M : Model) (γ : ℝ) : ℝ := M.bs0 * γ + M.bd0 * (1 - γ)

/-- State velocity, (12). -/
def velocity (M : Model) (x γ pm : ℝ) : ℝ :=
  -(attrition M γ) * x + (M.v - M.c - pm) * out M γ x

/-- Current-value Hamiltonian, proof of Theorem 2, printed p. 51. -/
def Hamiltonian (M : Model) (x pm γ ψ : ℝ) : ℝ :=
  pm * out M γ x + ψ * velocity M x γ pm

structure StationaryState where
  x : ℝ
  γ : ℝ
  pm : ℝ
  ψ : ℝ

/-- Stationary maximum-principle equations, not the desired closed form.
The balance maximization includes endpoints. The costate equation is Hx = ρψ. -/
def IsStationary (M : Model) (z : StationaryState) : Prop :=
  0 < z.x ∧ z.γ ∈ Set.Icc 0 1 ∧
  velocity M z.x z.γ z.pm = 0 ∧
  deriv (fun pm => Hamiltonian M z.x pm z.γ z.ψ) z.pm = 0 ∧
  (∀ η ∈ Set.Icc (0 : ℝ) 1,
    Hamiltonian M z.x z.pm η z.ψ ≤ Hamiltonian M z.x z.pm z.γ z.ψ) ∧
  M.ρ * z.ψ - deriv (fun x => Hamiltonian M x z.pm z.γ z.ψ) z.x = 0

/-- Total choice from the stationary equations; Theorem 2 proves existence and uniqueness.
The zero fallback is used only outside that theorem's hypotheses. -/
def stationaryState (M : Model) : StationaryState :=
  if hz : ∃ z, IsStationary M z then Classical.choose hz else ⟨0, 0, 0, 0⟩

def stationarySize (M : Model) : ℝ := (stationaryState M).x

/-- Choice from the published clamped inverse (14), never from an argmax.
The published goal proves unique existence for x > 0 under Standing. -/
def balance (M : Model) (x : ℝ) : ℝ :=
  if hb : ∃ γ, IsBalance M x γ then Classical.choose hb else 0

/-- Optimized discounted net welfare, Definition 4 evaluated at (14). No shape is assumed. -/
def W (M : Model) (x : ℝ) : ℝ := G M (balance M x) x

/-- The positive-quadrant Cobb–Douglas specialization in §4.2, printed p. 21. -/
def IsCobbDouglas (M : Model) (A as ad : ℝ) : Prop :=
  0 < A ∧ 0 < as ∧ 0 < ad ∧ M.α = as + ad ∧
  ∀ s d : ℝ, 0 ≤ s → 0 ≤ d → M.g s d = A * s ^ as * d ^ ad

def cobbDenom (M : Model) (as ad : ℝ) : ℝ :=
  as * (M.ρ + M.bd0) + ad * (M.ρ + M.bs0)

def cobbSize (M : Model) (A as ad : ℝ) : ℝ :=
  (A * (M.v - M.c) * M.bs1 ^ as * M.bd1 ^ ad * as ^ as * ad ^ ad /
    ((M.ρ + M.bd0) ^ (1 - as) * (M.ρ + M.bs0) ^ (1 - ad))) ^
    (1 / (1 - M.α)) * cobbDenom M as ad

def cobbBalance (M : Model) (as ad : ℝ) : ℝ :=
  as * (M.ρ + M.bd0) / cobbDenom M as ad

end
end TwoSidedGrowth.Balance.Supplement


