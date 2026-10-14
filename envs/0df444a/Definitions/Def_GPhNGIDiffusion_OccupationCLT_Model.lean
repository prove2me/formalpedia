-- Prove2me | Definitions.Def_GPhNGIDiffusion_OccupationCLT_Model
-- name    : GPhNGIDiffusion_OccupationCLT_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:36.877996+00:00
-- url     : https://prove2.me/theorems/9afff9d0-040b-433c-9c12-9ee4c630e53a
-- title:
--   §1.1, pp. 2–3, and (1.8) — parameters of the G/Ph/n+GI limiting diffusion, the drift g and the constant C_op
-- statement:
--   This file fixes the data of the limiting diffusion of the $G/Ph/n+GI$ queue in the Halfin–Whitt regime. Let $d\ge 1$ be the number of service phases.
--
--   1. The **model** consists of a patience rate $\alpha>0$, an arrival slack $\beta\in\mathbb R$, a vector $p\in\mathbb R^d$ with non-negative entries and $\sum_i p_i=1$, service rates $v_1,\dots,v_d>0$, a sub-stochastic routing matrix $P$ (non-negative entries, row sums at most one) with $P_{ii}=0$ and $I-P$ invertible, and a $d\times d$ matrix $\sigma$. With
--   $$
--   R=(I-P')\,\mathrm{diag}(v),\qquad \zeta=e'R^{-1}p,
--   $$
--   where $e=(1,\dots,1)'$, the phase distribution has mean one, $\zeta=1$, and $\sigma\sigma'$ is uniformly elliptic: there is $c>0$ with $\xi'\sigma\sigma'\xi\ge c\,\xi'\xi$ for all $\xi\in\mathbb R^d$.
--   2. The **drift** of the diffusion is
--   $$
--   g(x)=-\beta p-Rx+(R-\alpha I)p\,(e'x)^+,\qquad x\in\mathbb R^d,
--   $$
--   with $y^+=\max\{0,y\}$.
--   3. The constant (1.8) is $C_{op}=\|R\|_{op}+\|(R-\alpha I)pe'\|_{op}$, where $\|\cdot\|_{op}$ is the operator norm for the Euclidean norm $|\cdot|$.
--
--   These are the standing assumptions of the paper; every result of the mission is stated for such a model.
--
--   **Formalization Note** The state space is `EuclideanSpace ℝ (Fin d)`, so $|\cdot|$ is the Euclidean norm; matrices act through `Matrix.toEuclideanCLM`, whose norm is the operator norm. The paper also gives an explicit formula for $\sigma\sigma'$ (p. 3) in terms of $c_a^2>0$, $p$, $P$, $v$ and $\gamma=R^{-1}p$; it is not imposed, because the paper's results use only ellipticity (Remark 1.1: "The explicit form of $\sigma$ is not important for the result in Dieker and Gao [19] and in our work"), so the theorems are stated for every elliptic $\sigma$, which includes the paper's. The condition $\sum_i p_i=1$ excludes $d=0$.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, pp. 2–3, §1.1 (model, (1.1)); p. 8, (1.8)

import Mathlib

open Matrix
open scoped BigOperators

namespace GPhNGIDiffusion.OccupationCLT

/-- The parameters of the limiting diffusion of the `G/Ph/n + GI` queue in the Halfin–Whitt
regime (Jin, Pang, Xu & Xu, arXiv:2209.07361v1, pp. 2–3), in dimension `d` (the number of
service phases), with their standing assumptions:
* `α > 0` (patience rate), `β ∈ ℝ` (arrival slack);
* `p ∈ ℝᵈ` with non-negative entries summing to one;
* service rates `vₖ > 0`;
* `P` sub-stochastic (non-negative entries, row sums at most one), `Pᵢᵢ = 0`, `I − P` invertible;
* the mean condition `ζ = e′R⁻¹p = 1` with `R = (I − P′) diag(v)`;
* uniform ellipticity of `σσ′`: `ξ′σσ′ξ ≥ c ξ′ξ` for some `c > 0`.
The paper's explicit formula for `σσ′` is not imposed: the results use only ellipticity
(Remark 1.1). -/
structure Model (d : ℕ) where
  α : ℝ
  β : ℝ
  p : Fin d → ℝ
  v : Fin d → ℝ
  P : Matrix (Fin d) (Fin d) ℝ
  σ : Matrix (Fin d) (Fin d) ℝ
  α_pos : 0 < α
  p_nonneg : ∀ i, 0 ≤ p i
  p_sum : ∑ i, p i = 1
  v_pos : ∀ i, 0 < v i
  P_nonneg : ∀ i j, 0 ≤ P i j
  P_rowSum : ∀ i, ∑ j, P i j ≤ 1
  P_diag : ∀ i, P i i = 0
  P_inv : IsUnit (1 - P)
  mean_one : ∑ i, ((((1 : Matrix (Fin d) (Fin d) ℝ) - Pᵀ) * diagonal v)⁻¹ *ᵥ p) i = 1
  elliptic : ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin d → ℝ, c * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ ((σ * σᵀ) *ᵥ ξ)

variable {d : ℕ}

/-- The state space `ℝᵈ` with the Euclidean norm `|·|`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A `d × d` matrix acting on `ℝᵈ` as a continuous linear map; its norm is `‖·‖_op`. -/
noncomputable abbrev mat (A : Matrix (Fin d) (Fin d) ℝ) : E d →L[ℝ] E d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A

/-- `R = (I − P′) diag(v)`. -/
def Model.R (M : Model d) : Matrix (Fin d) (Fin d) ℝ :=
  ((1 : Matrix (Fin d) (Fin d) ℝ) - M.Pᵀ) * diagonal M.v

/-- The vector `p` as a point of `ℝᵈ`. -/
def Model.pE (M : Model d) : E d := WithLp.toLp 2 M.p

/-- `e′x = x₁ + ⋯ + x_d`. -/
def eDot (x : E d) : ℝ := ∑ i, x i

/-- The matrix `(R − αI) p e′`. -/
def Model.Q (M : Model d) : Matrix (Fin d) (Fin d) ℝ :=
  (M.R - M.α • (1 : Matrix (Fin d) (Fin d) ℝ)) * vecMulVec M.p (fun _ => (1 : ℝ))

/-- The drift `g(x) = −βp − Rx + (R − αI)p (e′x)⁺` of (1.1). -/
noncomputable def Model.g (M : Model d) (x : E d) : E d :=
  -(M.β • M.pE) - mat M.R x + max (eDot x) 0 • mat (M.R - M.α • 1) M.pE

/-- `C_op = ‖R‖_op + ‖(R − αI)pe′‖_op`, (1.8). -/
noncomputable def Model.Cop (M : Model d) : ℝ := ‖mat M.R‖ + ‖mat M.Q‖

end GPhNGIDiffusion.OccupationCLT


