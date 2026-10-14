-- Prove2me | Definitions.Def_GPhNGIDiffusion_EMError_Model
-- name    : GPhNGIDiffusion_EMError_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:45.252146+00:00
-- url     : https://prove2.me/theorems/0ad4cf4d-bf01-4e26-a570-ccb19bd2d849
-- title:
--   Parameters, drift $g(x)=-\beta p-Rx+(R-\alpha I)p(e'x)^+$ and constants $C_{\mathrm{op}},\tilde C_{\mathrm{op}}$ of the $G/Ph/n+GI$ limiting diffusion
-- statement:
--   This module fixes the data of the limiting diffusion of the $G/Ph/n+GI$ queue in the Halfin–Whitt regime. The state space is $\mathbb R^d$ with the Euclidean norm $|\cdot|$, and $e=(1,\dots,1)'$.
--
--   A **model** consists of:
--
--   1. a patience rate $\alpha>0$ and a slack $\beta\in\mathbb R$;
--   2. a vector $p\in\mathbb R^d$ with $p_i\ge 0$ and $\sum_i p_i=1$;
--   3. service rates $v_1,\dots,v_d>0$ of the phases;
--   4. a sub-stochastic matrix $P$ (entries $\ge 0$, row sums $\le 1$) with $P_{ii}=0$ and $I-P$ invertible;
--   5. the mean-one condition $\zeta=e'R^{-1}p=1$, where $R=(I-P')\,\mathrm{diag}(v)$;
--   6. a $d\times d$ matrix $\sigma$ that is uniformly elliptic: there is $c>0$ with $\xi'\sigma\sigma'\xi\ge c\,\xi'\xi$ for all $\xi\in\mathbb R^d$.
--
--   The drift of the diffusion is the piecewise-linear map
--   $$
--   g(x)=-\beta p-Rx+(R-\alpha I)p\,(e'x)^+,\qquad y^+=\max\{0,y\}.
--   $$
--   The module also defines the operator norm $\|A\|_{\mathrm{op}}=\sup_{|u|=1}|Au|$, the Hilbert–Schmidt norm $\|A\|_{\mathrm{HS}}=(\sum_{i,j}A_{ij}^2)^{1/2}$, and the constants
--   $$
--   C_{\mathrm{op}}=\|R\|_{\mathrm{op}}+\|(R-\alpha I)pe'\|_{\mathrm{op}},\qquad
--   \tilde C_{\mathrm{op}}=C_{\mathrm{op}}+\|\sigma\sigma'\|_{\mathrm{HS}}+1+\|R-\alpha I\|_{\mathrm{op}}+|\beta|.
--   $$
--
--   These are the standing assumptions of the whole paper; every statement of the mission is made for an arbitrary model.
--
--   **Formalization Note** The paper gives an explicit formula for $\sigma\sigma'$ in terms of $c_a^2$, $p$, $P$, $v$ and $\gamma=R^{-1}p$, and remarks (Remark 1.1) that the explicit form of $\sigma$ is not important for its results; the proofs use only the uniform ellipticity, which the paper assumes throughout. Here $\sigma$ is therefore a general matrix with that ellipticity, a generalisation that contains the paper's covariance as a special case. The state space is `EuclideanSpace ℝ (Fin d)` and matrices act by the usual matrix–vector product. Since $\sum_i p_i=1$, a model forces $d\ge 1$.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, pp. 2-3, (1.1) and the model assumptions; p. 7, operator and HS norms; p. 8, (1.8)-(1.9)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState

open Matrix

namespace GPhNGIDiffusion.EMError

/-- A `d × d` matrix acting on the Euclidean state space `ℝ^d = EuclideanSpace ℝ (Fin d)`:
`A x` is the usual matrix–vector product. -/
noncomputable def mv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : EthierKurtz.SDEState d) :
    EthierKurtz.SDEState d :=
  WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)

/-- Operator norm `‖A‖_op = sup_{|u| = 1} |A u|` with respect to the Euclidean norm `|·|`
(§1.4, p. 7). -/
noncomputable def opNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ u : EthierKurtz.SDEState d, ‖u‖ = 1 ∧ r = ‖mv A u‖}

/-- Hilbert–Schmidt norm `‖A‖_HS = (∑_{i,j} A_{ij}²)^{1/2}` (§1.4, p. 7). -/
noncomputable def hsNorm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- The parameters of the limiting diffusion of the `G/Ph/n + GI` queue in the Halfin–Whitt
regime (Jin, Pang, Xu & Xu, arXiv:2209.07361v1, §1.1, pp. 2–3):
* `α > 0` the patience rate, `β ∈ ℝ` the slack in the arrival rate;
* `p ∈ ℝ^d` with nonnegative entries summing to one;
* `v ∈ ℝ^d` the (positive) service rates of the phases;
* `P` a sub-stochastic phase-transition matrix with `P_ii = 0` and `I − P` invertible;
* the Ph distribution has mean one: `ζ = e′R⁻¹p = 1`, where `R = (I − P′) diag(v)`;
* the diffusion matrix `σ` is uniformly elliptic: `ξ′σσ′ξ ≥ c ξ′ξ` for some `c > 0`.
The paper gives an explicit formula for `σσ′` (p. 3) but notes (Remark 1.1) that the explicit form
of `σ` is not important for its results; `σ` is therefore a general matrix with the paper's standing
ellipticity assumption. -/
structure Model (d : ℕ) where
  α : ℝ
  β : ℝ
  p : Fin d → ℝ
  v : Fin d → ℝ
  P : Matrix (Fin d) (Fin d) ℝ
  σ : Matrix (Fin d) (Fin d) ℝ
  hα : 0 < α
  hp_nonneg : ∀ i, 0 ≤ p i
  hp_sum : ∑ i, p i = 1
  hv : ∀ i, 0 < v i
  hP_nonneg : ∀ i j, 0 ≤ P i j
  hP_rowsum : ∀ i, ∑ j, P i j ≤ 1
  hP_diag : ∀ i, P i i = 0
  hP_inv : IsUnit (1 - P).det
  hζ : ∑ i, (((1 - Pᵀ) * diagonal v)⁻¹ *ᵥ p) i = 1
  hell : ∃ c : ℝ, 0 < c ∧ ∀ ξ : Fin d → ℝ, c * (ξ ⬝ᵥ ξ) ≤ ξ ⬝ᵥ ((σ * σᵀ) *ᵥ ξ)

namespace Model

variable {d : ℕ}

/-- `R = (I − P′) diag(v)` (p. 2). -/
noncomputable def R (M : Model d) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - M.Pᵀ) * diagonal M.v

/-- The piecewise-linear drift `g(x) = −βp − Rx + (R − αI)p (e′x)⁺` of (1.1), where
`e = (1, …, 1)′` and `y⁺ = max{0, y}` (p. 2). -/
noncomputable def drift (M : Model d) (x : EthierKurtz.SDEState d) : EthierKurtz.SDEState d :=
  WithLp.toLp 2 (-(M.β • M.p) - M.R *ᵥ WithLp.ofLp x
    + max 0 (∑ i, x i) • ((M.R - M.α • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ M.p))

/-- `C_op = ‖R‖_op + ‖(R − αI)pe′‖_op` (1.8), p. 8. -/
noncomputable def Cop (M : Model d) : ℝ :=
  opNorm M.R + opNorm ((M.R - M.α • (1 : Matrix (Fin d) (Fin d) ℝ)) * Matrix.of (fun i _ => M.p i))

/-- `C̃_op = C_op + ‖σσ′‖_HS + 1 + ‖R − αI‖_op + |β|` (1.9), p. 8. -/
noncomputable def Ctop (M : Model d) : ℝ :=
  M.Cop + hsNorm (M.σ * M.σᵀ) + 1 + opNorm (M.R - M.α • (1 : Matrix (Fin d) (Fin d) ℝ)) + |M.β|

end Model

end GPhNGIDiffusion.EMError


