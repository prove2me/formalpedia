-- Prove2me | Definitions.Def_DRJointCC_Individual_Supplement_Support
-- name    : DRJointCC_Individual_Supplement_Support
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:27:31.671793+00:00
-- url     : https://prove2.me/theorems/751239ac-5b85-46f1-a5ce-8cef3a7d7ffc
-- title:
--   pp. 22–23 — support set $\Xi$, the moment set $\mathcal P_\Xi$, and the sets $\mathcal X_\Xi^{\mathrm{JCC}}$, $\mathcal Z_\Xi^{\mathrm{JCC}}(\alpha)$, $\mathcal Y_\Xi^{\mathrm{JCC}}(\alpha)$
-- statement:
--   Throughout, $\mathcal P$ is the set of all probability distributions on $\mathbb R^k$ with mean $\mu$ and covariance matrix $\Sigma\succ0$, $\Omega=\begin{bmatrix}\Sigma+\mu\mu^\top&\mu\\\mu^\top&1\end{bmatrix}$ is the second-order moment matrix, $\langle X,Y\rangle=\mathrm{Tr}(XY)$, and $\epsilon\in(0,1)$.
--
--   **Support.** Let $W_1,\dots,W_l\in\mathbb S^{k+1}$ and
--
--   $$
--   \Xi=\big\{\xi\in\mathbb R^k:\ [\xi^\top\ 1]\,W_j\,[\xi^\top\ 1]^\top\le0,\ j=1,\dots,l\big\}.
--   $$
--
--   $\mathcal P_\Xi$ is the set of distributions in $\mathcal P$ (mean $\mu$, covariance $\Sigma$) that are supported on $\Xi$, i.e. give $\mathbb R^k\setminus\Xi$ probability zero.
--
--   **Feasible sets.** For the joint chance constraint with rows $y_i^0(x)+y_i(x)^\top\tilde\xi\le0$, $i=1,\dots,m$, and $\alpha\in\mathbb R^m$:
--
--   $$
--   \mathcal X_\Xi^{\mathrm{JCC}}=\Big\{x:\ \inf_{\mathbb P\in\mathcal P_\Xi}\mathbb P\big(y_i^0(x)+y_i(x)^\top\tilde\xi\le0\ \forall i\big)\ge1-\epsilon\Big\},
--   $$
--
--   $$
--   \mathcal Z_\Xi^{\mathrm{JCC}}(\alpha)=\Big\{x:\ \sup_{\mathbb P\in\mathcal P_\Xi}\mathbb P\text{-}\mathrm{CVaR}_\epsilon\Big(\max_{i=1,\dots,m}\alpha_i\big(y_i^0(x)+y_i(x)^\top\tilde\xi\big)\Big)\le0\Big\},
--   $$
--
--   and $\mathcal Y_\Xi^{\mathrm{JCC}}(\alpha)$ (43) is the set of $x$ for which there are $M\in\mathbb S^{k+1}$, $\beta\in\mathbb R$ and $\tau_0,\dots,\tau_m\in\mathbb R^l$ with $\tau_i\ge0$ and
--
--   $$
--   \beta+\tfrac1\epsilon\langle\Omega,M\rangle\le0,\quad M+\sum_{j=1}^l\tau_{0,j}W_j\succeq0,\quad M+\sum_{j=1}^l\tau_{i,j}W_j-\begin{bmatrix}0&\frac12\alpha_iy_i(x)\\\frac12\alpha_iy_i(x)^\top&\alpha_iy_i^0(x)-\beta\end{bmatrix}\succeq0\ \ (i=1,\dots,m).
--   $$
--
--   These are the objects of §3.6, where support information tightens the moment-based approximations (Theorem 3.7).
--
--   **Formalization Note** "Supported on $\Xi$" is $\mathbb P(\Xi^{\mathrm c})=0$. The worst-case CVaR over $\mathcal P_\Xi$ is a supremum of the published extended-real `cvar` of the published `maxLoss`, not the published `wcCVaR`, which ranges over all of $\mathcal P$. The multipliers $\tau_0$ and $\tau_1,\dots,\tau_m$ are `τ0` and `τ i` (rows 0-based). $M\in\mathbb S^{k+1}$ is `M.IsHermitian`; the bordered block is the published `lmiBlock`.
-- source:
--   Zymler, Kuhn, Rustem, Distributionally Robust Joint Chance Constraints with Second-Order Moment Information, Math. Program. 137 (2013), accepted manuscript of 13 Aug 2011, p. 22, §3.6 Distributional Assumptions, X_Ξ^JCC and Z_Ξ^JCC(α); p. 23, (43)

import Mathlib
import Definitions.Def_DRJointCC_Joint_Joint

open MeasureTheory
open scoped ENNReal

namespace DRJointCC.Individual.Supplement

/-- The support set `Ξ = { ξ ∈ ℝ^k : [ξᵀ 1] W_j [ξᵀ 1]ᵀ ≤ 0 ∀ j = 1, …, l }`, p. 22. -/
def Xi {k l : ℕ} (W : Fin l → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) : Set (Fin k → ℝ) :=
  {ξ | ∀ j, DRJointCC.Individual.liftQuad (W j) ξ ≤ 0}

/-- `𝒫_Ξ`, p. 22: the distributions in the moment set `𝒫` (mean `μ`, covariance `Sig`) that are
supported on `Ξ`, i.e. give the complement of `Ξ` measure zero. -/
def PXi {k l : ℕ} (μ : Fin k → ℝ) (Sig : Matrix (Fin k) (Fin k) ℝ)
    (W : Fin l → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) : Set (Measure (Fin k → ℝ)) :=
  {P | P ∈ DRJointCC.Individual.ambiguitySet μ Sig ∧ P (Xi W)ᶜ = 0}

/-- `𝒳_Ξ^JCC = { x : inf_{ℙ ∈ 𝒫_Ξ} ℙ(y_i⁰(x) + y_i(x)ᵀξ̃ ≤ 0 ∀ i) ≥ 1 − ε }`, p. 22. -/
def XXi {m n k l : ℕ} (D : DRJointCC.Joint.JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ)
    (W : Fin l → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) : Set (Fin n → ℝ) :=
  {x | ENNReal.ofReal (1 - ε) ≤
    ⨅ P ∈ PXi μ Sig W,
      P {ξ | ∀ i, DRJointCC.Joint.y0 D i x + DRJointCC.Joint.y D i x ⬝ᵥ ξ ≤ 0}}

/-- `𝒵_Ξ^JCC(α) = { x : sup_{ℙ ∈ 𝒫_Ξ} ℙ-CVaR_ε(max_i α_i (y_i⁰(x) + y_i(x)ᵀξ̃)) ≤ 0 }`, p. 22. -/
def ZXi {m n k l : ℕ} (D : DRJointCC.Joint.JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ)
    (W : Fin l → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (α : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | (⨆ P ∈ PXi μ Sig W, DRJointCC.Individual.cvar ε P (DRJointCC.Joint.maxLoss D α x)) ≤ 0}

/-- The LMI set `𝒴_Ξ^JCC(α)` of (43), p. 23: there are `M ∈ 𝕊^{k+1}`, `β ∈ ℝ` and
`τ_0, …, τ_m ∈ ℝ^l` with `β + (1/ε)⟨Ω, M⟩ ≤ 0`, `τ_i ≥ 0`, `M + Σ_j τ_{0,j} W_j ≽ 0` and
`M + Σ_j τ_{i,j} W_j − [[0, ½α_i y_i(x)], [½α_i y_i(x)ᵀ, α_i y_i⁰(x) − β]] ≽ 0` for
`i = 1, …, m`. Here `τ0` is `τ_0` and `τ i` is `τ_{i+1}` (0-based rows). -/
def YXi {m n k l : ℕ} (D : DRJointCC.Joint.JCCData m n k) (μ : Fin k → ℝ)
    (Sig : Matrix (Fin k) (Fin k) ℝ) (ε : ℝ)
    (W : Fin l → Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (α : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ (M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℝ) (β : ℝ) (τ0 : Fin l → ℝ)
      (τ : Fin m → Fin l → ℝ),
    M.IsHermitian ∧
      β + ε⁻¹ * DRJointCC.Individual.frob (DRJointCC.Individual.momentMatrix μ Sig) M ≤ 0 ∧
      (∀ j, 0 ≤ τ0 j) ∧ (∀ i j, 0 ≤ τ i j) ∧
      (M + ∑ j, τ0 j • W j).PosSemidef ∧
      ∀ i, (M + ∑ j, τ i j • W j - DRJointCC.Joint.lmiBlock D x α β i).PosSemidef}

end DRJointCC.Individual.Supplement


