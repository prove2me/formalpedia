-- Prove2me | Definitions.Def_HackingInterval_ATE_Model
-- name    : HackingInterval_ATE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:37:24.853372+00:00
-- url     : https://prove2.me/theorems/306bd78c-c2cd-48f4-9983-41068f77cefb
-- title:
--   §5, §5.1, pp. 10–11 — treatment design X̃ = [X, 1[treated]], loss of (14)/(15), β∗LS, γ∗LS, β̃∗LS, Vtt, SSE (on X̃) and (16)/(17)
-- statement:
--   Scenario 1 consists of a confounder matrix $X\in\mathbb R^{n\times p}$, outcomes $Y\in\mathbb R^n$, and a treatment indicator $w\in\{0,1\}^n$. The full design is $\tilde X=[X,w]$, and the loss constrained in problems (14) and (15) is
--
--   $$L(\beta,\beta_0)=\sum_{i=1}^n(y_i-x_i^\mathsf T\beta-\beta_0w_i)^2.$$
--
--   The model defines $\beta^*_{\mathrm{LS}}=(X^\mathsf TX)^{-1}X^\mathsf TY$, $\gamma^*_{\mathrm{LS}}=(X^\mathsf TX)^{-1}X^\mathsf Tw$, and $\tilde\beta^*_{\mathrm{LS}}=(\tilde X^\mathsf T\tilde X)^{-1}\tilde X^\mathsf TY$. Its treatment coordinate is $\tilde\beta^*_{0,\mathrm{LS}}$, and $V_{tt}$ is the treatment diagonal entry of $(\tilde X^\mathsf T\tilde X)^{-1}$. The resulting closed-form candidate coefficient pairs are the plus and minus formulas of Theorem 1. A solution of (14) or (15) is a feasible pair that globally maximizes or minimizes the treatment coefficient.
--
--   This definition is the common model for the goal and the two equation milestones.
--
--   **Formalization Note** The regression of $Y$ on $\tilde X$ is packaged as an instance of the generic least-squares design `HackingInterval.ATE.Design`, so $\tilde\beta^*_{\mathrm{LS}}$ and SSE are that design's $\beta^*_{\mathrm{LS}}$ and SSE. The SSE is $\|Y-\tilde X\tilde\beta^*_{\mathrm{LS}}\|^2$. This corrects the paper's printed $X$-only SSE, which makes the stated endpoint formulas false. The treatment coordinate is the distinguished final column, with no implicit intercept.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), pp. 10–11 (PDF 11–12), §5–§5.1, Theorem 1 and problems (14)–(15)

import Mathlib
import Definitions.Def_HackingInterval_ATE_Design
open Matrix
noncomputable section

namespace HackingInterval.ATE

/-- Confounders, treatment assignments, and outcomes in Scenario 1. -/
structure TreatData (n p : ℕ) where
  X : Matrix (Fin n) (Fin p) ℝ
  treated : Fin n → Bool
  Y : Fin n → ℝ

variable {n p : ℕ}

/-- The treatment indicator. -/
def TreatData.ind (D : TreatData n p) : Fin n → ℝ :=
  fun i => if D.treated i then 1 else 0

/-- The full design with treatment as its last column. -/
def TreatData.Xt (D : TreatData n p) : Matrix (Fin n) (Fin p ⊕ Unit) ℝ :=
  Matrix.fromCols D.X (Matrix.replicateCol Unit D.ind)

/-- The quadratic loss in problems (14) and (15). -/
def TreatData.loss (D : TreatData n p) (β : Fin p → ℝ) (b0 : ℝ) : ℝ :=
  ∑ i, (D.Y i - (D.X *ᵥ β) i - b0 * D.ind i) ^ 2

/-- `β*_LS := (XᵀX)⁻¹XᵀY`, the regression of `Y` on the confounders `X`. -/
def TreatData.betaLS (D : TreatData n p) : Fin p → ℝ :=
  (D.Xᵀ * D.X)⁻¹ *ᵥ (D.Xᵀ *ᵥ D.Y)

/-- `γ*_LS := (XᵀX)⁻¹Xᵀ1[treated]`, the regression of the indicator on `X`. -/
def TreatData.gammaLS (D : TreatData n p) : Fin p → ℝ :=
  (D.Xᵀ * D.X)⁻¹ *ᵥ (D.Xᵀ *ᵥ D.ind)

/-- The regression of `Y` on the full design `X̃ = [X, 1[treated]]`, as a least-squares `Design`. -/
def TreatData.full (D : TreatData n p) : Design (Fin n) (Fin p ⊕ Unit) where
  X := D.Xt
  Y := D.Y

/-- `β̃*_LS := (X̃ᵀX̃)⁻¹X̃ᵀY`, the least-squares coefficients of the regression on `X̃`. -/
def TreatData.betaTildeLS (D : TreatData n p) : Fin p ⊕ Unit → ℝ :=
  D.full.betaLS

/-- `β̃*_{0,LS}`: the coordinate of `β̃*_LS` for the treatment column. -/
def TreatData.beta0TildeLS (D : TreatData n p) : ℝ :=
  D.betaTildeLS (Sum.inr ())

/-- `V_tt := ([X̃ᵀX̃]⁻¹)_tt`, the diagonal entry for the treatment column. -/
def TreatData.Vtt (D : TreatData n p) : ℝ :=
  (D.Xtᵀ * D.Xt)⁻¹ (Sum.inr ()) (Sum.inr ())

/-- SSE, corrected: the residual sum of squares `‖Y − X̃β̃*_LS‖²` of the regression on the full
design `X̃` (the page prints the regression on `X` alone, under which Theorem 1 is false). -/
def TreatData.SSE (D : TreatData n p) : ℝ :=
  D.full.SSE

/-- `β*_{0,max} = β̃*_{0,LS} + √V_tt √(θ − SSE)`, eq. (16). -/
def TreatData.beta0Max (D : TreatData n p) (θ : ℝ) : ℝ :=
  D.beta0TildeLS + Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE)

/-- `β*_{0,min} = β̃*_{0,LS} − √V_tt √(θ − SSE)`, eq. (17). -/
def TreatData.beta0Min (D : TreatData n p) (θ : ℝ) : ℝ :=
  D.beta0TildeLS - Real.sqrt D.Vtt * Real.sqrt (θ - D.SSE)

/-- `β*_max = β*_LS − β*_{0,max} γ*_LS`, eq. (16). -/
def TreatData.betaMax (D : TreatData n p) (θ : ℝ) : Fin p → ℝ :=
  D.betaLS - D.beta0Max θ • D.gammaLS

/-- `β*_min = β*_LS − β*_{0,min} γ*_LS`, eq. (17). -/
def TreatData.betaMin (D : TreatData n p) (θ : ℝ) : Fin p → ℝ :=
  D.betaLS - D.beta0Min θ • D.gammaLS

/-- A feasible point that globally maximizes the treatment coefficient in (14). -/
def TreatData.IsSol14 (D : TreatData n p) (θ : ℝ) (β : Fin p → ℝ) (b0 : ℝ) : Prop :=
  D.loss β b0 ≤ θ ∧ ∀ β' b0', D.loss β' b0' ≤ θ → b0' ≤ b0

/-- A feasible point that globally minimizes the treatment coefficient in (15). -/
def TreatData.IsSol15 (D : TreatData n p) (θ : ℝ) (β : Fin p → ℝ) (b0 : ℝ) : Prop :=
  D.loss β b0 ≤ θ ∧ ∀ β' b0', D.loss β' b0' ≤ θ → b0 ≤ b0'

end HackingInterval.ATE


