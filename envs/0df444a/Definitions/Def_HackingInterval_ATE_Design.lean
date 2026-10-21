-- Prove2me | Definitions.Def_HackingInterval_ATE_Design
-- name    : HackingInterval_ATE_Design
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:42.307541+00:00
-- url     : https://prove2.me/theorems/00daff60-bea2-4bde-b5fc-fd874aa940c5
-- title:
--   §5.2, Theorem 4, pp. 13–14 — least-squares design: loss Σ(yᵢ − xᵢᵀβ)², β∗LS, SSE, Υ, μ̃, β∗± and the solution predicates
-- statement:
--   A finite least-squares design consists of a real matrix $X$ and an outcome vector $Y$ with one outcome for each row of $X$. For a coefficient vector $\beta$, its loss is
--
--   $$L(\beta)=\sum_i (Y_i-(X\beta)_i)^2.$$
--
--   When the Gram matrix is invertible, the usual least-squares coefficient is $\beta^*_{\mathrm{LS}}=(X^\mathsf TX)^{-1}X^\mathsf TY$, and $\mathrm{SSE}=L(\beta^*_{\mathrm{LS}})$. For a new covariate vector $x^{(\mathrm{new})}$, the model also defines $\Upsilon=(X^\mathsf TX)^{-1}x^{(\mathrm{new})}$ and $\tilde\mu=\sqrt{\theta-\mathrm{SSE}}/\|X\Upsilon\|$. The two candidate coefficients are $\beta^*_{\mathrm{LS}}\pm\tilde\mu\Upsilon$. A maximum or minimum solution means a feasible coefficient vector whose prediction $x^{(\mathrm{new})\mathsf T}\beta$ bounds that of every feasible vector in the corresponding direction.
--
--   This generic design is reused in both halves of Theorem 4 and can be instantiated with the full treatment design of Theorem 1.
--
--   **Formalization Note** The formulas are total Lean definitions. The theorems separately require an invertible Gram matrix, nonnegative slack, and a nonzero prediction vector so their inverses, square roots, and quotient have the intended values.
-- source:
--   Coker, Rudin & King, A Theory of Statistical Inference for Ensuring the Robustness of Scientific Results, Management Science (Articles in Advance, 2021), pp. 13–14 (PDF 14–15), §5.2, Theorem 4

import Mathlib
open Matrix
noncomputable section

namespace HackingInterval.ATE

/-- A finite real least-squares design with observed responses. -/
structure Design (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq κ] where
  X : Matrix ι κ ℝ
  Y : ι → ℝ

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The quadratic loss `Σᵢ (yᵢ − xᵢᵀβ)²`. -/
def Design.loss (D : Design ι κ) (β : κ → ℝ) : ℝ :=
  ∑ i, (D.Y i - (D.X *ᵥ β) i) ^ 2

/-- `β*_LS := (XᵀX)⁻¹XᵀY`, with Mathlib's matrix inverse. -/
def Design.betaLS (D : Design ι κ) : κ → ℝ :=
  (D.Xᵀ * D.X)⁻¹ *ᵥ (D.Xᵀ *ᵥ D.Y)

/-- `SSE = ‖Y − Xβ*_LS‖²`. -/
def Design.SSE (D : Design ι κ) : ℝ := D.loss D.betaLS

/-- `Υ = (XᵀX)⁻¹x(new)`. -/
def Design.Upsilon (D : Design ι κ) (xnew : κ → ℝ) : κ → ℝ :=
  (D.Xᵀ * D.X)⁻¹ *ᵥ xnew

/-- `μ̃ = √(θ − SSE)/‖XΥ‖`, the Euclidean norm written as `√(Σᵢ (XΥ)ᵢ²)`. -/
def Design.muTilde (D : Design ι κ) (θ : ℝ) (xnew : κ → ℝ) : ℝ :=
  Real.sqrt (θ - D.SSE) / Real.sqrt (∑ i, ((D.X *ᵥ D.Upsilon xnew) i) ^ 2)

/-- `β*_+ = β*_LS + μ̃Υ`. -/
def Design.betaPlus (D : Design ι κ) (θ : ℝ) (xnew : κ → ℝ) : κ → ℝ :=
  D.betaLS + D.muTilde θ xnew • D.Upsilon xnew

/-- `β*_- = β*_LS − μ̃Υ`. -/
def Design.betaMinus (D : Design ι κ) (θ : ℝ) (xnew : κ → ℝ) : κ → ℝ :=
  D.betaLS - D.muTilde θ xnew • D.Upsilon xnew

/-- Feasibility and global optimality for the maximization in Theorem 4. -/
def Design.IsMaxSol (D : Design ι κ) (θ : ℝ) (xnew β : κ → ℝ) : Prop :=
  D.loss β ≤ θ ∧ ∀ β', D.loss β' ≤ θ → xnew ⬝ᵥ β' ≤ xnew ⬝ᵥ β

/-- Feasibility and global optimality for the minimization in Theorem 4. -/
def Design.IsMinSol (D : Design ι κ) (θ : ℝ) (xnew β : κ → ℝ) : Prop :=
  D.loss β ≤ θ ∧ ∀ β', D.loss β' ≤ θ → xnew ⬝ᵥ β ≤ xnew ⬝ᵥ β'

end HackingInterval.ATE


