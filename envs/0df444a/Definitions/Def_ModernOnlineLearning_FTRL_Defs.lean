-- Prove2me | Definitions.Def_ModernOnlineLearning_FTRL_Defs
-- name    : ModernOnlineLearning_FTRL_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:26.691597+00:00
-- url     : https://prove2.me/theorems/30b84701-6e0e-4f5b-984d-3ec5c2705386
-- title:
--   Algorithm 7.1 and Corollary 7.6 — FTRL rounds, minimizers, subgradients, and regularizer schedule
-- statement:
--   For a feasible set $V$ in a finite-dimensional real normed space, the round-$t$ objective is
--   $$F_t(z)=\psi_t(z)+\sum_{i=1}^{t-1}\ell_i(z).$$
--   An FTRL run selects, for each required round, an arbitrary minimizer $x_t\in\operatorname*{argmin}_{z\in V}F_t(z)$. The run extends to $T+1$ because the regret identity uses that extra iterate. A subgradient $g$ of a real-valued loss at $x$ is a continuous linear functional satisfying $f(y)\ge f(x)+g(y-x)$ for every point $y$ in the ambient space; its operator norm is the dual norm. Closedness means the epigraph over $V$ is closed.
--
--   For Corollary 7.6, if $m$ is the attained minimum of $\psi$ on $V$, the regularizer in rounds $1,\ldots,T$ is $\psi_t(z)=(\psi(z)-m)/\eta_{t-1}$ and $\psi_{T+1}=\psi_T$. These definitions let the chapter's equality and stability bounds use the same algorithmic model.
--
--   **Formalization Note** Losses and regularizers are real-valued on the ambient space, while optimization is restricted to $V$. The value at round zero and after $T+1$ is irrelevant to the stated results. An open-neighborhood Lipschitz predicate is included for the corollary's second conclusion.
-- source:
--   Orabona, arXiv:1912.13213v10, Algorithm 7.1, p. 99; Lemma 7.1, p. 100; Corollary 7.6, p. 102

import Mathlib

set_option autoImplicit false

namespace ModernOnlineLearning.FTRL

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The regularized cumulative loss before round `t`; round one has an empty history. -/
def F (ψ ℓ : ℕ → E → ℝ) (t : ℕ) (z : E) : ℝ :=
  ψ t z + ∑ i ∈ Finset.Ico 1 t, ℓ i z

/-- A point attaining the minimum of a real-valued function on the feasible set. -/
def IsMinimizerOn (V : Set E) (f : E → ℝ) (z : E) : Prop :=
  z ∈ V ∧ ∀ y ∈ V, f z ≤ f y

/-- Algorithm 7.1, including the extra iterate needed in the regret identity. -/
def IsFTRLRunUpTo (V : Set E) (ψ ℓ : ℕ → E → ℝ)
    (x : ℕ → E) (T : ℕ) : Prop :=
  ∀ t ∈ Finset.Icc 1 (T + 1), IsMinimizerOn V (F ψ ℓ t) (x t)

/-- A full-space subgradient, in the dual of the ambient normed space. -/
def IsSubgradientAt (f : E → ℝ) (z : E) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ y : E, f z + g (y - z) ≤ f y

/-- Subdifferentiability at every feasible point. -/
def IsSubdifferentiableOn (V : Set E) (f : E → ℝ) : Prop :=
  ∀ z ∈ V, ∃ g : E →L[ℝ] ℝ, IsSubgradientAt f z g

/-- Closedness of the function restricted to the feasible set, by its epigraph. -/
def IsClosedFunctionOn (V : Set E) (f : E → ℝ) : Prop :=
  IsClosed {p : E × ℝ | p.1 ∈ V ∧ f p.1 ≤ p.2}

/-- The Lipschitz condition on an open neighborhood of the feasible set. -/
def IsLipschitzOnOpenNeighborhood (V : Set E) (f : E → ℝ) (L : ℝ) : Prop :=
  ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧
    ∀ a ∈ U, ∀ b ∈ U, |f a - f b| ≤ L * ‖a - b‖

/-- Corollary 7.6's regularizer schedule, including ψ_(T+1) = ψ_T. -/
noncomputable def scheduledRegularizer (ψ : E → ℝ) (m : ℝ) (η : ℕ → ℝ)
    (T t : ℕ) (z : E) : ℝ :=
  if t ≤ T then (ψ z - m) / η (t - 1)
  else (ψ z - m) / η (T - 1)

end ModernOnlineLearning.FTRL


