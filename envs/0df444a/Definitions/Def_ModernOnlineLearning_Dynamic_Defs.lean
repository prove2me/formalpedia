-- Prove2me | Definitions.Def_ModernOnlineLearning_Dynamic_Defs
-- name    : ModernOnlineLearning_Dynamic_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:31:00.034264+00:00
-- url     : https://prove2.me/theorems/4cca88ce-7255-4584-8156-593cf358b61d
-- title:
--   Definition 14.1 and Algorithm 6.1 — dynamic regret, path length, and an OMD run
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $V\subseteq X\subseteq E$ a feasible set and regularizer domain, and $T\ge1$. The following definitions describe the online protocol in Chapter 14.
--
--   1. A regularizer $\psi$ is **closed on $X$** when the epigraph of its extension by $+\infty$ outside $X$ is closed.
--   2. A functional $g$ is a subgradient of a loss $f$ at $z$, relative to $V$, when $f(z)+\langle g,y-z\rangle\le f(y)$ for every $y\in V$.
--   3. A finite **online mirror descent run** starts at $x_1\in V\cap\operatorname{int}X$. At round $t$, the learner uses a positive step $\eta_t$, chooses a relative subgradient $g_t$ of $\ell_t$ at $x_t$, and takes $x_{t+1}$ to be any minimizer over $V$ of $z\mapsto\langle g_t,z\rangle+B_\psi(z;x_t)/\eta_t$. The losses have relative subgradients at every feasible point, and all iterates through $x_{T+1}$ lie in $V\cap\operatorname{int}X$.
--   4. For any comparator sequence $u_1,\ldots,u_T$, define
--
--   $$
--   \operatorname{DRegret}_T(u)=\sum_{t=1}^T(\ell_t(x_t)-\ell_t(u_t)),\qquad P(u)=\sum_{t=2}^T\lVert u_t-u_{t-1}\rVert.
--   $$
--
--   For differentiable $\psi$, the finite quantity used in Theorem 14.2 is
--
--   $$
--   Q=\max_{1\le t\le T}\lVert\nabla\psi(x_t)-\nabla\psi(x_1)\rVert_*.
--   $$
--
--   These definitions provide the common model for the one-step estimate and the dynamic regret theorem.
--
--   **Formalization Note** The OMD run records the page's interior-iterate condition explicitly. Subgradients are relative to $V$, as only comparisons with points of $V$ are used; this is weaker than the book's full-space subgradient convention. Index zero is unused. The dual norm is the operator norm of continuous linear functionals.
-- source:
--   Orabona, arXiv:1912.13213v10, Definition 14.1, p. 227 (PDF p. 239); Algorithm 6.1, p. 65 (PDF p. 77); Theorem 14.2, p. 228 (PDF p. 240)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting
import Definitions.Def_ModernOnlineLearning_OMD_Defs

namespace ModernOnlineLearning.Dynamic

/-- A real-valued regularizer on `X` is closed when its extended-real epigraph
`{(z,r) : z ∈ X and ψ z ≤ r}` is closed. This is the book's convention for a
closed function whose value is `+∞` outside its domain. -/
def ClosedRegularizerOn {E : Type*} [TopologicalSpace E]
    (X : Set E) (ψ : E → ℝ) : Prop :=
  IsClosed {p : E × ℝ | p.1 ∈ X ∧ ψ p.1 ≤ p.2}

/-- Algorithm 6.1: a finite OMD run, retaining every allowed oracle and
argmin choice. Round zero is unused. The interior clauses make the Bregman
divergences evaluated along the run meaningful. -/
def IsOMDRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (ℓ : ℕ → E → ℝ) (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) (T : ℕ) : Prop :=
  x 1 ∈ V ∩ interior X ∧
  ∀ t ∈ Finset.Icc 1 T,
    0 < η t ∧ x t ∈ V ∩ interior X ∧ x (t + 1) ∈ V ∩ interior X ∧
    (∀ z ∈ V, ∃ q : E →L[ℝ] ℝ, ModernOnlineLearning.OMD.IsSubgradientOn V (ℓ t) z q) ∧
    ModernOnlineLearning.OMD.IsSubgradientOn V (ℓ t) (x t) (g t) ∧
    ∀ z ∈ V,
      g t (x (t + 1)) + (1 / η t) * BeckTeboulleMD.EMDA.bregman ψ (x (t + 1)) (x t) ≤
        g t z + (1 / η t) * BeckTeboulleMD.EMDA.bregman ψ z (x t)

/-- Definition 14.1, regret against a specified comparator sequence. -/
def dynamicRegret {E : Type*} (ℓ : ℕ → E → ℝ) (x u : ℕ → E) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (ℓ t (x t) - ℓ t (u t))

/-- The norm path length in Definition 14.1; `u 0` is never used. -/
def pathLength {E : Type*} [NormedAddGroup E] (u : ℕ → E) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 2 T, ‖u t - u (t - 1)‖

/-- The finite maximum `Q` in Theorem 14.2. The horizon is nonzero. -/
noncomputable def maxGradientShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (x : ℕ → E) (T : ℕ) (hT : 1 ≤ T) : ℝ :=
  ((Finset.Icc 1 T).image
    (fun t => ‖fderiv ℝ ψ (x t) - fderiv ℝ ψ (x 1)‖)).max'
    (by
      refine ⟨‖fderiv ℝ ψ (x 1) - fderiv ℝ ψ (x 1)‖, ?_⟩
      exact Finset.mem_image.mpr ⟨1, Finset.mem_Icc.mpr ⟨le_refl 1, hT⟩, rfl⟩)

end ModernOnlineLearning.Dynamic


