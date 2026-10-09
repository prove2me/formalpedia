-- Prove2me | Definitions.Def_ModernOnlineLearning_OMD_Defs
-- name    : ModernOnlineLearning_OMD_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:08.344403+00:00
-- url     : https://prove2.me/theorems/843826f0-053f-4584-b74b-45c72b276be5
-- title:
--   Definition 6.4 and Algorithm 6.1 — Bregman setting and online mirror descent
-- statement:
--   Let $E$ be a real normed space (the book's $\mathbb R^d$ with an arbitrary norm $\|\cdot\|$), $X$ the domain of a regularizer $\psi$, and $V\subseteq X$ the nonempty, closed, convex feasible set. The Bregman divergence is
--
--   $$B_\psi(y;x)=\psi(y)-\psi(x)-\langle\nabla\psi(x),y-x\rangle,$$
--
--   where the gradient is evaluated only when $x$ lies in the interior of $X$. A step of online mirror descent with subgradient $g_t$ and positive step size $\eta_t$ chooses a minimizer in $V$ of $y\mapsto\langle g_t,y\rangle+B_\psi(y;x_t)/\eta_t$. A run starts at $x_1\in V\cap\operatorname{int}X$, uses a selected subgradient of each loss, and applies that update on rounds $1,\ldots,T$.
--
--   These definitions give a shared, set-valued model of Algorithm 6.1 for the one-step and regret theorems. No tie-breaking rule is imposed on the subgradient or minimizer.
--
--   **Formalization Note** The Bregman formula is imported from the published Beck–Teboulle definition. The dual norm is the operator norm on continuous linear functionals. A total real-valued Lean function represents $\psi$ on $X$; its values outside $X$ are ignored. Closedness means that the epigraph of this domain-restricted function is closed. The setting assumes the book's "(6.5) or (6.6)": either $\lim_{\lambda\to0^+}\langle\nabla\psi((1-\lambda)x+\lambda y),y-x\rangle=-\infty$ for every boundary point $x$ of $X$ and every interior point $y$, or $V\subseteq\operatorname{int}X$; the gradients in (6.5) are taken at interior points of the convex set $X$, where $\psi$ is differentiable. Subgradients are relative to $V$; the chosen inequality is exactly what the regret argument uses.
-- source:
--   Orabona, arXiv:1912.13213v10, Definition 6.4, p. 63; Algorithm 6.1, (6.5) and (6.6), p. 65; Lemma 6.10 and Theorem 6.11, p. 67

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace ModernOnlineLearning.OMD

/-- A subgradient relative to the feasible set.  The action of `g` is the pairing
between a vector and an element of the continuous dual. -/
def IsSubgradientOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (f : E → ℝ) (x : E) (g : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ V, f x + g (y - x) ≤ f y

/-- Closedness of the extended function equal to `ψ` on `X` and `+∞` off `X`:
its epigraph is closed.  Values of the total Lean function outside `X` are ignored. -/
def IsClosedOnDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) : Prop :=
  IsClosed {p : E × ℝ | p.1 ∈ X ∧ ψ p.1 ≤ p.2}

/-- Condition (6.5), p. 65: `lim_{λ→0} ⟨∇ψ((1 − λ)x + λy), y − x⟩ = −∞` for every
boundary point `x` of `X` and every interior point `y`.  For `λ ∈ (0, 1]` the point
`(1 − λ)x + λy` lies in `int X` when `X` is convex, where `ψ` is differentiable, so the
gradient is genuine there. -/
def Condition65 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) : Prop :=
  ∀ x ∈ frontier X, ∀ y ∈ interior X,
    Filter.Tendsto (fun r : ℝ => fderiv ℝ ψ ((1 - r) • x + r • y) (y - x))
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot

/-- The standing hypotheses of Definition 6.4 and Lemma 6.10, with the book's
"(6.5) or (6.6)".  Nonemptiness of `V` and `V ⊆ X` make the extended regularizer
proper. -/
def IsOMDSetting {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X V : Set E) (ψ : E → ℝ) (lam : ℝ) : Prop :=
  0 < lam ∧ Convex ℝ X ∧ StrictConvexOn ℝ X ψ ∧
    DifferentiableOn ℝ ψ (interior X) ∧ IsClosedOnDomain X ψ ∧
    V.Nonempty ∧ IsClosed V ∧ Convex ℝ V ∧ V ⊆ X ∧
    (Condition65 X ψ ∨ V ⊆ interior X) ∧ StrongConvexOn V lam ψ

/-- The update of Algorithm 6.1. The current point must be feasible and a point
where the gradient of `ψ` is defined. The next point minimizes the linear term
plus the Bregman penalty on `V`; the step size is positive. -/
def IsOMDStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (ψ : E → ℝ) (η : ℝ) (g : E →L[ℝ] ℝ)
    (x y : E) : Prop :=
  0 < η ∧ x ∈ V ∧ DifferentiableAt ℝ ψ x ∧ y ∈ V ∧
    ∀ z ∈ V, g y + (1 / η) * BeckTeboulleMD.EMDA.bregman ψ y x ≤
      g z + (1 / η) * BeckTeboulleMD.EMDA.bregman ψ z x

/-- Algorithm 6.1 on rounds `1,...,T`, with the oracle's selected subgradient
and selected argmin explicit.  Index zero is unused. -/
def IsOMDRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℕ) (X V : Set E) (ψ : E → ℝ) (η : ℕ → ℝ)
    (ℓ : ℕ → E → ℝ) (x : ℕ → E) (g : ℕ → E →L[ℝ] ℝ) : Prop :=
  x 1 ∈ V ∩ interior X ∧
    ∀ t ∈ Finset.Icc 1 T,
      x t ∈ V ∩ interior X ∧
      (∀ z ∈ V, ∃ q : E →L[ℝ] ℝ, IsSubgradientOn V (ℓ t) z q) ∧
      IsSubgradientOn V (ℓ t) (x t) (g t) ∧
      IsOMDStep V ψ (η t) (g t) (x t) (x (t + 1))

/-- The finite maximum in Theorem 6.11, defined only with evidence that the
round set is nonempty. -/
noncomputable def bregmanMax {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℕ) (hT : 1 ≤ T) (ψ : E → ℝ) (u : E) (x : ℕ → E) : ℝ :=
  (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
    (fun t => BeckTeboulleMD.EMDA.bregman ψ u (x t))

end ModernOnlineLearning.OMD


