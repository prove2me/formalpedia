-- Prove2me | Definitions.Def_CondatPD_FB_Setting
-- name    : CondatPD_FB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:39:44.410166+00:00
-- url     : https://prove2.me/theorems/e0b61d63-a3df-4d3d-bcad-2370acd595a1
-- title:
--   §2–§4 — conjugate, smooth term, primal–dual solution, averaged map, algorithms and block forms
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be real Hilbert spaces. For an extended-real function $J$ on a Hilbert space, the **Fenchel conjugate** is
--   $$J^*(s)=\sup_{s'}\{\langle s,s'\rangle-J(s')\}. $$
--   The **smooth term** $F:\mathcal X\to\mathbb R$ is convex, differentiable, and has a $\beta$-Lipschitz gradient, with $\beta\ge0$. A **primal–dual solution** $(\hat x,\hat y)$ satisfies the two inclusions (6):
--   $$-L^*\hat y-\nabla F(\hat x)\in\partial G(\hat x),\qquad L\hat x\in\partial H^*(\hat y).$$
--   The definition also records the paper's averaged-operator class $\mathcal A(\mathcal H,\alpha)$ for $0<\alpha\le1$, the relaxation bound $\delta=2-(\beta/2)(1/\tau-\sigma\|L\|^2)^{-1}$, and the complete error-bearing recursions of Algorithms 3.1 and 3.2. The quadratic forms $q_P(x,y)=\langle(x,y),P(x,y)\rangle_I$ and $q_{P'}$ represent the block operators (20) and (44).
--
--   These definitions give the common mathematical setting for the convergence theorem and its proof milestones.
--
--   **Formalization Note** Extended values use `EReal`; the conjugate takes its supremum there. Proximity maps are the published minimizer predicate and are required to exist in the theorem under positive step sizes. The run predicates prescribe every step from arbitrary initial states, including all three error sequences.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), pp. 2–5 and 8–13, (2), (6), Algorithms 3.1–3.2, (20), (44)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_ThreeOpSplitting_Convergence_Nonexpansive
import Definitions.Def_InertialFB_IFB_ConvexAnalysis

open InnerProductSpace

namespace CondatPD.FB

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The Fenchel conjugate in §2, p. 2. -/
noncomputable def conj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : H → EReal) (s : H) : EReal :=
  ⨆ s' : H, ((⟪s, s'⟫_ℝ : ℝ) : EReal) - J s'

/-- The smooth term in (2), with the paper's β-Lipschitz convention. -/
def IsSmoothTerm (β : ℝ) (F : X → ℝ) : Prop :=
  ConvexOn ℝ Set.univ F ∧ Differentiable ℝ F ∧ 0 ≤ β ∧
    ∀ x x' : X, ‖gradient F x - gradient F x'‖ ≤ β * ‖x - x'‖

/-- The primal–dual inclusion (6). -/
def IsPDSolution (F : X → ℝ) (G : X → EReal) (H : Y → EReal)
    (L : X →L[ℝ] Y) (xh : X) (yh : Y) : Prop :=
  InertialFB.IFB.IsSubgradient G xh
      (-(ContinuousLinearMap.adjoint L yh) - gradient F xh) ∧
    InertialFB.IFB.IsSubgradient (conj H) yh (L xh)

/-- The paper's α-averaged operators, including α = 1. -/
def IsAvg {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    (α : ℝ) (T : K → K) : Prop :=
  0 < α ∧ α ≤ 1 ∧ ∃ T' : K → K,
    ThreeOpSplitting.Convergence.IsNonexpansive T' ∧
      ∀ x : K, T x = α • T' x + (1 - α) • x

/-- The relaxation upper bound δ in Theorem 3.1(ii). -/
noncomputable def pdDelta (β τ σ : ℝ) (L : X →L[ℝ] Y) : ℝ :=
  2 - β / 2 * (1 / τ - σ * ‖L‖ ^ 2)⁻¹

/-- Algorithm 3.1 (9), including all three error sequences. -/
def IsAlg31Run (F : X → ℝ) (L : X →L[ℝ] Y) (PG : X → X) (PH : Y → Y)
    (τ σ : ℝ) (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let xt := PG (x n - τ • (gradient F (x n) + eF n) -
      τ • ContinuousLinearMap.adjoint L (y n)) + eG n
    let yt := PH (y n + σ • L ((2 : ℝ) • xt - x n)) + eH n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧
      y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- Algorithm 3.2 (10), with the dual proximal step first. -/
def IsAlg32Run (F : X → ℝ) (L : X →L[ℝ] Y) (PG : X → X) (PH : Y → Y)
    (τ σ : ℝ) (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (x : ℕ → X) (y : ℕ → Y) : Prop :=
  ∀ n : ℕ,
    let yt := PH (y n + σ • L (x n)) + eH n
    let xt := PG (x n - τ • (gradient F (x n) + eF n) -
      τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - y n)) + eG n
    x (n + 1) = ρ n • xt + (1 - ρ n) • x n ∧
      y (n + 1) = ρ n • yt + (1 - ρ n) • y n

/-- The quadratic form ⟨z,Pz⟩_I for (20). -/
noncomputable def qP (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, (1 / τ) • x - ContinuousLinearMap.adjoint L y⟫_ℝ +
    ⟪y, -(L x) + (1 / σ) • y⟫_ℝ

/-- The corresponding quadratic form for P′ in (44). -/
noncomputable def qP' (τ σ : ℝ) (L : X →L[ℝ] Y) (x : X) (y : Y) : ℝ :=
  ⟪x, (1 / τ) • x + ContinuousLinearMap.adjoint L y⟫_ℝ +
    ⟪y, L x + (1 / σ) • y⟫_ℝ

end CondatPD.FB


