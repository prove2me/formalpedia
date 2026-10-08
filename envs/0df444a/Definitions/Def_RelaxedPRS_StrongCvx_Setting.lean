-- Prove2me | Definitions.Def_RelaxedPRS_StrongCvx_Setting
-- name    : RelaxedPRS_StrongCvx_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:10:58.840375+00:00
-- url     : https://prove2.me/theorems/864674dd-483e-451e-b14f-57edfb591914
-- title:
--   §1.2–§1.10, pp. 3–8 — refl, T_PRS, (T_PRS)_λ, relaxed PRS (Algorithm 1), x_g, x_f, the prox subgradients, strong convexity, Lipschitz gradients, S_f, Λ_k, the λ-weighted average
-- statement:
--   Throughout, $\mathcal H$ is a real Hilbert space, $\gamma>0$, and $f,g:\mathcal H\to(-\infty,\infty]$ are closed, proper and convex. The proximal maps $\mathbf{prox}_{\gamma f},\mathbf{prox}_{\gamma g}$ enter as maps $P_f,P_g:\mathcal H\to\mathcal H$. This file defines the objects shared by every mission of Davis and Yin's analysis of relaxed Peaceman–Rachford splitting.
--
--   1. The **reflection** $\mathbf{refl}_{\gamma f}=2\,\mathbf{prox}_{\gamma f}-I_{\mathcal H}$ and the **PRS operator** $T_{\mathrm{PRS}}=\mathbf{refl}_{\gamma f}\circ\mathbf{refl}_{\gamma g}$ (p. 4).
--   2. The **averaged map** $(T_{\mathrm{PRS}})_\lambda=(1-\lambda)I_{\mathcal H}+\lambda T_{\mathrm{PRS}}$ (p. 4).
--   3. A **relaxed PRS run** (Algorithm 1, p. 5) with relaxation parameters $(\lambda_k)_{k\ge0}$: a sequence $(z^k)_{k\ge0}$ with
--   $$z^{k+1}=(1-\lambda_k)z^k+\lambda_k\,\mathbf{refl}_{\gamma f}\circ\mathbf{refl}_{\gamma g}(z^k)\qquad(k\ge0).$$
--   4. The **auxiliary points** of Lemma 1.1 (p. 7), $x_g=\mathbf{prox}_{\gamma g}(z)$ and $x_f=\mathbf{prox}_{\gamma f}(\mathbf{refl}_{\gamma g}(z))$, and the **prox subgradients**
--   $$\widetilde\nabla g(x_g)=\tfrac1\gamma(z-x_g),\qquad\widetilde\nabla f(x_f)=\tfrac1\gamma(\mathbf{refl}_{\gamma g}(z)-x_f).$$
--   5. **$\mu$-strong convexity** of an extended-valued $f$ (§1.10, p. 7): for all $x,y$ and $t\in[0,1]$,
--   $$f(tx+(1-t)y)+\tfrac{\mu}{2}t(1-t)\|x-y\|^2\le t f(x)+(1-t)f(y).$$
--   6. "**$\nabla f$ is $(1/\beta)$-Lipschitz**": $f$ is real-valued, convex and (Fréchet) differentiable, and its gradient is $(1/\beta)$-Lipschitz.
--   7. The **regularity term** (1.14), p. 8, evaluated at specified subgradients $u=\widetilde\nabla f(x)$, $v=\widetilde\nabla f(y)$:
--   $$S_f(x,y)=\max\Big\{\frac{\mu_f}{2}\|x-y\|^2,\ \frac{\beta_f}{2}\|u-v\|^2\Big\}.$$
--   8. The partial sum $\Lambda_k=\sum_{i=0}^k\lambda_i$ of (1.3), p. 3, and the $\lambda$-weighted average $\overline{x}^k=\frac1{\Lambda_k}\sum_{i=0}^k\lambda_i x^i$ of a sequence (p. 4).
--
--   These are the objects every statement of the series is written in.
--
--   **Formalization Note** Functions are `EReal`-valued; closed, proper and convex is the published `IsProperClosedConvex`, and a prox map is any map satisfying the published `IsProx` (for $\gamma>0$ it is the unique proximal map). The definitions themselves impose no hypotheses: $\gamma>0$, $\lambda_k\in(0,1]$, $\mu_f,\beta_f\ge0$ and "$\beta_f>0\Rightarrow\nabla f$ is $(1/\beta_f)$-Lipschitz" are binders of the theorems that use them. In Lean $\gamma^{-1}=0$ at $\gamma=0$ and $\Lambda_k^{-1}=0$ at $\Lambda_k=0$; both cases are excluded by those binders. The prox subgradients are difference quotients by definition; that they lie in $\partial f(x_f)$, $\partial g(x_g)$ is the content of Proposition 1.1 Part 1 and Lemma 1.1. $S_f$ is defined at the subgradients the paper's proofs use, since (1.14) leaves the choice of $\widetilde\nabla f$ implicit. Strong convexity in `EReal` uses Mathlib's convention $0\cdot(\pm\infty)=0$, so its endpoints $t=0,1$ are trivial, as on paper.
-- source:
--   Davis & Yin, Faster convergence rates of relaxed Peaceman-Rachford and ADMM under regularity assumptions, arXiv:1407.5210v3, pp. 3–8, §1.2, Algorithm 1, Lemma 1.1, (1.14)

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_MoreauProx_Characterization_GammaZero

open scoped InnerProductSpace
open Finset

namespace RelaxedPRS.StrongCvx

/-- The reflection `2 prox_{γ f} - I` of §1.2, p. 4. -/
def refl {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : H → H) (z : H) : H := (2 : ℝ) • P z - z

/-- The Peaceman–Rachford operator `refl_{γ f} ∘ refl_{γ g}`. -/
def TPRS {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Pf Pg : H → H) (z : H) : H := refl Pf (refl Pg z)

/-- The averaged PRS operator `(1-λ)I + λ T_PRS`. -/
def Tlam {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Pf Pg : H → H) (lam : ℝ) (z : H) : H :=
  (1 - lam) • z + lam • TPRS Pf Pg z

/-- Algorithm 1, p. 5, with its relaxation bound imposed on each theorem using a run. -/
def IsPRSRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Pf Pg : H → H) (lam : ℕ → ℝ) (z : ℕ → H) : Prop :=
  ∀ k, z (k + 1) = (1 - lam k) • z k + lam k • TPRS Pf Pg (z k)

/-- The first auxiliary point of Lemma 1.1. -/
def xg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Pg : H → H) (z : H) : H := Pg z

/-- The second auxiliary point of Lemma 1.1. -/
def xf {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Pf Pg : H → H) (z : H) : H := Pf (refl Pg z)

/-- The proximal subgradient of `g` selected in Lemma 1.1. -/
noncomputable def gtG {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (Pg : H → H) (z : H) : H := γ⁻¹ • (z - xg Pg z)

/-- The proximal subgradient of `f` selected in Lemma 1.1. -/
noncomputable def gtF {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (γ : ℝ) (Pf Pg : H → H) (z : H) : H :=
  γ⁻¹ • (refl Pg z - xf Pf Pg z)

/-- Strong convexity for a proper extended-real function, §1.10, p. 7. -/
def IsStrongCvxE {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : ℝ) (f : H → EReal) : Prop :=
  ∀ x y : H, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t • x + (1 - t) • y) + ((μ / 2 * t * (1 - t) * ‖x - y‖ ^ 2 : ℝ) : EReal)
      ≤ (t : EReal) * f x + ((1 - t : ℝ) : EReal) * f y

/-- A positive `β` certifies that `f` is real-valued, differentiable, and has a
`β⁻¹`-Lipschitz gradient. The implication at `β = 0` is imposed in theorem statements. -/
def HasLipGrad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (β : ℝ) (f : H → EReal) : Prop :=
  ∃ h : H → ℝ, (∀ x, f x = (h x : EReal)) ∧
    ThreeOpSplitting.ConvexRates.IsSmoothConvex β h

/-- The regularity term `S_f(x,y)` of (1.14), for specified subgradients
`u ∈ ∂f(x)` and `v ∈ ∂f(y)`. -/
noncomputable def auxS {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ β : ℝ) (x y u v : H) : ℝ :=
  max (μ / 2 * ‖x - y‖ ^ 2) (β / 2 * ‖u - v‖ ^ 2)

/-- The partial sum `Λ_k` of (1.3), including the zeroth weight. -/
def Lam (lam : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range (k + 1), lam i

/-- The weighted ergodic average of §1.2. In theorems its weights are strictly
positive, so `Λ_k` never vanishes. -/
noncomputable def ergAvg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (lam : ℕ → ℝ) (w : ℕ → H) (k : ℕ) : H :=
  (Lam lam k)⁻¹ • ∑ i ∈ Finset.range (k + 1), lam i • w i

end RelaxedPRS.StrongCvx


