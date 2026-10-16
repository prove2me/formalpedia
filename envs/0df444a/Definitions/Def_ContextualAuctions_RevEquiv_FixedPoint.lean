-- Prove2me | Definitions.Def_ContextualAuctions_RevEquiv_FixedPoint
-- name    : ContextualAuctions_RevEquiv_FixedPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:45.937265+00:00
-- url     : https://prove2.me/theorems/b2a55551-8e27-455e-9c17-c3186ad84eb4
-- title:
--   §3.3 — the pacing domain X, the objective f, total variation V(u,Ω) (Definition 3), V_0, X_0 and the correspondence C*_0
-- statement:
--   This file fixes the fixed-point layer of §3.3, used as the hypothesis of Theorem 2.
--
--   1. $\mathcal X$ is the set of pacing functions $\mu$ that are Lebesgue integrable on $\Theta$ and take values in $[0,\omega/B_{\min}]$ on $\Theta$.
--   2. For pacing functions $\mu,\hat\mu$, the objective is $f(\mu,\hat\mu)=\mathbb E_{(w,B)\sim G}\big[q^\mu(w,B,\hat\mu(w,B))\big]$.
--   3. (Definition 3) For an open $\Omega\subset\mathbb R^m$ and $u\in L_1(\Omega)$, the total variation is
--   $$V(u,\Omega)=\sup\Big\{\int_\Omega u(z)\,\operatorname{div}\varphi(z)\,dz\ :\ \varphi\in C^1_c(\Omega,\mathbb R^m),\ \|\varphi\|_\infty\le1\Big\},$$
--   where $\operatorname{div}\varphi=\sum_{i=1}^m\partial\varphi_i/\partial z_i$ and $\|\varphi\|_\infty=\sup_z\|\varphi(z)\|$ with the Euclidean norm.
--   4. $V(\mu,\Theta)$ is the total variation of $\mu$ viewed as a function on $\Theta\subset\mathbb R^{d+1}$ (coordinates $(w_1,\dots,w_d,B)$), and $V_0=(d+1)U^{d+1}\omega/B_{\min}$.
--   5. $\mathcal X_0=\{\mu\in\mathcal X : V(\mu,\Theta)\le V_0\}$, and for $\mu\in\mathcal X_0$,
--   $$C^*_0(\mu)=\operatorname*{arg\,min}_{\hat\mu\in\mathcal X_0} f(\mu,\hat\mu).$$
--
--   A fixed point $\mu\in C^*_0(\mu)$ is an equilibrium pacing function for first price auctions; Theorem 2 shows that the same $\mu$ works for every standard auction.
--
--   **Formalization Note** $V(u,\Omega)$ takes values in the extended reals, so that the bound $V\le V_0$ is not satisfied by a junk value when the supremum is infinite. Pacing functions are functions, not $L_1$ classes; $C^*_0(\mu)$ is the set of minimizers of $f(\mu,\cdot)$ over $\mathcal X_0$ (attained minimum).
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 9–10, §3.3, X and f (p. 9), Definition 3, Lemma 3 (V_0), X_0 and C*_0 (p. 10)

import Mathlib
import Definitions.Def_ContextualAuctions_RevEquiv_Setting

namespace ContextualAuctions.RevEquiv

open MeasureTheory
open Classical

noncomputable section

/-- The bounded, Lebesgue-integrable pacing functions of §3.3. -/
def Xset (M : Model) : Set (Buyer M → ℝ) :=
  {μ | IsPacing M μ ∧ IntegrableOn μ (Theta M) (volume : Measure (Buyer M)) ∧
    ∀ θ ∈ Theta M, μ θ ∈ Set.Icc 0 (omega M / M.Bmin)}

/-- The combined dual objective of §3.3. -/
def fObj (M : Model) (μ μhat : Buyer M → ℝ) : ℝ :=
  ∫ θ, qDual M μ θ (μhat θ) ∂M.G

/-- Divergence of a C¹ vector field on Euclidean coordinate space. -/
def divergence {m : ℕ} (φ : (Fin m → ℝ) → (Fin m → ℝ))
    (z : Fin m → ℝ) : ℝ :=
  ∑ i, (fderiv ℝ φ z (Pi.single i 1)) i

/-- Multivariate total variation, with extended values to preserve infinity. -/
def totVar {m : ℕ} (u : (Fin m → ℝ) → ℝ) (Ω : Set (Fin m → ℝ)) : EReal :=
  sSup {v : EReal | ∃ φ : (Fin m → ℝ) → (Fin m → ℝ),
    ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω ∧
    (∀ z, Real.sqrt (∑ i, (φ z i) ^ 2) ≤ 1) ∧
    v = (↑(∫ z in Ω, u z * divergence φ z ∂(volume : Measure (Fin m → ℝ))) : EReal)}

/-- Total variation on the type rectangle, transported to `d+1` coordinates. -/
def Vtheta (M : Model) (μ : Buyer M → ℝ) : EReal :=
  totVar (fun z : Fin (M.d + 1) → ℝ => μ (Fin.init z, z (Fin.last M.d)))
    {z | (Fin.init z, z (Fin.last M.d)) ∈ Theta M}

/-- The variation bound in Lemma 3. -/
def V0 (M : Model) : ℝ :=
  (M.d + 1 : ℕ) * M.U ^ (M.d + 1) * omega M / M.Bmin

/-- The bounded-variation pacing domain of §3.3. -/
def X0 (M : Model) : Set (Buyer M → ℝ) :=
  {μ | μ ∈ Xset M ∧ Vtheta M μ ≤ (V0 M : EReal)}

/-- The minimizer correspondence on `X₀`. -/
def C0star (M : Model) (μ : Buyer M → ℝ) : Set (Buyer M → ℝ) :=
  {μhat | μhat ∈ X0 M ∧ ∀ ν ∈ X0 M, fObj M μ μhat ≤ fObj M μ ν}

end
end ContextualAuctions.RevEquiv


