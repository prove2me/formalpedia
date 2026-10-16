-- Prove2me | Definitions.Def_ContextualAuctions_PoA_FixedPoint
-- name    : ContextualAuctions_PoA_FixedPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:45.54369+00:00
-- url     : https://prove2.me/theorems/00e83f1e-f748-4bb9-86ab-516a3079e1d0
-- title:
--   §3.3 — pacing fixed-point domain and bounded variation
-- statement:
--   The **pacing domain** $X$ consists of measurable functions $\mu:\Theta\to[0,\omega/B_{\min}]$ that are Lebesgue integrable on the buyer-type rectangle $\Theta$. For two such functions, the combined objective is
--   $$
--   f(\mu,\widehat\mu)=\mathbb E_{(w,B)\sim G}\bigl[q^\mu(w,B,\widehat\mu(w,B))\bigr].
--   $$
--   The **total variation** $V(\mu,\Theta)$ is the supremum of integrals of $\mu\,\mathrm{div}\,\varphi$ over continuously differentiable vector fields with compact support in $\Theta$ and pointwise Euclidean norm at most one. Let $V_0=(d+1)U^{d+1}\omega/B_{\min}$. The restricted domain and minimizer correspondence are
--   $$
--   X_0=\{\mu\in X:V(\mu,\Theta)\le V_0\},\qquad C_0^*(\mu)=\operatorname*{argmin}_{\widehat\mu\in X_0}f(\mu,\widehat\mu).
--   $$
--   A fixed point $\mu\in C_0^*(\mu)$ is the pacing equilibrium relevant to liquid welfare.
--
--   **Formalization Note** Variation takes values in extended reals, so infinite variation cannot satisfy the bound through an empty or unbounded real supremum. Coordinate vectors use the Euclidean length specified in §2.1. Functions represent the paper's $L_1$ classes.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 9–10, §3.3, Definition 3

import Mathlib
import Definitions.Def_ContextualAuctions_PoA_Setting

namespace ContextualAuctions.PoA

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
end ContextualAuctions.PoA


