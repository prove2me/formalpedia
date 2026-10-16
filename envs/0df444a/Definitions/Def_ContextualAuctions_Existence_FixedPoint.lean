-- Prove2me | Definitions.Def_ContextualAuctions_Existence_FixedPoint
-- name    : ContextualAuctions_Existence_FixedPoint
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T19:29:13.337821+00:00
-- url     : https://prove2.me/theorems/eabb585d-1585-4e0d-96d8-08c7c6276901
-- title:
--   §3.3, pp. 9–10 — X, f(µ, µ̂), ℓ^µ, V(µ, Θ), V₀, X₀ and C*₀, and their images in L₁(Θ)
-- statement:
--   This module defines the objects of the fixed-point argument of §3.3, in the model of the `Setting` module.
--
--   1. The set of candidate pacing functions
--   $$
--   \mathcal X=\{\mu\in L_1(\Theta)\mid \mu(w,B)\in[0,\omega/B_{\min}]\ \ \forall (w,B)\in\Theta\},
--   $$
--   with $L_1(\Theta)$ taken with respect to Lebesgue measure.
--   2. The combined objective $f(\mu,\hat\mu)=\mathbb E_{(w,B)\sim G}\big[q^\mu(w,B,\hat\mu(w,B))\big]$.
--   3. The smallest dual minimizer $\ell^\mu(w,B)=\min\{s\in\arg\min_{t\in[0,\omega/B_{\min}]}q^\mu(w,B,t)\}$.
--   4. The total variation $V(\mu,\Theta)$ of Definition 3, with $\Theta$ viewed as an open subset of $\mathbb R^{d+1}$, and the constant $V_0=(d+1)\max(U^d,U^{d+1})\,\omega/B_{\min}$ of Lemma 3. This equals the printed $(d+1)U^{d+1}\omega/B_{\min}$ when $U\ge1$ (see the note).
--   5. $\mathcal X_0=\{\mu\in\mathcal X\mid V(\mu,\Theta)\le V_0\}$ and the correspondence $C^*_0(\mu)=\arg\min_{\hat\mu\in\mathcal X_0}f(\mu,\hat\mu)$.
--   6. The image of $\mathcal X_0$ in the Banach space $L_1(\Theta)$ of a.e.-classes, and $f$ and $C^*_0$ on classes, for Lemma 4.
--
--   These are the objects to which the Kakutani–Fan–Glicksberg theorem is applied in the proof of Proposition 2.
--
--   **Formalization Note** Elements of $\mathcal X$ are measurable functions that are Lebesgue integrable on $\Theta$; an $L_1$ class has such a representative. $V$ is `EReal`-valued. $\ell^\mu$ is the infimum of the argmin set; that set is nonempty and compact (the paper notes $q^\mu$ is continuous in $t$, online appendix Corollary 1), so the infimum is attained and is the paper's minimum. $f$ on classes is evaluated on any representative; it does not depend on the representative because $G$ has a density and $G(\Theta^c)=0$. The topology of Lemma 4 is the $L_1$ norm topology. **Correction to the printed $V_0$:** the paper prints $(d+1)U^{d+1}\omega/B_{\min}$. Rescaling $(w,B,U,B_{\min},r)$ by $s>0$ leaves $\ell^\mu$ and $\omega/B_{\min}$ unchanged, multiplies $V(\ell^\mu,\Theta)$ by $s^d$ and multiplies the printed constant by $s^{d+1}$. So the printed bound fails for small $U$ whenever $\ell^\mu$ is not constant. The bound for a function that is monotone in each coordinate with values in $[0,\omega/B_{\min}]$ on the box $\Theta$ is $(d+1)U^d\omega/B_{\min}$. The mission uses $\max(U^d,U^{d+1})$, which is the printed constant whenever $U\ge1$.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, pp. 9–10, §3.3, Definition 3, Lemma 3

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_TotalVariation
import Definitions.Def_ContextualAuctions_Existence_Setting

namespace ContextualAuctions.Existence

open MeasureTheory

/-- The set `X = {μ ∈ L₁(Θ) | μ(w,B) ∈ [0, ω/B_min] ∀ (w,B) ∈ Θ}` of §3.3, as measurable pacing
functions that are Lebesgue integrable on `Θ` with values in `[0, ω/B_min]` on `Θ`. -/
def Xset (M : Model) : Set ((Fin M.d → ℝ) × ℝ → ℝ) :=
  {μ | IsPacing M μ ∧ IntegrableOn μ (Theta M) ∧ ∀ θ ∈ Theta M, μ θ ∈ Set.Icc 0 (omega M / M.Bmin)}

/-- The combined objective `f(μ, μ̂) = E_{(w,B) ∼ G}[q^μ(w, B, μ̂(w,B))]` of §3.3. -/
noncomputable def fObj (M : Model) (μ μhat : (Fin M.d → ℝ) × ℝ → ℝ) : ℝ :=
  ∫ θ, qDual M μ θ (μhat θ) ∂M.G

/-- The smallest dual minimizer
`ℓ^μ(w,B) = min {s ∈ argmin_{t ∈ [0, ω/B_min]} q^μ(w,B,t)}` of §3.3. -/
noncomputable def ell (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) (θ : (Fin M.d → ℝ) × ℝ) : ℝ :=
  sInf {s ∈ Set.Icc 0 (omega M / M.Bmin) |
    IsMinOn (qDual M μ θ) (Set.Icc 0 (omega M / M.Bmin)) s}

/-- The identification of `ℝ^{d+1}` (Euclidean) with types `(w, B)`: the first `d` coordinates
are `w`, the last is `B`. -/
def toType {d : ℕ} (x : EuclideanSpace ℝ (Fin (d + 1))) : (Fin d → ℝ) × ℝ :=
  (fun i => x (Fin.castSucc i), x (Fin.last d))

/-- `V(μ, Θ)`: the total variation (Definition 3, with `n = d + 1`) of `μ` on the open set `Θ`,
viewed as a subset of `ℝ^{d+1}`. -/
noncomputable def Vtheta (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) : EReal :=
  totalVariation (fun x => μ (toType x)) (toType ⁻¹' Theta M)

/-- The constant of Lemma 3, `V₀ = (d + 1) max(U^d, U^{d+1}) ω / B_min`. The paper prints
`(d + 1) U^{d+1} ω / B_min`; this is the printed constant whenever `U ≥ 1`. For `U < 1` the printed
bound is false: rescaling `(w, B, U, B_min, r)` by `s` leaves `ℓ^μ` and `ω / B_min` unchanged,
multiplies `V(ℓ^μ, Θ)` by `s^d`, and multiplies the printed constant by `s^{d+1}`. The constant
`(d + 1) U^d ω / B_min` is the bound for a function on `Θ` that is monotone in each coordinate and
takes values in `[0, ω / B_min]`. -/
noncomputable def V0 (M : Model) : ℝ :=
  (M.d + 1) * max (M.U ^ M.d) (M.U ^ (M.d + 1)) * omega M / M.Bmin

/-- `X₀ = {μ ∈ X | V(μ, Θ) ≤ V₀}`. -/
def X0 (M : Model) : Set ((Fin M.d → ℝ) × ℝ → ℝ) :=
  {μ | μ ∈ Xset M ∧ Vtheta M μ ≤ (V0 M : EReal)}

/-- `C*₀(μ) = argmin_{μ̂ ∈ X₀} f(μ, μ̂)`. -/
def C0star (M : Model) (μ : (Fin M.d → ℝ) × ℝ → ℝ) : Set ((Fin M.d → ℝ) × ℝ → ℝ) :=
  {μhat | μhat ∈ X0 M ∧ ∀ ν ∈ X0 M, fObj M μ μhat ≤ fObj M μ ν}

/-- `L₁(Θ)`: integrable functions on `Θ` with respect to Lebesgue measure, as a normed space of
a.e.-classes. -/
noncomputable abbrev L1Theta (M : Model) := Lp ℝ 1 ((volume : Measure ((Fin M.d → ℝ) × ℝ)).restrict (Theta M))

/-- The image of `X₀` in `L₁(Θ)`: the classes of elements of `X₀`. -/
def X0L (M : Model) : Set (L1Theta M) :=
  {g | ∃ μ ∈ X0 M, (g : (Fin M.d → ℝ) × ℝ → ℝ) =ᵐ[volume.restrict (Theta M)] μ}

/-- `f` on `L₁(Θ)` classes, evaluated on representatives. -/
noncomputable def fL (M : Model) (g h : L1Theta M) : ℝ :=
  fObj M (g : (Fin M.d → ℝ) × ℝ → ℝ) (h : (Fin M.d → ℝ) × ℝ → ℝ)

/-- `C*₀` on `L₁(Θ)` classes: `C*₀(g) = argmin_{h ∈ X₀} f(g, h)`. -/
def C0starL (M : Model) (g : L1Theta M) : Set (L1Theta M) :=
  {h | h ∈ X0L M ∧ ∀ k ∈ X0L M, fL M g h ≤ fL M g k}

end ContextualAuctions.Existence


