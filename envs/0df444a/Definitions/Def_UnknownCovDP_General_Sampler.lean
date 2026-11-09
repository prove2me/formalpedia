-- Prove2me | Definitions.Def_UnknownCovDP_General_Sampler
-- name    : UnknownCovDP_General_Sampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:43.993135+00:00
-- url     : https://prove2.me/theorems/95010a79-3317-4a17-9ef8-b30d0c2bb846
-- title:
--   Definition 2.2 — $(\lambda,\alpha)$-sampler for $\mathcal P_{\mathrm{sub}}$
-- statement:
--   Let $\Sigma$ have the $\Sigma$-marginal of $\mathcal P_{\mathrm{sub}}(d,k)$, let $X\sim N(0,\Sigma)^{\otimes n}$, and let $\mathcal M$ be a randomized algorithm from datasets to $\mathbb R^d$. For $\lambda,\alpha>0$, the algorithm $\mathcal M$ is a **$(\lambda,\alpha)$-sampler** for $\mathcal P_{\mathrm{sub}}$ with sample complexity $n$ if
--   $$\Pr_{\Sigma,\ X,\ \text{coins of }\mathcal M}\bigl[\mathcal M(X)^\top\Sigma\,\mathcal M(X)\ge\lambda^2\bigr]\ge\tfrac1{12}\qquad\text{and}\qquad\|\mathcal M(X)\|_2\le\alpha.$$
--   A sampler outputs a short vector that nevertheless has large energy in the hidden subspace. The mission's lower bound shows that a private sampler must have a long output.
--
--   **Formalization Note** The source puts the norm bound outside the probability. `IsSampler` reads it as a bound for every input and every coin (the output law gives the complement of the ball mass $0$). `IsAESampler` asks for it only almost surely under $\Sigma$, $X$ and the coins, and `IsSampler.toAE` shows that every sampler is an almost-sure sampler. The file also fixes the quadratic form $y^\top Sy$ and the centred experiment probability.
-- source:
--   Gaucher, Linder, Smith, Ullman, Zakynthinou, Dimension-Free Private Mean Estimation is Impossible Without the Covariance, STOC 2027 submission #573 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/573.pdf, Definition 2.2, printed p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_UnknownCovDP_General_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace UnknownCovDP.General

/-!
# Samplers for the random-subspace prior

Definition 2.2 (printed p. 11, PDF p. 12) of Gaucher, Linder, Smith, Ullman, Zakynthinou, STOC 2027
submission #573.

**Formalization Note.** The source's bound `‖ℳ(X)‖₂ ≤ α` sits outside the probability, as a property
of the algorithm. `IsSampler` reads it as holding for every input and every coin (`κ X` gives the
complement of the ball measure zero, for every `X`). `IsAESampler` asks for it only almost surely
under `Σ ∼ covPrior`, `X ∼ N(0,Σ)^{⊗n}` and the coins. Every `IsSampler` is an `IsAESampler`
(`IsSampler.toAE`); lower bounds on samplers are stated for the larger class.
-/

/-- The quadratic form `yᵀ S y`. -/
noncomputable def quadForm {d : ℕ} (S : Mat d) (y : Vec d) : ℝ :=
  y.ofLp ⬝ᵥ (S.mulVec y.ofLp)

/-- `Pr_{Σ∼Q, X∼N(0,Σ)^{⊗n}, coins of ℳ}[ℳ(X) ∈ A(Σ,X)]`. -/
noncomputable def centeredProb {d : ℕ} (Q : Measure (Mat d)) (n : ℕ) (κ : Algorithm d n)
    (A : Mat d → (Fin n → Vec d) → Set (Vec d)) : ℝ≥0∞ :=
  ∫⁻ S, ∫⁻ X, κ X (A S X) ∂(dataLaw n (0 : Vec d) S) ∂Q

/-- Definition 2.2: `κ` is a `(lam, α)`-sampler for `P_sub(d,k)` with sample complexity `n`:
`lam, α > 0`, `Pr[ℳ(X)ᵀ Σ ℳ(X) ≥ lam²] ≥ 1/12`, and `‖ℳ(X)‖₂ ≤ α` on every input and coin. -/
structure IsSampler {d n : ℕ} (k : ℕ) (lam α : ℝ) (κ : Algorithm d n) : Prop where
  lam_pos : 0 < lam
  alpha_pos : 0 < α
  correlated :
    1 / 12 ≤ centeredProb (covPrior d k) n κ (fun S _ => {y | lam ^ 2 ≤ quadForm S y})
  bounded : ∀ X, κ X (Metric.closedBall (0 : Vec d) α)ᶜ = 0

/-- The almost-sure variant of Definition 2.2: the same with `‖ℳ(X)‖₂ ≤ α` almost surely under
`Σ ∼ covPrior d k`, `X ∼ N(0,Σ)^{⊗n}` and the coins. -/
structure IsAESampler {d n : ℕ} (k : ℕ) (lam α : ℝ) (κ : Algorithm d n) : Prop where
  lam_pos : 0 < lam
  alpha_pos : 0 < α
  correlated :
    1 / 12 ≤ centeredProb (covPrior d k) n κ (fun S _ => {y | lam ^ 2 ≤ quadForm S y})
  bounded_ae :
    centeredProb (covPrior d k) n κ (fun _ _ => (Metric.closedBall (0 : Vec d) α)ᶜ) = 0

/-- Every sampler in the sense of Definition 2.2 is an almost-sure sampler. -/
lemma IsSampler.toAE {d n k : ℕ} {lam α : ℝ} {κ : Algorithm d n} (h : IsSampler k lam α κ) :
    IsAESampler k lam α κ :=
  ⟨h.lam_pos, h.alpha_pos, h.correlated, by simp [centeredProb, h.bounded]⟩

end UnknownCovDP.General


