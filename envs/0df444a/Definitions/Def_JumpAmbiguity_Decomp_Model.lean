-- Prove2me | Definitions.Def_JumpAmbiguity_Decomp_Model
-- name    : JumpAmbiguity_Decomp_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:27.32816+00:00
-- url     : https://prove2.me/theorems/5ad9313b-7d55-490d-a185-e30dd5449898
-- title:
--   §2 and (A.1), (10)–(15): jump market and robust generator
-- statement:
--   A market has $m$ risky assets and $n$ jump types. The matrix $\Sigma$ gives diffusion coefficients, the matrix $J$ gives jump coefficients, $\mu$ gives expected returns, $r$ is the bond rate, $\lambda_k$ is the reference intensity of jump type $k$, and $\Phi_k$ is its jump-size law. Risk aversion is $\gamma$ and ambiguity aversion is $\phi$. A portfolio $\pi$ is admissible when $\pi'J_k\in[0,1]$ for every jump type.
--
--   For exposure $a$, an alternative jump model changes the intensity by a positive factor $\vartheta$ and the jump-size law by a positive density $\varphi$ normalized to integrate to one. Its contribution to the pointwise robust generator is
--
--   $$
--   L_k(a,\vartheta,\varphi)=\lambda_k\int\left[\frac{(1+ay)^{1-\gamma}-1}{1-\gamma}\,\vartheta\varphi(y)+\frac{\vartheta\varphi(y)\log(\vartheta\varphi(y))+1-\vartheta\varphi(y)}{\phi}\right]d\Phi_k(y).
--   $$
--
--   The generator contains the actual infimum of $L_k$ over admissible alternative models. It also defines the transformed matrix $\widehat J=\Sigma^{-1}J$, transformed return $\widehat\mu=\Sigma^{-1}(\mu-r\mathbf1)$, their column-space decomposition, the worst-case factors of (10)–(11), and the reduced objective in (A.10). These definitions supply the common model for both propositions.
--
--   **Formalization Note** The theorem concerns the pointwise generator after the value-function ansatz, not a stochastic verification theorem. The jump laws are probability measures supported on $(-1,\infty)$. Real powers outside that support have no effect on the integrals. The real-valued tilt requires explicit integrability, and the alternative-model class requires integrability of the combined integrand. Excluded pairs have extended value $+\infty$ because that integrand has an integrable lower bound, so this restriction preserves the infimum. Positive $\gamma\ne1$, $\phi$, and $\lambda_k$ are explicit.
-- source:
--   Jin, Luo & Zeng, Tail Risk and Robust Portfolio Decisions, SSRN working paper 2865064 (version of April 18, 2017), pp. 7–15 (PDF 8–16), §2, §3, (A.1), (10)–(15)

import Mathlib

open MeasureTheory

namespace JumpAmbiguity.Decomp

noncomputable section

/-- The constant market parameters in §2, with time suppressed as in §3. -/
structure Market (m n : ℕ) where
  Sig : Matrix (Fin m) (Fin m) ℝ
  J : Matrix (Fin m) (Fin n) ℝ
  mu : Fin m → ℝ
  r : ℝ
  lam : Fin n → ℝ
  Phi : Fin n → Measure ℝ
  γ : ℝ
  phi : ℝ

/-- The standing assumptions from §2, with positivity and the CRRA domain made explicit. -/
def Market.Standing {m n : ℕ} (M : Market m n) : Prop :=
  n ≤ m ∧ IsUnit M.Sig.det ∧ M.J.rank = n ∧
  (∀ i k, M.J i k ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ k, IsProbabilityMeasure (M.Phi k)) ∧
  (∀ k, M.Phi k (Set.Ioi (-1 : ℝ))ᶜ = 0) ∧
  (∀ k, 0 < M.lam k) ∧ 0 < M.γ ∧ M.γ ≠ 1 ∧ 0 < M.phi

/-- The column `J_k`. -/
def Market.col {m n : ℕ} (M : Market m n) (k : Fin n) : Fin m → ℝ :=
  fun i => M.J i k

/-- The CRRA jump increment divided by `1 - γ`, as in (A.1). -/
def Market.cost {m n : ℕ} (M : Market m n) (a y : ℝ) : ℝ :=
  ((1 + a * y) ^ (1 - M.γ) - 1) / (1 - M.γ)

/-- The combined jump reward and entropy penalty in (A.1). -/
def Market.integrand {m n : ℕ} (M : Market m n) (a θ : ℝ)
    (varphi : ℝ → ℝ) (y : ℝ) : ℝ :=
  M.cost a y * (θ * varphi y) +
    ((θ * varphi y) * Real.log (θ * varphi y) + 1 - θ * varphi y) / M.phi

/-- The contribution of one jump type to the inner problem (A.1). -/
def Market.innerObj {m n : ℕ} (M : Market m n) (k : Fin n) (a θ : ℝ)
    (varphi : ℝ → ℝ) : ℝ :=
  M.lam k * ∫ y, M.integrand a θ varphi y ∂(M.Phi k)

/-- An intensity factor and a normalized positive jump-size density. -/
def Market.AdmissiblePair {m n : ℕ} (M : Market m n) (k : Fin n)
    (a θ : ℝ) (varphi : ℝ → ℝ) : Prop :=
  0 < θ ∧ Measurable varphi ∧ (∀ y, -1 < y → 0 < varphi y) ∧
  Integrable varphi (M.Phi k) ∧
  (∫ y, varphi y ∂(M.Phi k)) = 1 ∧
  Integrable (M.integrand a θ varphi) (M.Phi k)

/-- The genuine infimum over alternative intensity and density pairs. -/
def Market.innerInf {m n : ℕ} (M : Market m n) (k : Fin n) (a : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ θ varphi, M.AdmissiblePair k a θ varphi ∧
    v = M.innerObj k a θ varphi}

/-- The jump-wealth restriction `π'J_k ∈ [0,1]` from p. 8. -/
def Market.Admissible {m n : ℕ} (M : Market m n) : Set (Fin m → ℝ) :=
  {π | ∀ k, π ⬝ᵥ M.col k ∈ Set.Icc (0 : ℝ) 1}

/-- The pointwise robust generator from (A.1), omitting its time-only term. -/
def Market.generator {m n : ℕ} (M : Market m n) (π : Fin m → ℝ) : ℝ :=
  -(M.γ / 2) * ((Matrix.mulVec M.Sig.transpose π) ⬝ᵥ
      (Matrix.mulVec M.Sig.transpose π)) +
    π ⬝ᵥ (M.mu - M.r • (1 : Fin m → ℝ)) + M.r +
    ∑ k : Fin n, M.innerInf k (π ⬝ᵥ M.col k)

/-- The unnormalized worst-case jump tilt from (10)–(11). -/
def Market.psiStar {m n : ℕ} (M : Market m n) (a y : ℝ) : ℝ :=
  Real.exp (M.phi / (M.γ - 1) * ((1 + a * y) ^ (1 - M.γ) - 1))

/-- The worst-case intensity factor (11). -/
def Market.thetaStar {m n : ℕ} (M : Market m n) (k : Fin n) (a : ℝ) : ℝ :=
  ∫ y, M.psiStar a y ∂(M.Phi k)

/-- The worst-case density factor (10). -/
def Market.varphiStar {m n : ℕ} (M : Market m n) (k : Fin n)
    (a y : ℝ) : ℝ :=
  M.psiStar a y / M.thetaStar k a

/-- Finiteness needed for the real-valued expressions in (10)–(11). -/
def Market.JumpIntegrable {m n : ℕ} (M : Market m n) : Prop :=
  ∀ k : Fin n, ∀ a ∈ Set.Icc (0 : ℝ) 1,
    Integrable (M.psiStar a) (M.Phi k) ∧
    Integrable (fun y => M.cost a y * M.psiStar a y) (M.Phi k)

/-- The transformed jump matrix `Ĵ = Σ⁻¹J` from (14). -/
def Market.Jhat {m n : ℕ} (M : Market m n) : Matrix (Fin m) (Fin n) ℝ :=
  M.Sig⁻¹ * M.J

/-- The transformed excess return `µ̂ = Σ⁻¹(µ-r1)` from (14). -/
def Market.muhat {m n : ℕ} (M : Market m n) : Fin m → ℝ :=
  Matrix.mulVec M.Sig⁻¹ (M.mu - M.r • (1 : Fin m → ℝ))

/-- A column of `Ĵ`. -/
def Market.Jhatcol {m n : ℕ} (M : Market m n) (k : Fin n) : Fin m → ℝ :=
  fun i => M.Jhat i k

/-- The space generated by the columns of `Ĵ`. -/
def Market.K {m n : ℕ} (M : Market m n) : Submodule ℝ (Fin m → ℝ) :=
  Submodule.span ℝ (Set.range M.Jhatcol)

/-- The explicit column-space projection used on p. 14. -/
def Market.proj {m n : ℕ} (M : Market m n) (v : Fin m → ℝ) : Fin m → ℝ :=
  Matrix.mulVec M.Jhat
    (Matrix.mulVec ((M.Jhat.transpose * M.Jhat)⁻¹)
      (Matrix.mulVec M.Jhat.transpose v))

/-- The component of `µ̂` in the column space of `Ĵ`. -/
def Market.mubar {m n : ℕ} (M : Market m n) : Fin m → ℝ :=
  M.proj M.muhat

/-- The component of `µ̂` orthogonal to the columns of `Ĵ`. -/
def Market.muperp {m n : ℕ} (M : Market m n) : Fin m → ℝ :=
  M.muhat - M.mubar

/-- The transformed portfolio `π̂ = Σ'π` from (A.6). -/
def Market.pihat {m n : ℕ} (M : Market m n) (π : Fin m → ℝ) : Fin m → ℝ :=
  Matrix.mulVec M.Sig.transpose π

/-- The part of `π̂` in the column space of `Ĵ`. -/
def Market.pibar {m n : ℕ} (M : Market m n) (π : Fin m → ℝ) : Fin m → ℝ :=
  M.proj (M.pihat π)

/-- The part of `π̂` orthogonal to the columns of `Ĵ`. -/
def Market.piperp {m n : ℕ} (M : Market m n) (π : Fin m → ℝ) : Fin m → ℝ :=
  M.pihat π - M.pibar π

/-- Orthogonality to the column space, expressed with the real vector dot product. -/
def Market.IsOrthogonalToK {m n : ℕ} (M : Market m n) (v : Fin m → ℝ) : Prop :=
  ∀ x ∈ M.K, v ⬝ᵥ x = 0

/-- The admissible reduced portfolios in the jump column space. -/
def Market.ReducedAdmissible {m n : ℕ} (M : Market m n) : Set (Fin m → ℝ) :=
  {x | x ∈ M.K ∧ ∀ k, x ⬝ᵥ M.Jhatcol k ∈ Set.Icc (0 : ℝ) 1}

/-- The reduced objective in (A.10), including the entropy of the worst-case model. -/
def Market.reducedObj {m n : ℕ} (M : Market m n) (pibar : Fin m → ℝ) : ℝ :=
  -(M.γ / 2) * (pibar ⬝ᵥ pibar) + M.mubar ⬝ᵥ pibar +
    ∑ k : Fin n,
      M.innerObj k (pibar ⬝ᵥ M.Jhatcol k)
        (M.thetaStar k (pibar ⬝ᵥ M.Jhatcol k))
        (M.varphiStar k (pibar ⬝ᵥ M.Jhatcol k))

/-- The quadratic objective on the orthogonal diffusion component in (A.8). -/
def Market.diffusionObj {m n : ℕ} (M : Market m n) (x : Fin m → ℝ) : ℝ :=
  -(M.γ / 2) * (x ⬝ᵥ x) + x ⬝ᵥ M.muperp

end

end JumpAmbiguity.Decomp


