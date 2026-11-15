-- Prove2me | Definitions.Def_UnconditionalKLS_Dunkl_Supplement_Model
-- name    : UnconditionalKLS_Dunkl_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T05:15:29.166207+00:00
-- url     : https://prove2.me/theorems/62f27933-05c8-4eea-b21f-c6da902bf9af
-- title:
--   Orthant laws, inverse Hessian norm, log-concave laws and coordinatewise contractions (§4)
-- statement:
--   This file adds the objects of §4 that the published base model does not contain. Throughout, $\mathbb R^n$ is Euclidean space with coordinates $x_1,\dots,x_n$, and $C_P$ is the base optimal Poincaré constant.
--
--   1. The coordinatewise absolute value $|x| := (|x_1|,\dots,|x_n|)$ and, for a measure $\mu$, the law $\mu_+ := |\cdot|_\#\mu$ of $(|X_1|,\dots,|X_n|)$ for $X\sim\mu$ (a pushforward, not a restriction).
--   2. The open positive orthant $\mathbb R^n_+ = (0,\infty)^n$, the normalizer $Z_V = \int_{\mathbb R^n_+} e^{-V}\,dx \in [0,\infty]$, and the law $\eta_V = Z_V^{-1}\,\mathbf 1_{\mathbb R^n_+} e^{-V}\,dx$ of density proportional to $e^{-V}$ on the orthant. Values of $V$ off the orthant play no role.
--   3. For a set $\Omega$ and $W:\mathbb R^n\to\mathbb R$, the measure $\nu = \mathbf 1_\Omega e^{-W}\,dx$; the Hessian matrix $\nabla^2W(x) = (\partial_i\partial_jW(x))_{ij}$; the $\ell^2\to\ell^2$ operator (spectral) norm $\|M\|_{op}$ of a square matrix; and
--   $$\big\|\mathbb E_\nu[(\nabla^2W)^{-1}]\big\|_{op}\in[0,\infty],$$
--   the operator norm of the entrywise expectation of the inverse Hessian, set to $+\infty$ when some entry of $(\nabla^2W)^{-1}$ is not $\nu$-integrable.
--   4. Log-concavity in the sense of p. 1, without unconditionality: a measure is log-concave if it has density $e^{-U}$ for some $U:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ with convex epigraph, where $e^{-\infty}=0$.
--   5. For $h:(0,\infty)\to(0,\infty)$: its inverse $h^{-1}$ on $(0,\infty)$, the coordinatewise contraction $T(y) = (h(y_1),\dots,h(y_n))$, its inverse $T^{-1}(x) = (h^{-1}(x_1),\dots,h^{-1}(x_n))$, the law $(T^{-1})_\#\eta$, and $r(t) = -(\log h')''(t)$.
--
--   These are the data of Lemma 4.1, Propositions 1.2 and 4.2 and Corollary 4.3; the file contains no inequality.
--
--   **Formalization Note** The matrix inverse is Mathlib's `Matrix` inverse, and the operator norm is that of `Matrix.toEuclideanCLM`, not the default entrywise matrix norm. $h^{-1}$ is `Function.invFunOn h (0,∞)`, which is the true inverse on $(0,\infty)$ and constant off it; only its values on $(0,\infty)$ matter because $\eta$ is carried by the open orthant. Partial derivatives are the base Fréchet partials `d`.
-- source:
--   Pierre Bizeul, Dan Mikulincer, Ilias Zadik, STOC 2027 submission #1161 (October 2026), p. 1 (definition of log-concave), p. 7 (Proposition 1.2), p. 28 (ℝⁿ₊ and μ₊, Lemma 4.1), p. 30 (Proposition 4.2, (4.8)). https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1161.pdf

import Definitions.Def_UnconditionalKLS_Dunkl_Model

open MeasureTheory Filter
open scoped BigOperators ENNReal ContDiff
noncomputable section

namespace UnconditionalKLS.Dunkl.Supplement
open UnconditionalKLS.Dunkl
variable {n : ℕ}

/-- `x ↦ (|x₁|, …, |xₙ|)`. -/
def absCoord (x : Space n) : Space n := WithLp.toLp 2 (fun j => |x j|)

/-- `μ₊`, the law of `(|X₁|, …, |Xₙ|)` for `X ∼ μ` (a pushforward, not a restriction). -/
def plusLaw (μ : Measure (Space n)) : Measure (Space n) := Measure.map absCoord μ

/-- The open positive orthant `ℝⁿ₊ = (0, ∞)ⁿ` (p. 28). -/
def posOrthant : Set (Space n) := {x | ∀ j, 0 < x j}

/-- `∫_{ℝⁿ₊} e^{-V}`. -/
def orthantNormalizer (V : Fn n) : ℝ≥0∞ :=
  ∫⁻ x in posOrthant, ENNReal.ofReal (Real.exp (-V x))

/-- The probability measure on `ℝⁿ₊` with density proportional to `e^{-V}`;
values of `V` off `ℝⁿ₊` are irrelevant. -/
def orthantLaw (V : Fn n) : Measure (Space n) :=
  (orthantNormalizer V)⁻¹ •
    volume.withDensity (posOrthant.indicator fun x => ENNReal.ofReal (Real.exp (-V x)))

/-- The measure with density `e^{-W}` on `Ω` (and zero off `Ω`). -/
def domainLaw (Ω : Set (Space n)) (W : Fn n) : Measure (Space n) :=
  volume.withDensity (Ω.indicator fun x => ENNReal.ofReal (Real.exp (-W x)))

/-- The Hessian matrix `(∂ᵢ∂ⱼW(x))ᵢⱼ`, built from the base partial derivative `d`. -/
def hessMatrix (W : Fn n) (x : Space n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => d (d W j) i x

/-- The `ℓ²→ℓ²` operator (spectral) norm of a real square matrix. -/
def opNorm (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

open Classical in
/-- `‖𝔼_ν[(∇²W)⁻¹]‖_op` for `ν = domainLaw Ω W`, the expectation taken entrywise;
it is `+∞` when some entry of the inverse Hessian is not `ν`-integrable. -/
def avgInvHessNorm (Ω : Set (Space n)) (W : Fn n) : ℝ≥0∞ :=
  if ∀ i j : Fin n, Integrable (fun x => (hessMatrix W x)⁻¹ i j) (domainLaw Ω W) then
    ENNReal.ofReal (opNorm (Matrix.of fun i j => ∫ x, (hessMatrix W x)⁻¹ i j ∂domainLaw Ω W))
  else ⊤

/-- Log-concavity in the sense of p. 1, without unconditionality: a density `e^{-U}` with
`U : ℝⁿ → ℝ ∪ {+∞}` convex (convex epigraph) and `e^{-∞} = 0`. -/
def LogConcaveLaw (μ : Measure (Space n)) : Prop :=
  ∃ U : Space n → WithTop ℝ,
    Convex ℝ {p : Space n × ℝ | U p.1 ≤ (p.2 : WithTop ℝ)} ∧
    μ = volume.withDensity
      (fun x => ENNReal.ofReal (if U x = ⊤ then 0 else Real.exp (-(U x).untopD 0)))

/-- `h⁻¹`, the inverse of `h` restricted to `(0, ∞)`. -/
def hInv (h : ℝ → ℝ) : ℝ → ℝ := Function.invFunOn h (Set.Ioi 0)

/-- The coordinatewise map `T(y) = (h(y₁), …, h(yₙ))`. -/
def contraction (h : ℝ → ℝ) (y : Space n) : Space n := WithLp.toLp 2 (fun j => h (y j))

/-- `T⁻¹(x) = (h⁻¹(x₁), …, h⁻¹(xₙ))`. -/
def contractionInv (h : ℝ → ℝ) (x : Space n) : Space n :=
  WithLp.toLp 2 (fun j => hInv h (x j))

/-- `ν = (T⁻¹)_# η`. -/
def pullbackLaw (h : ℝ → ℝ) (η : Measure (Space n)) : Measure (Space n) :=
  Measure.map (contractionInv h) η

/-- `r(t) = -(log h')''(t)`. -/
def rate (h : ℝ → ℝ) (t : ℝ) : ℝ := -deriv (deriv (fun s => Real.log (deriv h s))) t

end UnconditionalKLS.Dunkl.Supplement


