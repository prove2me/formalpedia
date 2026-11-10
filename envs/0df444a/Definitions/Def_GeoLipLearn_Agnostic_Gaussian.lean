-- Prove2me | Definitions.Def_GeoLipLearn_Agnostic_Gaussian
-- name    : GeoLipLearn_Agnostic_Gaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:51:27.252394+00:00
-- url     : https://prove2.me/theorems/5bb98918-9872-4ce0-b3bd-3c74edf37eaa
-- title:
--   Gaussian function spaces, smoothing, defect and agnostic risk
-- statement:
--   Let $X_d=\mathbb R^d$ have its Euclidean norm and standard Gaussian law $\gamma_d$. The Ornstein–Uhlenbeck operator is
--   $$U_sf(x)=\mathbb E_{z\sim\gamma_d}f(e^{-s}x+\sqrt{1-e^{-2s}}z).$$
--   Clipping is $C_B(t)=\max(-B,\min(B,t))$. The range predicate means $|f(x)|\le B$ for every $x$. Gaussian function norms are the extended nonnegative $L^p$ norms. For differentiable scalar functions define $\Gamma(f)=\mathbb E[(\|Df(x)\|-1)_+^2]$, where the operator norm of the derivative equals the Euclidean gradient norm; the uses here are polynomial functions. A polynomial is a real multivariate polynomial and its evaluation uses the coordinates of $x$.
--
--   A data law is a probability measure on $X_d\times\mathbb R$ with Gaussian first marginal. Bounded labels means $|y|\le B$ almost surely. A variance bound includes square integrability of the label and $\operatorname{Var}(y)\le V^2$, with unrestricted mean. Define
--   $$\operatorname{err}_\ell(f)=\mathbb E|f(x)-y|^\ell,\qquad \operatorname{opt}_\ell=\inf_{\operatorname{Lip}(g)\le1}\operatorname{err}_\ell(g).$$
--   Risk and its infimum are extended nonnegative quantities. The probability predicate requires a measurable subset on which the requested conclusions hold, with mass at least $1-\delta$. These objects provide the common analytic and statistical vocabulary. **Formalization Note** Smoothing and defect use Bochner integrals only on the bounded, Lipschitz, or polynomial functions appearing in the statements; risk uses a nonnegative integral and never collapses a divergent loss to zero.
-- source:
--   Lange, Marcussen and Vasilyan, Geometrically Constrained Learning II: Agnostic Proper Learning of Lipschitz Functions, STOC 2027 submission (manuscript sha256 45cb3c98836346299afa2ee9b2ff10d9d9a3fc8dcbbb9ecc23da2c89a9de615d), pp.11–14, §3; pp.48–49, Appendix C

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace GeoLipLearn.Agnostic

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
noncomputable def gaussian (d : ℕ) : Measure (Space d) := stdGaussian (Space d)
noncomputable def rho (s : ℝ) : ℝ := Real.exp (-s)
noncomputable def sigma (s : ℝ) : ℝ := Real.sqrt (1 - Real.exp (-2*s))
noncomputable def probe {d : ℕ} (s : ℝ) (x z : Space d) : Space d :=
  rho s • x + sigma s • z
noncomputable def ou {d : ℕ} (s : ℝ) (f : Space d → ℝ) (x : Space d) : ℝ :=
  ∫ z, f (probe s x z) ∂gaussian d
noncomputable def normG {d : ℕ} (p : ℝ≥0∞) (f : Space d → ℝ) : ℝ≥0∞ :=
  eLpNorm f p (gaussian d)
noncomputable def clip (B t : ℝ) : ℝ := max (-B) (min B t)
def InRange {d : ℕ} (B : ℝ) (f : Space d → ℝ) : Prop := ∀ x, |f x| ≤ B
noncomputable def defectAt {d : ℕ} (f : Space d → ℝ) (x : Space d) : ℝ :=
  (max (‖fderiv ℝ f x‖ - 1) 0)^2
noncomputable def defect {d : ℕ} (f : Space d → ℝ) : ℝ :=
  ∫ x, defectAt f x ∂gaussian d
abbrev Poly (d : ℕ) := MvPolynomial (Fin d) ℝ
noncomputable def evalPoly {d : ℕ} (p : Poly d) (x : Space d) : ℝ :=
  MvPolynomial.eval (fun i => x i) p
noncomputable def err {d : ℕ} (ell : ℕ) (D : Measure (Space d × ℝ))
    (f : Space d → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (|f z.1 - z.2|^ell) ∂D
noncomputable def opt {d : ℕ} (ell : ℕ) (D : Measure (Space d × ℝ)) : ℝ≥0∞ :=
  ⨅ f : {f : Space d → ℝ // LipschitzWith 1 f}, err ell D f.1
noncomputable def GaussianInput {d : ℕ} (D : Measure (Space d × ℝ)) : Prop :=
  D.map Prod.fst = gaussian d
noncomputable def VarianceBound {d : ℕ} (D : Measure (Space d × ℝ)) (V : ℝ) : Prop :=
  MemLp Prod.snd 2 D ∧ variance Prod.snd D ≤ V^2
noncomputable def BoundedLabels {d : ℕ} (D : Measure (Space d × ℝ)) (B : ℝ) : Prop :=
  ∀ᵐ z ∂D, |z.2| ≤ B
noncomputable def HighProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (δ : ℝ) (P : Ω → Prop) : Prop :=
  ∃ A : Set Ω, MeasurableSet A ∧ ENNReal.ofReal (1-δ) ≤ μ A ∧ ∀ ω ∈ A, P ω

end GeoLipLearn.Agnostic


