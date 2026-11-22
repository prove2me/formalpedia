-- Prove2me | Definitions.Def_SelfSelReg_Supplement_ProjectedSample
-- name    : SelfSelReg_Supplement_ProjectedSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T05:15:20.548356+00:00
-- url     : https://prove2.me/theorems/8e8703e3-3cdf-42c4-bb88-bf85cd6a8fb8
-- title:
--   Projected samples $(X,\,U\widetilde X^{\otimes r},\,Y_{\max})$ with $\widetilde X=X+\mathrm iX^\prime$, and their law
-- statement:
--   Theorem 8.1 assumes "fresh samples $(X,U\widetilde X^{\otimes r},Y_{\max})$ where $\widetilde X=X+\mathrm iX'$". Here $(X,Y_{\max})$ is an observation of the self-selection model with regressors $w_1,\dots,w_k$, the vector $X'\sim N(0,I_n)$ is independent of it, and $U\in\mathbb R^{p\times n^r}$ is a projection map, so that
--
--   $$
--   \bigl(U\widetilde X^{\otimes r}\bigr)_a=\sum_{(j_1,\dots,j_r)\in[n]^r}U_{a,(j_1,\dots,j_r)}\prod_{h=1}^r\bigl(X_{j_h}+\mathrm iX'_{j_h}\bigr)\in\mathbb C\qquad(a\in[p]).
--   $$
--
--   The bundle defines this vector and two laws:
--
--   1. the law of $(X,\operatorname{Re}U\widetilde X^{\otimes r},\operatorname{Im}U\widetilde X^{\otimes r},Y_{\max})\in\mathbb R^{n+2p+1}$, the projected sample of Theorem 8.1(i);
--   2. the law of $(X,X',\operatorname{Re}U\widetilde X^{\otimes r},\operatorname{Im}U\widetilde X^{\otimes r},Y_{\max})\in\mathbb R^{2n+2p+1}$, used for Theorem 8.1(ii): the odd features (108) contain the coordinate $\widetilde X_\ell=X_\ell+\mathrm iX'_\ell$, so the supplied sample must carry $X'$ as well.
--
--   The projected samples are how the estimation routine works with order-$r$ tensor features without ever forming a vector of $n^r$ entries.
--
--   **Formalization Note** A complex vector is stored as its real part followed by its imaginary part. Independent draws from these laws are "fresh": they are independent of the recovered list and of $U$, which are fixed beforehand.
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), Theorem 8.1, p.55 (PDF p.58); Section 8.1.2, (107), (108), pp.56–57 (PDF pp.59–60)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw
import Definitions.Def_SelfSelReg_Tensor

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

namespace Supplement

/-- The projected complex tensor power `U X̃^{⊗r} ∈ ℂᵖ`, `X̃ = X + iX′` (Theorem 8.1 and (107), (108),
pp.55–57, PDF pp.58–60): coordinate `a` is `Σ_J U_{a,J} ∏_h (x_{J_h} + i x′_{J_h})`. -/
noncomputable def projectedComplex {n p r : ℕ} (U : Matrix (Fin p) (Fin r → Fin n) ℝ)
    (x x' : EuclideanSpace ℝ (Fin n)) : Fin p → ℂ :=
  fun a => ∑ J, (U a J : ℂ) * ∏ h, ((x (J h) : ℂ) + Complex.I * (x' (J h) : ℂ))

/-- One projected sample `(X, U X̃^{⊗r}, Y_max)` as a vector of `ℝ^{n+2p+1}`: coordinates `0, …, n − 1`
are `X`, the next `p` are `Re(U X̃^{⊗r})`, the next `p` are `Im(U X̃^{⊗r})`, the last is `Y_max`. -/
noncomputable def projectedSampleOf {n k p r : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (U : Matrix (Fin p) (Fin r → Fin n) ℝ)
    (z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 2 * p + 1)) :=
  WithLp.toLp 2 fun m =>
    if hX : (m : ℕ) < n then z.1.1 ⟨m, hX⟩
    else if hRe : (m : ℕ) < n + p then (projectedComplex U z.1.1 z.2 ⟨m - n, by omega⟩).re
    else if hIm : (m : ℕ) < n + 2 * p then (projectedComplex U z.1.1 z.2 ⟨m - (n + p), by omega⟩).im
    else yMax w z.1.1 z.1.2

/-- **The law of one projected sample** `(X, U X̃^{⊗r}, Y_max)`.

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), Theorem 8.1, p.55 (PDF p.58): "fix a projection map U : ℝ^{n^r} → ℝᵖ,
where U ∈ ℝ^{p×n^r} has orthonormal rows. Assume we are given fresh samples (X, U X̃^{⊗r}, Y_max) where
X̃ = X + iX′."

`(X, ξ)` has the law `jointLaw n k` of the model and `X′ ∼ N(0, I_n)` is independent of it (§4.4, (13),
p.17: the complex component of the Hermite representation).

**Formalization Note.** The complex vector `U X̃^{⊗r}` is stored as its real and imaginary parts. A
stream of independent draws from this law is "fresh": it is independent of the recovered list and of
`U`, which are fixed before it. -/
noncomputable def projectedSampleLaw {n k p r : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (U : Matrix (Fin p) (Fin r → Fin n) ℝ) :
    Measure (EuclideanSpace ℝ (Fin (n + 2 * p + 1))) :=
  ((jointLaw n k).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (projectedSampleOf w U)

/-- One projected sample that also carries the complex component: `(X, X′, U X̃^{⊗r}, Y_max)` as a
vector of `ℝ^{2n+2p+1}` (`X`, then `X′`, then real parts, imaginary parts, and `Y_max` last). -/
noncomputable def projectedSampleOfOdd {n k p r : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (U : Matrix (Fin p) (Fin r → Fin n) ℝ)
    (z : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin k)) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (2 * n + 2 * p + 1)) :=
  WithLp.toLp 2 fun m =>
    if hX : (m : ℕ) < n then z.1.1 ⟨m, hX⟩
    else if hX' : (m : ℕ) < 2 * n then z.2 ⟨m - n, by omega⟩
    else if hRe : (m : ℕ) < 2 * n + p then
      (projectedComplex U z.1.1 z.2 ⟨m - 2 * n, by omega⟩).re
    else if hIm : (m : ℕ) < 2 * n + 2 * p then
      (projectedComplex U z.1.1 z.2 ⟨m - (2 * n + p), by omega⟩).im
    else yMax w z.1.1 z.1.2

/-- The law of one projected sample for the odd features, `(X, X′, U X̃^{⊗r}, Y_max)`.

**Formalization Note.** The odd coordinate feature (108), p.57 (PDF p.60),
`Ψ^U_{odd,ℓ}(X, X′) = Re[(U X̃^{⊗r})(U X̃^{⊗r})ᵀ X̃_ℓ]/√((2r+1)!)`, contains `X̃_ℓ = X_ℓ + iX′_ℓ`, and
Algorithm 8.1 takes features "evaluated from the supplied samples"; so for the odd call the supplied
sample carries `X′` as well. -/
noncomputable def projectedSampleLawOdd {n k p r : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (U : Matrix (Fin p) (Fin r → Fin n) ℝ) :
    Measure (EuclideanSpace ℝ (Fin (2 * n + 2 * p + 1))) :=
  ((jointLaw n k).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))).map (projectedSampleOfOdd w U)

end Supplement

end SelfSelReg


