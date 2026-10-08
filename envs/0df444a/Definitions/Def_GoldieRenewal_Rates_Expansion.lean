-- Prove2me | Definitions.Def_GoldieRenewal_Rates_Expansion
-- name    : GoldieRenewal_Rates_Expansion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:05.749804+00:00
-- url     : https://prove2.me/theorems/1b817448-cbdc-4b02-aa72-99000bb33350
-- title:
--   Theorem 3.2 expansions (3.8), (3.10) with contour terms; kernel K, r, c, r₁ of the proof (pp. 153–154)
-- statement:
--   In the setting of Theorem 3.2, write $\eta$ for the tilted law of $M$, $\hat\eta$ for its transform, $\hat g_{\pm1}$ for the transforms of $g_{\pm1}$, and let $\mathscr C$ be the positively oriented boundary of an admissible rectangle (closure in $D=\{-\beta<\Im\theta<0\}$, all zeros of $1-\hat\eta$ in $D$ inside).
--
--   1. **Expansion (3.8).** For every admissible $\mathscr C$,
--   $$t^\kappa P(R>t)=C_+-\frac1{2\pi}\,\Re\oint_{\mathscr C} e^{-i\theta\log t}\,\frac{\hat g_1(\theta)}{1-\hat\eta(\theta)}\,d\theta+O(t^{-\beta/2}),\qquad t\to\infty.$$
--   2. **Expansion (3.10).** The same with $P(R<-t)$, $C_-$ and $\hat g_{-1}$.
--   3. **Objects of the proof.** For $b>0$, the kernel $K(t):=be^{-bt}\mathbf 1_{t>0}$; $r(t):=e^{\kappa t}P(R>e^t)$;
--   $$c(t):=\frac1{2\pi}\oint_{\mathscr C}e^{-i\theta t}\frac{d\theta}{1-\hat\eta(\theta)},\qquad r_1(t):=C_+-r(t)-(g_1*c)(t)\mathbf 1_{t>0},$$
--   with $(g_1*c)(t)=\int g_1(u)c(t-u)\,du$.
--
--   These are the conclusions of Theorem 3.2 and the functions through which its proof passes.
--
--   **Formalization Note** The paper prints $e^{-i\theta t}$ in (3.8) and (3.10). Its proof (pp. 154–155) works in the logarithmic variable $s=\log t$: it shows $\Re r_1(s)=O(e^{-\beta s/2})$ with $r(s)=e^{\kappa s}P(R>e^s)$ and $g_1*c(s)=\frac1{2\pi}\oint e^{-i\theta s}\hat g_1(\theta)/(1-\hat\eta(\theta))\,d\theta$. The expansions are therefore stated with $e^{-i\theta\log t}$, which is what the proof establishes; read literally with $e^{-i\theta t}$ the contour term would decay exponentially and the statement would be a different (unproved) claim. The contour integral is `RectangleIntegral` (bottom edge left to right, right edge upward, top edge right to left, left edge downward).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, pp. 132–133, Theorem 3.2, (3.8), (3.10); p. 143, (9.3); pp. 153–154, proof of Theorem 3.2

import Mathlib
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_GoldieRenewal_Rates_Transforms
import Definitions.Def_GoldieRenewal_Rates_Model
import Definitions.Def_GoldieRenewal_Implicit_TailConstants

open MeasureTheory ProbabilityTheory Complex Filter Asymptotics

namespace GoldieRenewal.Rates

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The contour term of Goldie 1991, (3.8) (p. 132), for the upper tail, at the variable `t`:
`(1/2π) ℜ ∮_𝒞 e^{−iθ log t} ĝ₁(θ) / (1 − η̂(θ)) dθ`, where `η = tiltedLaw P M κ`,
`ĝ₁ = fourierTransform g₁`, and `𝒞` is the positively oriented boundary of the rectangle with
lower-left corner `z` and upper-right corner `w` (`RectangleIntegral`, counterclockwise).
Formalization Note: the paper prints `e^{−iθt}`; its proof (pp. 154–155) works in the
logarithmic variable `s = log t` (it proves `ℜ r₁(s) = O(e^{−βs/2})` with
`r(s) = e^{κs}P(R > e^s)`), so the exponent is `−iθ log t`. -/
noncomputable def contourTermPos (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (z w : ℂ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (RectangleIntegral
      (fun θ : ℂ => Complex.exp (-(I * θ * (Real.log t : ℂ))) *
        fourierTransform (fun s => (gPos P M R κ s : ℂ)) θ /
          (1 - charTransform (tiltedLaw P M κ) θ)) z w).re

/-- The contour term of Goldie 1991, (3.10) (p. 133), for the lower tail:
`(1/2π) ℜ ∮_𝒞 e^{−iθ log t} ĝ₋₁(θ) / (1 − η̂(θ)) dθ` (same conventions as `contourTermPos`). -/
noncomputable def contourTermNeg (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (z w : ℂ) (t : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (RectangleIntegral
      (fun θ : ℂ => Complex.exp (-(I * θ * (Real.log t : ℂ))) *
        fourierTransform (fun s => (gNeg P M R κ s : ℂ)) θ /
          (1 - charTransform (tiltedLaw P M κ) θ)) z w).re

/-- Conclusion (3.8) of Goldie 1991, Theorem 3.2(i) (p. 132), in its proved form: for every
admissible rectangle contour `𝒞` (see `EnclosesZerosInStrip`),
`t^κ P(R > t) = C₊ − (1/2π) ℜ ∮_𝒞 e^{−iθ log t} ĝ₁(θ)/(1 − η̂(θ)) dθ + O(t^{−β/2})`,
`t → ∞`. -/
def ExpansionPos (P : Measure Ω) (M R : Ω → ℝ) (κ β : ℝ) : Prop :=
  ∀ z w : ℂ, EnclosesZerosInStrip (fun θ => 1 - charTransform (tiltedLaw P M κ) θ) β z w →
    (fun t : ℝ => t ^ κ * P.real {ω | t < R ω} -
        (CPlus P M R κ - contourTermPos P M R κ z w t))
      =O[atTop] (fun t : ℝ => t ^ (-(β / 2)))

/-- Conclusion (3.10) of Goldie 1991, Theorem 3.2(ii) (p. 133), in its proved form: for every
admissible rectangle contour `𝒞`,
`t^κ P(R < −t) = C₋ − (1/2π) ℜ ∮_𝒞 e^{−iθ log t} ĝ₋₁(θ)/(1 − η̂(θ)) dθ + O(t^{−β/2})`,
`t → ∞`. -/
def ExpansionNeg (P : Measure Ω) (M R : Ω → ℝ) (κ β : ℝ) : Prop :=
  ∀ z w : ℂ, EnclosesZerosInStrip (fun θ => 1 - charTransform (tiltedLaw P M κ) θ) β z w →
    (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t} -
        (CMinus P M R κ - contourTermNeg P M R κ z w t))
      =O[atTop] (fun t : ℝ => t ^ (-(β / 2)))

/-- The smoothing kernel `K(t) := b e^{−bt} 1_{t>0}` of the proof of Goldie 1991, Theorem 3.2
(p. 153). -/
noncomputable def smoothingKernel (b : ℝ) (t : ℝ) : ℝ :=
  if 0 < t then b * Real.exp (-(b * t)) else 0

/-- `c(t) := (1/2π) ∮_𝒞 e^{−iθt} dθ / (1 − η̂(θ))` (Goldie 1991, p. 154), with `𝒞` the
positively oriented boundary of the rectangle with corners `z` (lower left) and `w` (upper
right). -/
noncomputable def cFun (η : Measure ℝ) (z w : ℂ) (t : ℝ) : ℂ :=
  (1 / (2 * Real.pi : ℂ)) *
    RectangleIntegral (fun θ : ℂ => Complex.exp (-(I * θ * (t : ℂ))) / (1 - charTransform η θ)) z w

/-- `r₁(t) := C₊ − r(t) − g₁ ∗ c(t) 1_{t>0}` (Goldie 1991, p. 154), where
`g₁ ∗ c(t) = ∫ g₁(u) c(t − u) du`, `η = tiltedLaw P M κ`. Complex valued, since `c` is. -/
noncomputable def r1Fun (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ) (z w : ℂ) (t : ℝ) : ℂ :=
  (CPlus P M R κ : ℂ) - (GoldieRenewal.Implicit.rFun P R κ t : ℂ) -
    (if 0 < t then ∫ u : ℝ, (gPos P M R κ u : ℂ) * cFun (tiltedLaw P M κ) z w (t - u) else 0)

end GoldieRenewal.Rates


