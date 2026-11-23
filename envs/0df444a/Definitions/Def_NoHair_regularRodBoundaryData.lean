-- Prove2me | Definitions.Def_NoHair_regularRodBoundaryData
-- name    : NoHair_regularRodBoundaryData
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T10:29:59.837694+00:00
-- url     : https://prove2.me/theorems/d884c788-9283-4d74-be72-fd432132dd72
-- title:
--   Regular weighted axial norm and twist data on the compactified Weyl rectangle
-- statement:
--   Use the reciprocal radius $q=1/(m+R)$ and angular variable $c=z/R$. On $0\le q\le 1/(m+\ell)$, $-1\le c\le1$, the fields represent $X/r^2$ and $(Y-2J(3c-c^3))/r^2$. Their first angular derivatives are continuous on the entire rectangle. The fields vanish at the two polar sides, the axial norm has strict inward slope there and is positive in the interior, and the infinity edge carries $1-c^2$ and zero. This definition expresses regular boundary data without dividing by the vanishing polar factor.
-- source:
--   P. T. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Astérisque 321 (2008), §§6.2–6.7, https://arxiv.org/abs/0806.0016. The compactified variables and angular derivative criterion here are an explicit sufficient condition for the platform’s normalized rod estimates.

import Definitions.Def_NoHair_weylBoundaryProfile

noncomputable section
open Set
namespace NoHair.Weyl

/-- The closed prolate coordinate rectangle, with reciprocal radius zero at infinity. -/
def rodRectangle (m ℓ : ℝ) : Set OrbitPoint := Icc 0 (1/(m+ℓ)) ×ˢ Icc (-1) 1

/-- Angular boundary regularity of the weighted axial norm and twist difference.
The two functions and their angular derivatives extend across the full closed rectangle,
including the two endpoints of the horizon interval and both ends of the infinity edge. -/
structure RegularRodBoundaryData (u : ErnstPotentials) (m ℓ J : ℝ) where
  normData : OrbitPoint → ℝ
  twistData : OrbitPoint → ℝ
  normSlope : OrbitPoint → ℝ
  twistSlope : OrbitPoint → ℝ
  normSlope_continuous : ContinuousOn normSlope (rodRectangle m ℓ)
  twistSlope_continuous : ContinuousOn twistSlope (rodRectangle m ℓ)
  norm_derivative : ∀ z ∈ rodRectangle m ℓ,
    HasDerivAt (fun c => normData (z.1,c)) (normSlope z) z.2
  twist_derivative : ∀ z ∈ rodRectangle m ℓ,
    HasDerivAt (fun c => twistData (z.1,c)) (twistSlope z) z.2
  values : ∀ p : OrbitPoint,
    let R := prolateRadius ℓ p
    let r := m+R
    let c := p.2/R
    normData (1/r,c) = u.normSq p/r^2 ∧
      twistData (1/r,c) = (u.twist p - 2*J*(3*c-c^3))/r^2
  poles : ∀ q ∈ Icc 0 (1/(m+ℓ)),
    normData (q,-1) = 0 ∧ normData (q,1) = 0 ∧
    twistData (q,-1) = 0 ∧ twistData (q,1) = 0 ∧
    0 < normSlope (q,-1) ∧ normSlope (q,1) < 0
  interior_pos : ∀ q ∈ Icc 0 (1/(m+ℓ)), ∀ c ∈ Ioo (-1:ℝ) 1, 0 < normData (q,c)
  infinity : ∀ c ∈ Icc (-1:ℝ) 1, normData (0,c) = 1-c^2 ∧ twistData (0,c) = 0

end NoHair.Weyl


