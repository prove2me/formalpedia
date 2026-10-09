-- Prove2me | Definitions.Def_PhilipponMultiplicity_ParameterStalk
-- name    : PhilipponMultiplicity_ParameterStalk
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-09T00:57:27.438607+00:00
-- url     : https://prove2.me/theorems/8741cb72-6bd3-4541-a02f-c76b92dd5ff9
-- title:
--   Parameter stalks and finite evaluation of their coefficient fractions
-- statement:
--   Let $F\subseteq\mathbf P^N$ be an embedded commutative algebraic group over a field $K$, and fix a parameter $y$ and pivot $c$ with $Y_c(y)\ne0$. Let $R_c$ be the quotient of the polynomial ring by the vanishing ideal of all normalized group points in that chart. Define
--   $$\mathfrak p_y=\ker(\operatorname{ev}_{Y(y)/Y_c(y)}:R_c\to K),\qquad S_y=(R_c)_{\mathfrak p_y}.$$
--   The evaluation ideal is prime because the target is a field. For each $a\in S_y$, choose its localization fraction $n_a/s_a$ with $s_a\notin\mathfrak p_y$. Define its chosen fraction value at a group point $z$ as the quotient of the two evaluations when $Y_c(z)\ne0$, and as zero otherwise. The field quotient uses the usual total inverse operation even if a denominator vanishes away from $y$.
--
--   For a polynomial with coefficients in $S_y$, its form value at $(x,z)$ is the finite sum over its support of the chosen coefficient fraction value times the corresponding monomial in the selected projective representative of $x$.
--
--   **Formalization Note.** These are definitions in the actual normalized chart coordinate ring. They neither assert existence of translation families nor assert that chosen fraction evaluation is a global ring homomorphism. Each denominator is nonzero at the base parameter. Applications restrict to a neighborhood where the finitely many denominators are nonzero; finite support is retained explicitly in the form value.
-- source:
--   Coordinate-ring stalks on affine schemes: Stacks Project, Section 26.5, Lemma 26.5.4(6), https://stacks.math.columbia.edu/tag/01HR . Localization fractions: Section 10.9, https://stacks.math.columbia.edu/tag/00CM . The chosen pointwise representative evaluation is an auxiliary construction for parameter forms in the projective point model; it is not asserted to be a ring homomorphism outside its local domain.

import Definitions.Def_PhilipponMultiplicity_ParameterChart
set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.ParameterStalk
universe u
variable {K : Type u} [Field K] (F : EmbeddedCommutativeGroup K)
  (c : Fin (F.ambientDimension + 1)) (y : F.Point) (hy : y.val.rep c ≠ 0)

/-- The evaluation prime of the actual normalized parameter-chart coordinate ring. -/
def pointIdeal : Ideal (ParameterChart.CoordinateRing F c) :=
  RingHom.ker (ParameterChart.quotientEval F c y hy)

instance pointIdeal_isPrime : (pointIdeal F c y hy).IsPrime := RingHom.ker_isPrime _

/-- Localization at the parameter point, as opposed to localization at one element. -/
abbrev Ring := Localization.AtPrime (pointIdeal F c y hy)

def numerator (a : Ring F c y hy) : ParameterChart.CoordinateRing F c :=
  (IsLocalization.sec (pointIdeal F c y hy).primeCompl a).1

def denominator (a : Ring F c y hy) : (pointIdeal F c y hy).primeCompl :=
  (IsLocalization.sec (pointIdeal F c y hy).primeCompl a).2

/-- Evaluate a chosen fraction representative; only its germ near y is intended.
No ring-homomorphism claim is made at points where its denominator vanishes. -/
def value (a : Ring F c y hy) (z : F.Point) : K := by
  classical
  exact if hz : z.val.rep c ≠ 0 then
    ParameterChart.quotientEval F c z hz (numerator F c y hy a) /
      ParameterChart.quotientEval F c z hz (denominator F c y hy a).val
  else 0

/-- Finite evaluation of a polynomial with parameter-stalk coefficients. -/
def formValue (P : MvPolynomial (Fin (F.ambientDimension + 1)) (Ring F c y hy))
    (x z : F.Point) : K :=
  ∑ m ∈ P.support,
    value F c y hy (P.coeff m) z * m.prod (fun j n => x.val.rep j ^ n)

end PhilipponMultiplicity.ParameterStalk


