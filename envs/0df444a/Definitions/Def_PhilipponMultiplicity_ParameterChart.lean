-- Prove2me | Definitions.Def_PhilipponMultiplicity_ParameterChart
-- name    : PhilipponMultiplicity_ParameterChart
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-08T23:46:01.958982+00:00
-- url     : https://prove2.me/theorems/e992593a-2fce-4251-b2cb-479f6ee8f64d
-- title:
--   Localized coordinate rings and specialization on projective parameter charts
-- statement:
--   Let $F\subseteq\mathbf P^N$ be an embedded commutative algebraic group over a field $K$. Fix an index $c$ and normalize a point $y$ with $Y_c(y)\ne0$ by $z_j(y)=Y_j(y)/Y_c(y)$. Define the vanishing ideal and chart coordinate ring by
--   $$I_c=\bigcap_{y\in F,\;Y_c(y)\ne0}\ker(\operatorname{ev}_{z(y)}),\qquad R_c=K[Z_0,\ldots,Z_N]/I_c.$$
--   For $H\in K[Z_0,\ldots,Z_N]$, the localized parameter ring is
--   $$R_{c,H}=R_c[1/\overline H].$$
--   A point is valid for $(c,H)$ when $Y_c(y)\ne0$ and $H(z(y))\ne0$. Evaluation at each valid point factors through $R_c$ and extends to a ring homomorphism $R_{c,H}\to K$, sending a quotient polynomial to its value at $z(y)$ and $\overline H^{-1}$ to $H(z(y))^{-1}$.
--
--   These definitions provide concrete coefficient rings and specialization maps for local translation families. They impose no geometric existence, degree, or regularity assumption on such families.
--
--   **Formalization Note.** The coordinate ring is defined from the actual normalized group-point vanishing ideal. The name for the localized ring denotes a principal localization, not a stalk or a claim that the ring is local. Quotient evaluation and localization extension are included as well-defined ring homomorphisms.
-- source:
--   Auxiliary parameter-chart definitions for the forms over affine parameter rings in Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups (2002), Section 3.3, pp.63–64, https://doi.org/10.3929/ethz-a-004445245 . The quotient is explicitly the vanishing ideal of normalized chart points. Principal localization and its universal property: Stacks Project Section 10.9, Proposition 10.9.3, https://stacks.math.columbia.edu/tag/00CM ; affine structure sheaf on principal opens: Section 26.5, Lemma 26.5.1 and Definition 26.5.3, https://stacks.math.columbia.edu/tag/01HR .

import Definitions.Def_PhilipponMultiplicity_Geometry
set_option autoImplicit false
noncomputable section

namespace PhilipponMultiplicity.ParameterChart
universe u
variable {K : Type u} [Field K] (F : EmbeddedCommutativeGroup K)

abbrev PolynomialRing := MvPolynomial (Fin (F.ambientDimension + 1)) K

def coordinates (c : Fin (F.ambientDimension + 1)) (y : F.Point) :
    Fin (F.ambientDimension + 1) → K := fun j => y.val.rep j / y.val.rep c

/-- The actual vanishing ideal of the normalized parameter chart. -/
def ideal (c : Fin (F.ambientDimension + 1)) : Ideal (PolynomialRing F) :=
  ⨅ y : {y : F.Point // y.val.rep c ≠ 0},
    RingHom.ker (MvPolynomial.eval (coordinates F c y.val))

abbrev CoordinateRing (c : Fin (F.ambientDimension + 1)) :=
  PolynomialRing F ⧸ ideal F c

def quotientEval (c : Fin (F.ambientDimension + 1)) (y : F.Point)
    (hy : y.val.rep c ≠ 0) : CoordinateRing F c →+* K :=
  Ideal.Quotient.lift (ideal F c) (MvPolynomial.eval (coordinates F c y)) (by
    intro P hP
    exact (iInf_le (fun z : {z : F.Point // z.val.rep c ≠ 0} =>
      RingHom.ker (MvPolynomial.eval (coordinates F c z.val))) ⟨y,hy⟩) hP)

abbrev LocalRing (c : Fin (F.ambientDimension + 1)) (H : PolynomialRing F) :=
  Localization.Away (Ideal.Quotient.mk (ideal F c) H)

def Valid (c : Fin (F.ambientDimension + 1)) (H : PolynomialRing F) (y : F.Point) : Prop :=
  y.val.rep c ≠ 0 ∧ MvPolynomial.eval (coordinates F c y) H ≠ 0

/-- Specialization of a localized parameter coefficient at a point of its principal chart. -/
def specialize (c : Fin (F.ambientDimension + 1)) (H : PolynomialRing F)
    (y : F.Point) (hy : Valid F c H y) : LocalRing F c H →+* K :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (ideal F c) H)
    (g := quotientEval F c y hy.1) (by
      change IsUnit (MvPolynomial.eval (coordinates F c y) H)
      exact isUnit_iff_ne_zero.mpr hy.2)

end PhilipponMultiplicity.ParameterChart


