-- Prove2me | Definitions.Def_PhilipponMultiplicity_AdditionLaws
-- name    : PhilipponMultiplicity_AdditionLaws
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-30T16:04:53.283993+00:00
-- url     : https://prove2.me/theorems/034f68e2-83e2-49c0-b620-967202434513
-- title:
--   Bihomogeneous addition laws on embedded groups
-- statement:
--   An addition law for a projectively embedded commutative algebraic group is a tuple of bihomogeneous polynomials of a common bidegree. Evaluating the first coordinate block at $x$ and the second at $y$ gives either the zero tuple or a projective representative of $x+y$. The degree in each block is recorded separately. The tuple may have a base locus, and coverage by a family of laws is an additional assertion, not part of this definition.
--
--   **Formalization Note.** The data use the actual projective points, coordinate ring, and addition of the existing embedded-group definitions. They make no reembedding, covering, or degree-bound assertion.
-- source:
--   H. Lange, Families of translations of commutative algebraic groups, Journal of Algebra 109(1) (1987), pp. 260–265, DOI 10.1016/0021-8693(87)90174-8. Algebraic formulation: L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), Corollary 3.3.4, p. 66, and Theorem 3.4.6(2), p. 72; base-field convention on p. 13. https://doi.org/10.3929/ethz-a-004445245 . The formal statement restricts to commutative groups, puts the translated point in the first block, and includes the global compatibility of each rational addition law.

import Definitions.Def_PhilipponMultiplicity_Geometry

set_option autoImplicit false
noncomputable section
namespace PhilipponMultiplicity.EmbeddedCommutativeGroup
universe u
variable {K : Type u} [Field K]

/-- The first projective block is the point to be translated; the second is
the translation parameter. -/
def additionPair (E : EmbeddedCommutativeGroup K) (x y : E.Point) :
    (projectiveSquare K E.ambientDimension).Point :=
  fun i => if i.val = 0 then x.val else y.val

/-- A bihomogeneous addition law. It is allowed to vanish as a whole tuple;
where it is nonzero it must represent the actual group sum. -/
structure AdditionLaw (E : EmbeddedCommutativeGroup K) where
  degree : (projectiveSquare K E.ambientDimension).FactorIndex → ℕ
  coordinates : Fin (E.ambientDimension + 1) →
    (projectiveSquare K E.ambientDimension).CoordinateRing
  homogeneous : ∀ j, (projectiveSquare K E.ambientDimension).IsHomogeneous
    (coordinates j) degree
  represents : ∀ (x y : E.Point)
    (h : (fun j => (projectiveSquare K E.ambientDimension).eval
      (coordinates j) (E.additionPair x y)) ≠ 0),
    Projectivization.mk K (fun j => (projectiveSquare K E.ambientDimension).eval
      (coordinates j) (E.additionPair x y)) h = (x+y).val

end PhilipponMultiplicity.EmbeddedCommutativeGroup


