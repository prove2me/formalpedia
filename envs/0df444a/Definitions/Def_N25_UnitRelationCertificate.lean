-- Prove2me | Definitions.Def_N25_UnitRelationCertificate
-- name    : N25_UnitRelationCertificate
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:02:05.727198+00:00
-- url     : https://prove2.me/theorems/a96da01a-9a97-4761-8ff3-3a8561dc610f
-- title:
--   Finite modular certificates for the unit relation
-- statement:
--   The file defines four pairwise coprime reconstruction bases $B_i=2^{91}-(2i+1)$, finite blocks of exponents associated with level-$25$ residue pairs, their binomial-product polynomials, and the cleared numerator polynomial for the unit relation. It also defines a modular evaluator for that numerator modulo $B^N$. This is a computational certificate package for proving many initial coefficients vanish from bounded congruence data.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_Polynomial_BinomialResidue
set_option autoImplicit false
open Polynomial
namespace N25

/-- Four pairwise coprime bases used for bounded coefficient reconstruction. -/
def unitRelationCertificateBase25 (i : Fin 4) : ℕ := 2^91 - (2*i.val+1)

/-- The four binomial exponents in each level-25 residue-pair block. -/
def unitPairBlocks25 (t a b : ℕ) : List (List ℕ) :=
  (List.range t).map fun m => [25*m+a, 25*m+b, 25*(m+1)-a, 25*(m+1)-b]

/-- The finite polynomial of an unshifted residue pair. -/
noncomputable def unitPairPolynomial25 (t a b : ℕ) : ℤ[X] :=
  Polynomial.binomialBlocksPolynomial (unitPairBlocks25 t a b)

/-- The numerator after clearing the residue-pair denominator in the plane relation. -/
def unitRelationNumerator25 {A : Type*} [CommRing A] (q p r s : A) : A :=
  q^8*p^4*s^4*r - q^9*p^6*s^3 + q^5*p^3*s^2*r^4 -
    q^7*p^5*s^2*r^2 - 2*q^8*p^6*s^2*r -
    q^5*p^4*s*r^4 - q^6*p^5*s*r^3 - 2*q^7*p^6*s*r^2 + q^7*p^7*r^2

/-- The finite polynomial whose low coefficients certify the relation. -/
noncomputable def unitRelationNumeratorPolynomial25 (t : ℕ) : ℤ[X] :=
  unitRelationNumerator25 Polynomial.X
    (unitPairPolynomial25 t 1 7) (unitPairPolynomial25 t 2 11)
    (unitPairPolynomial25 t 3 4)

/-- The modular integer computation for the finite numerator. -/
def unitRelationNumeratorResidue25 (base count : ℕ) : ℤ :=
  let modulus := base ^ count
  let t := (count + 24) / 25
  let p := Polynomial.binomialBlocksResidue base count (unitPairBlocks25 t 1 7)
  let r := Polynomial.binomialBlocksResidue base count (unitPairBlocks25 t 2 11)
  let s := Polynomial.binomialBlocksResidue base count (unitPairBlocks25 t 3 4)
  let term := fun i j =>
    (((Polynomial.residuePower p (i+j) modulus * (Polynomial.residuePower s j modulus)) % modulus *
      (Polynomial.residuePower r (9-i-2*j) modulus)) * base ^ (i+2*j)) % modulus
  ((term 0 4 : ℤ) - term 3 3 + term 1 2 - term 3 2 -
    2 * term 4 2 - term 3 1 - term 4 1 - 2 * term 5 1 + term 7 0) % modulus

end N25


