-- Prove2me | Definitions.Def_APSCounting893_Main_ModularJacobianData
-- name    : APSCounting893_Main_ModularJacobianData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T16:45:43.042589+00:00
-- url     : https://prove2.me/theorems/34f1cea9-7d46-4eee-a6df-334b5761c411
-- title:
--   Integer circuit fractions and bounded modular Jacobian certificates
-- statement:
--   This module gives integer fraction semantics and bounded modular certificates for the Jacobian step in rational image-dimension computation.
--
--   For each circuit gate, store integer polynomials $N,D$ representing the rational function $N/D$. Addition, subtraction, multiplication and division use cross multiplication; no cancellation or pointwise inversion is performed. Partial differentiation replaces this pair by
--
--   $$
--   (N'D-ND',D^2).
--   $$
--
--   For a selected square Jacobian matrix of such pairs, clear the denominators separately in each row and let $Q$ be the resulting integer polynomial matrix. Its determinant is the cleared Jacobian minor. A sparse assignment is a finite list of variable indices and integer values, with unlisted variables assigned zero.
--
--   Write $L$ for the circuit's binary encoding length. The predicate $\operatorname{Cert}(C,k)$ asserts that there are $k$ distinct output indices, $k$ distinct variable indices, a prime $p$, and a sparse assignment $a$ for which
--
--   $$
--   \det Q(a)\ne0\pmod p.
--   $$
--
--   Each selected variable index has at most $L$ bits, the prime has at most $128(L+1)+8$ bits, and the encoded sparse assignment has length at most $32(L+1)^2$. The following theorems connect this predicate to image dimension and finite-machine computation. The definition itself makes neither assertion.
--
--   **Formalization Note** The circuit and coefficient-field semantics are the mission's existing definitions. The explicit certificate bounds are auxiliary bounds for this Jacobian implementation, rather than the paper's separate resultant sampling constants.
-- source:
--   Agarwal, Hari, Pandey and Shukla, Approximate Polynomial Satisfiability and Integral Closure Membership in the Counting Hierarchy, STOC 2027 submission #893, Section 6, Lemma 6.1 and its Jacobian-rank proof, p.23. Auxiliary integer-fraction and modular-certificate implementation of that characteristic-zero step. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf#page=23 ; Schwartz–Zippel: Mathlib 0df444a, Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean, schwartz_zippel_totalDegree; small-modulus bound: Mathlib/NumberTheory/Chebyshev.lean, two_pow_le_mul_lcmUpto.

import Definitions.Def_APSCounting893_Main_SampledResultant
set_option autoImplicit false
namespace APSCounting893.Main

abbrev IntegerPolynomialPair (n : ℕ) := MvPolynomial (Fin n) ℤ × MvPolynomial (Fin n) ℤ

noncomputable def integerPolynomialEmbedding (n : ℕ) : MvPolynomial (Fin n) ℤ →+* CircuitFunctionField .rational n :=
  (algebraMap (MvPolynomial (Fin n) CoefficientPresentation.rational.Field) (CircuitFunctionField .rational n)).comp
    (MvPolynomial.map (Int.castRingHom CoefficientPresentation.rational.Field))

noncomputable def IntegerPolynomialPair.value {n : ℕ} (p : IntegerPolynomialPair n) :
    CircuitFunctionField .rational n := integerPolynomialEmbedding n p.1/integerPolynomialEmbedding n p.2

noncomputable def IntegerPolynomialPair.add {n : ℕ} (p q : IntegerPolynomialPair n) : IntegerPolynomialPair n :=
  (p.1*q.2+q.1*p.2,p.2*q.2)
noncomputable def IntegerPolynomialPair.sub {n : ℕ} (p q : IntegerPolynomialPair n) : IntegerPolynomialPair n :=
  (p.1*q.2-q.1*p.2,p.2*q.2)
noncomputable def IntegerPolynomialPair.mul {n : ℕ} (p q : IntegerPolynomialPair n) : IntegerPolynomialPair n :=
  (p.1*q.1,p.2*q.2)
noncomputable def IntegerPolynomialPair.div {n : ℕ} (p q : IntegerPolynomialPair n) : IntegerPolynomialPair n :=
  (p.1*q.2,p.2*q.1)

noncomputable def integerGateValue {n : ℕ} (prior : List (IntegerPolynomialPair n)) : ArithmeticGate n → Option (IntegerPolynomialPair n)
  | .variable i => some (MvPolynomial.X i,1)
  | .constant cs => let q:=cs.headD 0;some (MvPolynomial.C q.num,MvPolynomial.C (q.den : ℤ))
  | .add a b => do return (←prior[a]?).add (←prior[b]?)
  | .sub a b => do return (←prior[a]?).sub (←prior[b]?)
  | .mul a b => do return (←prior[a]?).mul (←prior[b]?)
  | .div a b => do return (←prior[a]?).div (←prior[b]?)

noncomputable def integerCircuitValues {n : ℕ} (C : ArithmeticCircuit n) : Option (List (IntegerPolynomialPair n)) :=
  C.gates.foldl (fun acc g => do
    let prior ← acc
    let value ← integerGateValue prior g
    return prior++[value]) (some [])


noncomputable def integerCircuitOutput {n : ℕ} (C : ArithmeticCircuit n) (j : Fin C.outputs.length) :
    IntegerPolynomialPair n :=
  (((integerCircuitValues C).getD [])[C.outputs[j]]?).getD (0,1)


noncomputable def IntegerPolynomialPair.derivative {n : ℕ} (j : Fin n) (p : IntegerPolynomialPair n) :
    IntegerPolynomialPair n :=
  (MvPolynomial.pderiv j p.1*p.2-p.1*MvPolynomial.pderiv j p.2,p.2^2)


noncomputable def clearedIntegerMatrix {n r : ℕ} (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n)) :
    Matrix (Fin r) (Fin r) (MvPolynomial (Fin n) ℤ) := fun i j =>
  (A i j).1*∏ k ∈ Finset.univ.erase j,(A i k).2

noncomputable def integerMatrixDenominator {n r : ℕ} (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n)) :
    MvPolynomial (Fin n) ℤ := ∏ i,∏ j,(A i j).2

noncomputable def integerMatrixDeterminantPair {n r : ℕ} (A : Matrix (Fin r) (Fin r) (IntegerPolynomialPair n)) :
    IntegerPolynomialPair n := ((clearedIntegerMatrix A).det,integerMatrixDenominator A)


noncomputable def circuitJacobianIntegerPairs {n k : ℕ} (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) : Matrix (Fin k) (Fin k) (IntegerPolynomialPair n) :=
  fun i j => (integerCircuitOutput C (o i)).derivative (v j)

noncomputable def circuitJacobianIntegerMinor {n k : ℕ} (C : ArithmeticCircuit n)
    (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n) : MvPolynomial (Fin n) ℤ :=
  (clearedIntegerMatrix (circuitJacobianIntegerPairs C o v)).det


def sparseAssignmentPoint {n : ℕ} (a : List (Fin n × ℤ)) (i : Fin n) : ℤ :=
  (a.lookup i).getD 0


def encodeSparseAssignment {n : ℕ} (a : List (Fin n × ℤ)) : Word :=
  encodeList (fun p => encodeNat p.1.val++encodeInt p.2) a


noncomputable def ModularJacobianCertificate {n : ℕ} (C : ArithmeticCircuit n) (k : ℕ) : Prop :=
  ∃ (o : Fin k → Fin C.outputs.length) (v : Fin k → Fin n),
    Function.Injective o ∧ Function.Injective v ∧
    (∀ j,(v j).val.bits.length≤C.encode.length) ∧
    ∃ p : ℕ,p.Prime ∧ p.bits.length≤128*(C.encode.length+1)+8 ∧
      ∃ a : List (Fin n × ℤ),(encodeSparseAssignment a).length≤polyBound 32 2 C.encode.length ∧
        (MvPolynomial.eval (sparseAssignmentPoint a) (circuitJacobianIntegerMinor C o v) : ZMod p)≠0

end APSCounting893.Main


