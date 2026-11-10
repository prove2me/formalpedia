-- Prove2me | Definitions.Def_APSCounting893_Main_CircuitInputs
-- name    : APSCounting893_Main_CircuitInputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:00:31.560264+00:00
-- url     : https://prove2.me/theorems/531ea20d-c6aa-4910-97ee-34f86da63630
-- title:
--   Encoded coefficient fields, arithmetic DAGs and polynomial APS
-- statement:
--   A coefficient presentation is $\mathbb Q$, a number field given by an irreducible rational polynomial, or a finite field given by its binary characteristic and an irreducible polynomial over the prime field. The latter two fields are the corresponding quotient fields $\operatorname{AdjoinRoot}(f)$. Scalars are power-basis coordinate lists, with binary rational coordinates in characteristic zero and canonical prime-field residues in finite characteristic.
--
--   An arithmetic circuit is a topologically ordered finite DAG with shared gates and multiple outputs. Gates are variables, constants, addition, subtraction, multiplication or division. Gate semantics are computed in the multivariate fraction field. Every divisor must be nonzero there, and every output must belong to the polynomial ring. Sparse terms have binary exponents. All encodings include dimensions, wire indices, lists, field descriptions and constants.
--
--   For a polynomial tuple $F$ over the presented field $k$, define
--
--   $$\operatorname{APS}(F)\iff 0\in\overline{F(\overline{k}^{\,n})}^{\,\mathrm{Zar}}.$$
--
--   This definition includes zero variables and outputs and does not bound the domain, degree or coefficient height.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Problem 1.1; Remarks 1.4–1.6, 6.7, p. 3, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry

set_option autoImplicit false

namespace APSCounting893.Main

/-- Explicit coefficient fields; the proofs are semantic validity, not part of the serialized data. -/
inductive CoefficientPresentation where
  | rational
  | number (f : Polynomial ℚ) (irreducible : Irreducible f)
  | finite (p : ℕ) (prime : p.Prime) (f : Polynomial (ZMod p))
      (irreducible : Irreducible f)

noncomputable def CoefficientPresentation.Field : CoefficientPresentation → Type
  | .rational => ℚ
  | .number f _ => AdjoinRoot f
  | .finite _ _ f _ => AdjoinRoot f

noncomputable instance (P : CoefficientPresentation) : Field P.Field := by
  cases P with
  | rational => exact inferInstanceAs (Field ℚ)
  | number f hf =>
      letI : Fact (Irreducible f) := ⟨hf⟩
      exact inferInstanceAs (Field (AdjoinRoot f))
  | finite p hp f hf =>
      letI : Fact p.Prime := ⟨hp⟩
      letI : Fact (Irreducible f) := ⟨hf⟩
      exact inferInstanceAs (Field (AdjoinRoot f))

noncomputable def CoefficientPresentation.generator (P : CoefficientPresentation) : P.Field :=
  match P with
  | .rational => 0
  | .number f _ => AdjoinRoot.root f
  | .finite _ _ f _ => AdjoinRoot.root f

def CoefficientPresentation.degree : CoefficientPresentation → ℕ
  | .rational => 1
  | .number f _ => f.natDegree
  | .finite _ _ f _ => f.natDegree

/-- Scalar coordinates are binary rationals in characteristic zero, and canonical residues in
positive characteristic. There is no bound on the degree of the field presentation. -/
def CoefficientPresentation.ValidScalar (P : CoefficientPresentation) (v : List ℚ) : Prop :=
  v.length ≤ P.degree ∧ match P with
    | .finite p _ _ _ => ∀ q ∈ v, q.den = 1 ∧ 0 ≤ q.num ∧ q.num < (p : ℤ)
    | _ => True

noncomputable def CoefficientPresentation.scalar (P : CoefficientPresentation) (v : List ℚ) : P.Field :=
  ∑ i ∈ Finset.range v.length,
    ((v[i]!.num : P.Field) / (v[i]!.den : P.Field)) * P.generator ^ i

/-- Length-delimited binary encodings, including signed numerators and positive denominators. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeInt (z : ℤ) : List Bool := (z < 0) :: encodeNat z.natAbs

def encodeRat (q : ℚ) : List Bool := encodeInt q.num ++ encodeNat q.den

def encodeList {α : Type} (f : α → List Bool) (v : List α) : List Bool :=
  encodeNat v.length ++ v.flatMap f

noncomputable def CoefficientPresentation.encode : CoefficientPresentation → List Bool
  | .rational => [false, false]
  | .number f _ => [false, true] ++ encodeList encodeRat
      ((List.range (f.natDegree + 1)).map f.coeff)
  | .finite p _ f _ => [true] ++ encodeNat p ++ encodeList encodeNat
      ((List.range (f.natDegree + 1)).map (fun i => (f.coeff i).val))

/-- A finite DAG in topological order. Wire indices point into the previously evaluated list. -/
inductive ArithmeticGate (n : ℕ) where
  | variable (i : Fin n)
  | constant (coordinates : List ℚ)
  | add (left right : ℕ)
  | sub (left right : ℕ)
  | mul (left right : ℕ)
  | div (left right : ℕ)

structure ArithmeticCircuit (n : ℕ) where
  gates : List (ArithmeticGate n)
  outputs : List ℕ

abbrev CircuitFunctionField (P : CoefficientPresentation) (n : ℕ) :=
  FractionRing (MvPolynomial (Fin n) P.Field)

open Classical in
noncomputable def gateValue (P : CoefficientPresentation) {n : ℕ}
    (prior : List (CircuitFunctionField P n)) : ArithmeticGate n → Option (CircuitFunctionField P n)
  | .variable i => some (algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n) (MvPolynomial.X i))
  | .constant cs => some (algebraMap (MvPolynomial (Fin n) P.Field) (CircuitFunctionField P n) (MvPolynomial.C (P.scalar cs)))
  | .add a b => do return (← prior[a]?) + (← prior[b]?)
  | .sub a b => do return (← prior[a]?) - (← prior[b]?)
  | .mul a b => do return (← prior[a]?) * (← prior[b]?)
  | .div a b => do
      let numerator ← prior[a]?
      let denominator ← prior[b]?
      if denominator = 0 then none else some (numerator / denominator)

noncomputable def circuitValues (P : CoefficientPresentation) {n : ℕ}
    (C : ArithmeticCircuit n) : Option (List (CircuitFunctionField P n)) :=
  C.gates.foldl (fun acc g => do
    let prior ← acc
    let value ← gateValue P prior g
    return prior ++ [value]) (some [])

/-- Divisors are checked in the fraction field, before any evaluation at points. Outputs are
promised polynomials, with no bound on their expanded degree or coefficient height. -/
def ValidCircuit (P : CoefficientPresentation) {n : ℕ} (C : ArithmeticCircuit n) : Prop :=
  (∀ g ∈ C.gates, match g with | .constant cs => P.ValidScalar cs | _ => True) ∧
  ∃ values, circuitValues P C = some values ∧
    ∀ o ∈ C.outputs, ∃ (v : CircuitFunctionField P n) (f : MvPolynomial (Fin n) P.Field),
      values[o]? = some v ∧ algebraMap _ _ f = v

/-- Total only outside the semantic promise; on valid circuits, the polynomial is uniquely
specified by injectivity of the polynomial ring into its fraction field. -/
noncomputable def circuitPolynomials (P : CoefficientPresentation) {n : ℕ}
    (C : ArithmeticCircuit n) (j : Fin C.outputs.length) : MvPolynomial (Fin n) P.Field := by
  classical
  let v := ((circuitValues P C).getD [])[C.outputs[j]]?.getD 0
  exact if h : ∃ f : MvPolynomial (Fin n) P.Field, algebraMap _ _ f = v
    then Classical.choose h else 0

def ArithmeticGate.encode {n : ℕ} : ArithmeticGate n → List Bool
  | .variable i => encodeNat 0 ++ encodeNat i.val
  | .constant cs => encodeNat 1 ++ encodeList encodeRat cs
  | .add a b => encodeNat 2 ++ encodeNat a ++ encodeNat b
  | .sub a b => encodeNat 3 ++ encodeNat a ++ encodeNat b
  | .mul a b => encodeNat 4 ++ encodeNat a ++ encodeNat b
  | .div a b => encodeNat 5 ++ encodeNat a ++ encodeNat b

def ArithmeticCircuit.encode {n : ℕ} (C : ArithmeticCircuit n) : List Bool :=
  encodeNat n ++ encodeList ArithmeticGate.encode C.gates ++ encodeList encodeNat C.outputs

/-- Sparse terms carry binary exponents; repeated squaring is a theorem, not a degree promise. -/
structure SparseTerm (n : ℕ) where
  coefficient : List ℚ
  exponent : Fin n → ℕ

abbrev SparseSystem (n : ℕ) := List (List (SparseTerm n))

noncomputable def sparsePolynomials (P : CoefficientPresentation) {n : ℕ}
    (S : SparseSystem n) (j : Fin S.length) : MvPolynomial (Fin n) P.Field :=
  (S[j]).foldl (fun f term => f + MvPolynomial.C (P.scalar term.coefficient) *
    ∏ i : Fin n, MvPolynomial.X i ^ term.exponent i) 0

def validSparse (P : CoefficientPresentation) {n : ℕ} (S : SparseSystem n) : Prop :=
  ∀ output ∈ S, ∀ term ∈ output, P.ValidScalar term.coefficient

def encodeSparse {n : ℕ} (S : SparseSystem n) : List Bool :=
  encodeNat n ++ encodeList (encodeList (fun term =>
    encodeList encodeRat term.coefficient ++ encodeList encodeNat (List.ofFn term.exponent))) S

/-- Image closure is taken over the entire algebraic closure of the coefficient field. -/
noncomputable def PolynomialAPS (P : CoefficientPresentation) {n m : ℕ}
    (F : Fin m → MvPolynomial (Fin n) P.Field) : Prop :=
  (0 : Fin m → AlgebraicClosure P.Field) ∈ RSCapacity.zClosure
    (Set.range (fun x : Fin n → AlgebraicClosure P.Field =>
      fun i => MvPolynomial.eval₂ (algebraMap P.Field (AlgebraicClosure P.Field)) x (F i)))

end APSCounting893.Main


