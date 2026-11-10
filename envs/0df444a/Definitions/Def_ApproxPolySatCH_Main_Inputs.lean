-- Prove2me | Definitions.Def_ApproxPolySatCH_Main_Inputs
-- name    : ApproxPolySatCH_Main_Inputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:08:53.591634+00:00
-- url     : https://prove2.me/theorems/7cf4e6c5-6988-4b8a-82db-d7d3f1983e68
-- title:
--   Coefficient presentations, binary polynomial inputs and APS semantics
-- statement:
--   A coefficient field is either $\mathbb Q$ or $\mathbb F_p[U]/(\mu)$, where $p$ is prime and $\mu$ is specified, monic, irreducible and of positive degree. Rational scalars use binary integer numerator/denominator pairs with nonzero denominator. Finite-field scalars use residue coordinates in the power basis. Counts, exponents and wire addresses have length-delimited binary encodings.
--
--   For $f=(f_1,\ldots,f_m)$ in $n$ variables over $k$, put $K=\overline k$. The acceptance condition is
--   $$\operatorname{APS}(f)\iff 0\in\overline{\{(f_1(x),\ldots,f_m(x)):x\in K^n\}}^{\mathrm{Zar}}.$$
--   Sparse inputs are lists of terms, with duplicates summed. Dense inputs contain every coefficient in a total-degree simplex, including zeros. Division-free circuits are finite shared DAGs in topological order, with addition and multiplication gates; negative constants implement subtraction. Invalid wire indices and scalar encodings are excluded by explicit validity conditions. Zero and empty systems remain admissible. A tagged union combines the three input representations for each fixed coefficient field.
--
--   These definitions connect the actual bit strings to image-closure membership; polynomial expansion is mathematical semantics and is never declared a unit-cost computation.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), §§2–3, pp.5–7,14–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf

import Mathlib
import Definitions.Def_RSCapacity_AffineGeometry
import Definitions.Def_ApproxPolySatCH_Main_Complexity

set_option autoImplicit false

namespace ApproxPolySatCH.Main

inductive CoefficientField where
  | rational
  | finite (p : ℕ) (hp : p.Prime) (mu : Polynomial (ZMod p))
      (monic : mu.Monic) (positiveDegree : 0 < mu.natDegree) (irreducible : Irreducible mu)

noncomputable def CoefficientField.Carrier : CoefficientField → Type
  | .rational => ℚ
  | .finite _ _ mu _ _ _ => AdjoinRoot mu

noncomputable instance (k : CoefficientField) : Field k.Carrier := by
  cases k with
  | rational => exact inferInstanceAs (Field ℚ)
  | finite p hp mu _ _ hirr =>
    letI : Fact p.Prime := ⟨hp⟩
    letI : Fact (Irreducible mu) := ⟨hirr⟩
    exact inferInstanceAs (Field (AdjoinRoot mu))

def CoefficientField.degree : CoefficientField → ℕ
  | .rational => 1
  | .finite _ _ mu _ _ _ => mu.natDegree

noncomputable def CoefficientField.generator : (k : CoefficientField) → k.Carrier
  | .rational => 0
  | .finite _ _ mu _ _ _ => AdjoinRoot.root mu

abbrev ScalarCode := List (ℤ × ℤ)

def ValidScalar (k : CoefficientField) (s : ScalarCode) : Prop :=
  s.length ≤ k.degree ∧ match k with
  | .rational => ∀ z ∈ s, z.2 ≠ 0
  | .finite p _ _ _ _ _ => ∀ z ∈ s, z.2 = 1 ∧ 0 ≤ z.1 ∧ z.1 < (p : ℤ)

noncomputable def scalar (k : CoefficientField) (s : ScalarCode) : k.Carrier :=
  ∑ i ∈ Finset.range s.length,
    ((s[i]!.1 : k.Carrier) / (s[i]!.2 : k.Carrier)) * k.generator ^ i

def encodeNat (n : ℕ) : Word := List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeInt (z : ℤ) : Word := (z < 0) :: encodeNat z.natAbs

def encodeList {A : Type} (encode : A → Word) (xs : List A) : Word :=
  encodeNat xs.length ++ xs.flatMap encode

def encodeScalar (s : ScalarCode) : Word :=
  encodeList (fun z => encodeInt z.1 ++ encodeInt z.2) s

noncomputable def CoefficientField.encode : CoefficientField → Word
  | .rational => [false]
  | .finite p _ mu _ _ _ => [true] ++ encodeNat p ++
    encodeList encodeNat ((List.range (mu.natDegree + 1)).map (fun j => (mu.coeff j).val))

abbrev Poly (k : Type) [CommSemiring k] (n : ℕ) := MvPolynomial (Fin n) k

noncomputable def APS {k : Type} [Field k] {n m : ℕ} (f : Fin m → Poly k n) : Prop :=
  (0 : Fin m → AlgebraicClosure k) ∈ RSCapacity.zClosure
    (Set.range (fun x : Fin n → AlgebraicClosure k =>
      fun i => MvPolynomial.eval₂ (algebraMap k (AlgebraicClosure k)) x (f i)))

structure Term (n : ℕ) where
  coeff : ScalarCode
  exponents : Fin n → ℕ

abbrev SparseSystem (n : ℕ) := List (List (Term n))

def ValidSparse (k : CoefficientField) {n : ℕ} (S : SparseSystem n) : Prop :=
  ∀ f ∈ S, ∀ t ∈ f, ValidScalar k t.coeff

noncomputable def sparsePolynomials (k : CoefficientField) {n : ℕ} (S : SparseSystem n) :
    Fin S.length → Poly k.Carrier n :=
  fun i => (S[i]).foldl (fun f t => f + MvPolynomial.C (scalar k t.coeff) *
    ∏ j : Fin n, MvPolynomial.X j ^ t.exponents j) 0

def encodeSparse {n : ℕ} (S : SparseSystem n) : Word :=
  encodeNat n ++ encodeList (encodeList (fun t => encodeScalar t.coeff ++
    encodeList encodeNat (List.ofFn t.exponents))) S

/-- Degree-bounded simplex monomials, in lexicographic order; the dense array includes zeros. -/
def denseExponents : (n D : ℕ) → List (Fin n → ℕ)
  | 0, _ => [Fin.elim0]
  | n + 1, D => (List.range (D + 1)).flatMap (fun j =>
      (denseExponents n (D - j)).map (fun a => Fin.cons j a))

structure DensePolynomial (n : ℕ) where
  degree : ℕ
  coeffs : List ScalarCode
  complete : coeffs.length = (denseExponents n degree).length

abbrev DenseSystem (n : ℕ) := List (DensePolynomial n)

noncomputable def densePolynomial (k : CoefficientField) {n : ℕ} (p : DensePolynomial n) :
    Poly k.Carrier n :=
  ((denseExponents n p.degree).zip p.coeffs).foldl
    (fun f t => f + MvPolynomial.C (scalar k t.2) * ∏ j, MvPolynomial.X j ^ t.1 j) 0

def ValidDense (k : CoefficientField) {n : ℕ} (S : DenseSystem n) : Prop :=
  ∀ p ∈ S, ∀ c ∈ p.coeffs, ValidScalar k c

def encodeDense {n : ℕ} (S : DenseSystem n) : Word :=
  encodeNat n ++ encodeList (fun p => encodeNat p.degree ++ encodeList encodeScalar p.coeffs) S

inductive Gate (n : ℕ) where
  | variable (i : Fin n)
  | constant (c : ScalarCode)
  | add (i j : ℕ)
  | multiply (i j : ℕ)

structure Circuit (n : ℕ) where
  gates : List (Gate n)
  outputs : List ℕ

noncomputable def gateValue (k : CoefficientField) {n : ℕ} (prior : List (Poly k.Carrier n)) :
    Gate n → Option (Poly k.Carrier n)
  | .variable i => some (MvPolynomial.X i)
  | .constant c => some (MvPolynomial.C (scalar k c))
  | .add i j => do return (← prior[i]?) + (← prior[j]?)
  | .multiply i j => do return (← prior[i]?) * (← prior[j]?)

noncomputable def circuitValues (k : CoefficientField) {n : ℕ} (C : Circuit n) :
    Option (List (Poly k.Carrier n)) :=
  C.gates.foldl (fun acc g => do
    let prior ← acc
    let value ← gateValue k prior g
    return prior ++ [value]) (some [])

def ValidCircuit (k : CoefficientField) {n : ℕ} (C : Circuit n) : Prop :=
  (∀ g ∈ C.gates, match g with | .constant c => ValidScalar k c | _ => True) ∧
  ∃ values, circuitValues k C = some values ∧ ∀ o ∈ C.outputs, o < values.length

noncomputable def circuitPolynomials (k : CoefficientField) {n : ℕ} (C : Circuit n) :
    Fin C.outputs.length → Poly k.Carrier n :=
  fun i => ((circuitValues k C).getD [])[C.outputs[i]]?.getD 0

def encodeGate {n : ℕ} : Gate n → Word
  | .variable i => encodeNat 0 ++ encodeNat i.val
  | .constant c => encodeNat 1 ++ encodeScalar c
  | .add i j => encodeNat 2 ++ encodeNat i ++ encodeNat j
  | .multiply i j => encodeNat 3 ++ encodeNat i ++ encodeNat j

def encodeCircuit {n : ℕ} (C : Circuit n) : Word :=
  encodeNat n ++ encodeList encodeGate C.gates ++ encodeList encodeNat C.outputs

noncomputable def SparseLanguage (k : CoefficientField) : Language :=
  {x | ∃ (n : ℕ) (S : SparseSystem n), x = encodeSparse S ∧
    ValidSparse k S ∧ APS (sparsePolynomials k S)}

noncomputable def DenseLanguage (k : CoefficientField) : Language :=
  {x | ∃ (n : ℕ) (S : DenseSystem n), x = encodeDense S ∧ ValidDense k S ∧
    APS (fun i : Fin S.length => densePolynomial k S[i])}

noncomputable def CircuitLanguage (k : CoefficientField) : Language :=
  {x | ∃ (n : ℕ) (C : Circuit n), x = encodeCircuit C ∧
    ValidCircuit k C ∧ APS (circuitPolynomials k C)}

/-- The fixed coefficient field language includes all three input representations. -/
noncomputable def APSLanguage (k : CoefficientField) : Language := {x |
  (∃ w ∈ SparseLanguage k, x = [false, false] ++ w) ∨
  (∃ w ∈ DenseLanguage k, x = [false, true] ++ w) ∨
  (∃ w ∈ CircuitLanguage k, x = [true] ++ w)}
end ApproxPolySatCH.Main


