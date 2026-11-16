-- Prove2me | Definitions.Def_ChowFormsCH_Supplement_FFCircuit
-- name    : ChowFormsCH_Supplement_FFCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:19:26.889212+00:00
-- url     : https://prove2.me/theorems/4c9fa2f3-457e-4fee-906e-8b111913f5f9
-- title:
--   Arithmetic circuits over rational function fields $F(t_1,\dots,t_k)$ with densely encoded constants
-- statement:
--   Let $F$ be $\mathbb{Q}$, a number field $\mathbb{Q}[\alpha]$, or a finite field $\mathbb{F}_{p^a}$, given by a presentation, and let $k \ge 0$. This definition introduces arithmetic circuits over the rational function field $F(t_1, \dots, t_k)$ as in §5.2:
--
--   1. a **constant** is a pair $(q, r)$ of polynomials in $t_1, \dots, t_k$ over $F$ with $r \ne 0$, each in the dense representation (a degree bound $D$ and one coefficient for every monomial of degree at most $D$), denoting $q/r \in F(t)$;
--   2. a **circuit** is a list of gates in topological order: variables $x_i$, constants, and $+, -, \times, \div$ gates, together with its output gates;
--   3. a circuit is **valid** if all constants are well formed, no division by zero occurs in $F(t)(x_1, \dots, x_n)$, and every output is a polynomial $f_j \in F(t)[x_1, \dots, x_n]$;
--   4. the **encoding** $|C|$ of a circuit is a binary string that contains the encodings of all its constants.
--
--   These are the inputs of the APS problem over $F(t_1, \dots, t_k)$ in Theorem 5.6.
--
--   **Formalization Note** The base field is the published `APSCounting893.Main.CoefficientPresentation`, which covers $\mathbb{Q}$, number fields and finite fields but no rational function fields. The field $F(t_1, \dots, t_k)$ is the fraction field of $F[t_1, \dots, t_k]$, and the gates mirror the published `ArithmeticGate`.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), Theorem 5.6, p.49 (PDF p.51); §5.2, p.44 (PDF p.46); Definition 2.6, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_ChowFormsCH_expList

set_option autoImplicit false

namespace ChowFormsCH.Supplement

open APSCounting893.Main

/-- A presentation of a rational function field `F(t₁, …, t_k)` over a presented base field `F`
(`ℚ`, a number field `ℚ[α]`, or a finite field `F_{p^a}`) (Andrews–Garg–Oliveira–Schost, *Some
algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version,
sha256 75e796c6…, Theorem 5.6, p.49: "F_{p^a}(t1, . . . , tk) … Q[α](t1, . . . , tk)"; §5.2, p.44).

**Formalization Note** The base field is the published `APSCounting893.Main.CoefficientPresentation`
(`ℚ`, `ℚ[U]/(μ)` for an irreducible `μ`, or `F_p[U]/(μ)` for a prime `p` and an irreducible `μ`);
`k ≥ 0` is the number of transcendental parameters. -/
structure FunFieldPresentation where
  base : CoefficientPresentation
  k : ℕ

/-- The field `F(t₁, …, t_k)`: the fraction field of `F[t₁, …, t_k]`. -/
abbrev FunFieldPresentation.Field (P : FunFieldPresentation) : Type :=
  FractionRing (MvPolynomial (Fin P.k) P.base.Field)

/-- A polynomial in `t₁, …, t_k` in the dense representation: a degree bound `D` and one
base-field scalar (given by its coordinate list) for every monomial of degree at most `D`, in the
order of the base mission's `expList k D` (§5.2, p.44: "the constants on the wires are encoded in
the dense representation"). -/
structure DenseParamPoly where
  degBound : ℕ
  coeffs : List (List ℚ)

/-- A dense parameter polynomial is well formed: it has exactly one coefficient per monomial of
degree at most `D`, and every coefficient is a valid scalar of the base field. -/
def DenseParamPoly.Valid (P : FunFieldPresentation) (q : DenseParamPoly) : Prop :=
  q.coeffs.length = (ChowFormsCH.expList P.k q.degBound).length ∧
    ∀ c ∈ q.coeffs, P.base.ValidScalar c

/-- The polynomial `∑_j c_j t^{α_j}` denoted by a dense parameter polynomial. -/
noncomputable def DenseParamPoly.toPoly (P : FunFieldPresentation) (q : DenseParamPoly) :
    MvPolynomial (Fin P.k) P.base.Field :=
  (((ChowFormsCH.expList P.k q.degBound).zip q.coeffs).map (fun ac =>
    MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm ac.1) (P.base.scalar ac.2))).sum

/-- Binary encoding of a dense parameter polynomial: the degree bound, then the coefficient list. -/
def DenseParamPoly.encode (q : DenseParamPoly) : List Bool :=
  encodeNat q.degBound ++ encodeList (encodeList encodeRat) q.coeffs

/-- A constant of `F(t₁, …, t_k)`: a numerator and a denominator, both dense parameter
polynomials (§5.2, p.44). -/
structure RatFunConst where
  num : DenseParamPoly
  den : DenseParamPoly

/-- A constant is well formed: both parts are well formed and the denominator is nonzero. -/
def RatFunConst.Valid (P : FunFieldPresentation) (c : RatFunConst) : Prop :=
  c.num.Valid P ∧ c.den.Valid P ∧ c.den.toPoly P ≠ 0

/-- The element `num / den` of `F(t₁, …, t_k)`. -/
noncomputable def RatFunConst.value (P : FunFieldPresentation) (c : RatFunConst) : P.Field :=
  algebraMap (MvPolynomial (Fin P.k) P.base.Field) P.Field (c.num.toPoly P) /
    algebraMap (MvPolynomial (Fin P.k) P.base.Field) P.Field (c.den.toPoly P)

def RatFunConst.encode (c : RatFunConst) : List Bool := c.num.encode ++ c.den.encode

/-- A gate of an arithmetic circuit over `F(t₁, …, t_k)` in the variables `x₁, …, x_n`
(Definition 2.6, p.11, with constants from the field, §5.2, p.44). Wire indices point into the
list of previously evaluated gates. -/
inductive FFGate (n : ℕ) where
  | variable (i : Fin n)
  | constant (c : RatFunConst)
  | add (left right : ℕ)
  | sub (left right : ℕ)
  | mul (left right : ℕ)
  | div (left right : ℕ)

/-- An arithmetic circuit over `F(t₁, …, t_k)`: a DAG in topological order and its output gates. -/
structure FFCircuit (n : ℕ) where
  gates : List (FFGate n)
  outputs : List ℕ

/-- The field `F(t)(x₁, …, x_n)` in which the gates of a circuit over `F(t)` take their values. -/
abbrev FFCircuitField (P : FunFieldPresentation) (n : ℕ) : Type :=
  FractionRing (MvPolynomial (Fin n) P.Field)

open Classical in
/-- The value of one gate, given the values of the earlier gates; `none` on a dangling wire or a
division by zero (Definition 2.6 requires that "no division by zero takes place"). -/
noncomputable def ffGateValue (P : FunFieldPresentation) {n : ℕ}
    (prior : List (FFCircuitField P n)) : FFGate n → Option (FFCircuitField P n)
  | .variable i => some (algebraMap (MvPolynomial (Fin n) P.Field) (FFCircuitField P n)
      (MvPolynomial.X i))
  | .constant c => some (algebraMap (MvPolynomial (Fin n) P.Field) (FFCircuitField P n)
      (MvPolynomial.C (c.value P)))
  | .add a b => do return (← prior[a]?) + (← prior[b]?)
  | .sub a b => do return (← prior[a]?) - (← prior[b]?)
  | .mul a b => do return (← prior[a]?) * (← prior[b]?)
  | .div a b => do
      let numerator ← prior[a]?
      let denominator ← prior[b]?
      if denominator = 0 then none else some (numerator / denominator)

/-- The values of all gates, in order, or `none` if some gate is undefined. -/
noncomputable def ffCircuitValues (P : FunFieldPresentation) {n : ℕ} (C : FFCircuit n) :
    Option (List (FFCircuitField P n)) :=
  C.gates.foldl (fun acc g => do
    let prior ← acc
    let value ← ffGateValue P prior g
    return prior ++ [value]) (some [])

/-- A valid circuit over `F(t)`: every constant is well formed, no wire dangles, no division by
zero takes place in `F(t)(x)`, and every output gate computes a polynomial of `F(t)[x]` (the
circuit "computes polynomials f₁, …, f_m ∈ F[x₁, …, xₙ]", Definition 1.7, p.5). -/
def ValidFFCircuit (P : FunFieldPresentation) {n : ℕ} (C : FFCircuit n) : Prop :=
  (∀ g ∈ C.gates, ∀ c : RatFunConst, g = FFGate.constant c → c.Valid P) ∧
  ∃ values, ffCircuitValues P C = some values ∧
    ∀ o ∈ C.outputs, ∃ (v : FFCircuitField P n) (f : MvPolynomial (Fin n) P.Field),
      values[o]? = some v ∧ algebraMap _ _ f = v

/-- The polynomials computed by the output gates of a circuit over `F(t)`, in order (meaningful
for valid circuits, where they are unique; `0` otherwise). -/
noncomputable def ffCircuitPolynomials (P : FunFieldPresentation) {n : ℕ} (C : FFCircuit n)
    (j : Fin C.outputs.length) : MvPolynomial (Fin n) P.Field := by
  classical
  let v := ((ffCircuitValues P C).getD [])[C.outputs[j]]?.getD 0
  exact if h : ∃ f : MvPolynomial (Fin n) P.Field, algebraMap _ _ f = v
    then Classical.choose h else 0

def FFGate.encode {n : ℕ} : FFGate n → List Bool
  | .variable i => encodeNat 0 ++ encodeNat i.val
  | .constant c => encodeNat 1 ++ c.encode
  | .add a b => encodeNat 2 ++ encodeNat a ++ encodeNat b
  | .sub a b => encodeNat 3 ++ encodeNat a ++ encodeNat b
  | .mul a b => encodeNat 4 ++ encodeNat a ++ encodeNat b
  | .div a b => encodeNat 5 ++ encodeNat a ++ encodeNat b

/-- The binary encoding `|C|` of a circuit over `F(t)`, including the bits of its constants
(§5.2, p.44: "the encoding of the circuit will include the bit complexity of the constants"). -/
def FFCircuit.encode {n : ℕ} (C : FFCircuit n) : List Bool :=
  encodeNat n ++ encodeList FFGate.encode C.gates ++ encodeList encodeNat C.outputs

end ChowFormsCH.Supplement


