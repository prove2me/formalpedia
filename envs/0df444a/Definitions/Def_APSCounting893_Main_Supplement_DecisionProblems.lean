-- Prove2me | Definitions.Def_APSCounting893_Main_Supplement_DecisionProblems
-- name    : APSCounting893_Main_Supplement_DecisionProblems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:07:35.245397+00:00
-- url     : https://prove2.me/theorems/666b72dc-4c2b-4a60-8657-975793688ece
-- title:
--   Encoded integrality problems and deterministic many-one reductions
-- statement:
--   A system input consists of a published coefficient presentation, a variable count, and either a published finite arithmetic DAG or a sparse polynomial list. Validity retains binary constants, binary sparse exponents, nonzero rational-function divisors and polynomial output promises. The field presentation is included in the bit encoding. For integrality, the first output is $f$ and all remaining outputs generate the subalgebra; at least one output is required, but the generator list may be empty.
--
--   A deterministic polynomial-time many-one reduction has a single total bit-string function $r$, computed by a published charged machine with empty oracle, such that
--
--   $$I\text{ valid}\ \Longrightarrow\ r(\operatorname{enc} I)=\operatorname{enc} J,\quad J\text{ valid},\quad(I\text{ yes}\ \Longleftrightarrow\ J\text{ yes}).$$
--
--   The machine and time bound are fixed before every input and coefficient presentation. The target uses the same presentation. A fresh-variable construction is specified on DAGs, with sparse lists first converted by binary powering, giving output $z$ and generators $zf_i$. Empty sparse terms never cause a unary expansion of the variable count. A separate algebraic correctness predicate for powered systems quantifies over every algebraically closed field and all sufficiently large exponents, without presuming bit encodings of arbitrary abstract fields. Complexity statements cover the finitely presented rational, number and finite fields, including binary characteristic and inseparability.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), Problems 1.1–1.2, p. 2; Theorems 1.8/1.11, p. 4; §3.4, p. 15; Remarks 6.7/7.10, pp. 27/32; Lemma 7.11, pp. 32–33

import Definitions.Def_APSCounting893_Main_CountingHierarchy
import Definitions.Def_APSCounting893_Main_CircuitInputs
import Definitions.Def_APSCounting893_Main_Supplement_Certificates

set_option autoImplicit false

namespace APSCounting893.Main.Supplement

/-- Use the published DAG and sparse syntax, with all their semantic promises. -/
inductive InputRepresentation (n : ℕ) where
  | circuit (C : ArithmeticCircuit n)
  | sparse (S : SparseSystem n)

structure SystemInput where
  presentation : CoefficientPresentation
  nvars : ℕ
  representation : InputRepresentation nvars

def SystemInput.outputCount (I : SystemInput) : ℕ :=
  match I.representation with
  | .circuit C => C.outputs.length
  | .sparse S => S.length

noncomputable def SystemInput.polynomials (I : SystemInput) :
    PolynomialMap I.presentation.Field I.nvars I.outputCount :=
by
  cases I with
  | mk P n repr =>
    cases repr with
    | circuit C => exact circuitPolynomials P C
    | sparse S => exact sparsePolynomials P S

def SystemInput.Valid (I : SystemInput) : Prop :=
  match I.representation with
  | .circuit C => ValidCircuit I.presentation C
  | .sparse S => validSparse I.presentation S

noncomputable def SystemInput.encode (I : SystemInput) : Word :=
  match I.representation with
  | .circuit C => [false] ++ I.presentation.encode ++ C.encode
  | .sparse S => [true] ++ I.presentation.encode ++ encodeSparse S

noncomputable def SystemInput.APS (I : SystemInput) : Prop :=
  PolynomialAPS I.presentation I.polynomials

/-- Integral-closure inputs list f first, then all its generators. Empty generator lists
are allowed; an empty output list is not an integral-closure instance. -/
def SystemInput.ValidIntegral (I : SystemInput) : Prop := I.Valid ∧ 0 < I.outputCount

noncomputable def SystemInput.target (I : SystemInput) (h : 0 < I.outputCount) :
    Polynomials I.presentation.Field I.nvars := I.polynomials ⟨0, h⟩

noncomputable def SystemInput.generators (I : SystemInput) (h : 0 < I.outputCount) :
    PolynomialMap I.presentation.Field I.nvars (I.outputCount - 1) :=
  fun j => I.polynomials ⟨j.val + 1, by omega⟩

def SystemInput.Integral (I : SystemInput) : Prop :=
  ∃ h : 0 < I.outputCount, IntegralOverGenerators (I.generators h) (I.target h)

/-- Promise many-one reduction with one total, charged, deterministic polynomial-time
machine for every coefficient presentation, length, circuit and sparse input. The output
must be valid and use the same coefficient presentation. -/
def PolynomialManyOne (validSource yesSource validTarget yesTarget : SystemInput → Prop) : Prop :=
  ∃ r : Word → Word, FunctionInPWithOracle (fun _ => False) r ∧
    ∀ I : SystemInput, validSource I → ∃ J : SystemInput,
      validTarget J ∧ J.presentation = I.presentation ∧ r I.encode = J.encode ∧
        (yesSource I ↔ yesTarget J)

/-- Algebraic correctness of the powered forward construction over every algebraically
closed field. The exponent threshold is independent of integrality. No encoding of an
arbitrary abstract field is presumed by this predicate. -/
def PoweredAlgebraicReduction : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (n m : ℕ)
    (F : PolynomialMap K n m) (f : Polynomials K n),
    ∃ M₀ : ℕ, 0 < M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      (IntegralOverGenerators F f ↔ ¬ AlgebraicAPS (poweredSystem F f M))

/-- Rename old variable gates; wire indices and binary constants are unchanged. -/
def extendGate {n : ℕ} : ArithmeticGate n → ArithmeticGate (n + 1)
  | .variable i => .variable i.castSucc
  | .constant cs => .constant cs
  | .add i j => .add i j
  | .sub i j => .sub i j
  | .mul i j => .mul i j
  | .div i j => .div i j

/-- Exact DAG transformation: one z gate, then one multiplication per old output. -/
def freshCircuit {n : ℕ} (C : ArithmeticCircuit n) : ArithmeticCircuit (n + 1) :=
  { gates := C.gates.map extendGate ++ [.variable (Fin.last n)] ++
      C.outputs.map (fun i => .mul C.gates.length i)
    outputs := C.gates.length ::
      (List.range C.outputs.length).map (fun i => C.gates.length + 1 + i) }

/-- Append one gate and return its wire. No semantic computation is performed. -/
def emitGate {n : ℕ} (gates : List (ArithmeticGate n)) (g : ArithmeticGate n) :
    List (ArithmeticGate n) × ℕ := (gates ++ [g], gates.length)

/-- Binary powering of an existing wire. The accumulator starts at one. -/
def powerWire {n : ℕ} (gates : List (ArithmeticGate n)) (wire exponent : ℕ) :
    List (ArithmeticGate n) × ℕ :=
  let initial := emitGate gates (.constant [1])
  let result := exponent.bits.foldl
    (fun state bit =>
      let product := if bit then emitGate state.1 (.mul state.2.1 state.2.2)
        else (state.1, state.2.1)
      let square := emitGate product.1 (.mul state.2.2 state.2.2)
      (square.1, (product.2, square.2)))
    (initial.1, (initial.2, wire))
  (result.1, result.2.1)

/-- A term's n exponents are explicitly present in its sparse input. No n-fold loop
is run for an absent term, even if the binary variable count is enormous. -/
def termCircuit {n : ℕ} (gates : List (ArithmeticGate n)) (term : SparseTerm n) :
    List (ArithmeticGate n) × ℕ :=
  (List.finRange n).foldl
    (fun state i =>
      if term.exponent i = 0 then state else
        let v := emitGate state.1 (.variable i)
        let pw := powerWire v.1 v.2 (term.exponent i)
        emitGate pw.1 (.mul state.2 pw.2))
    (emitGate gates (.constant term.coefficient))

/-- Sparse-to-circuit conversion with shared accumulated gates and binary powers.
Zero outputs are constant gates, so no unary expansion of the variable count is needed. -/
def sparseCircuit {n : ℕ} (S : SparseSystem n) : ArithmeticCircuit n :=
  S.foldl (fun C terms =>
    let sum := terms.foldl (fun state term =>
      let value := termCircuit state.1 term
      emitGate value.1 (.add state.2 value.2))
      (emitGate C.gates (.constant [0]))
    { gates := sum.1, outputs := C.outputs ++ [sum.2] })
    { gates := [], outputs := [] }

def freshInput (I : SystemInput) : SystemInput :=
  { presentation := I.presentation
    nvars := I.nvars + 1
    representation := match I.representation with
      | .circuit C => .circuit (freshCircuit C)
      | .sparse S => .circuit (freshCircuit (sparseCircuit S)) }

/-- Runtime and correctness of the specified fresh-variable construction. -/
def FreshVariableReduction : Prop :=
  (∃ r : Word → Word, FunctionInPWithOracle (fun _ => False) r ∧
    ∀ I : SystemInput, r I.encode = (freshInput I).encode) ∧
  ∀ I : SystemInput, I.Valid → (freshInput I).ValidIntegral ∧
    (I.APS ↔ ¬ (freshInput I).Integral)

end APSCounting893.Main.Supplement


