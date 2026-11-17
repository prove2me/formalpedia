-- Prove2me | Definitions.Def_CoRSuccGap_Supplement_TestSystem
-- name    : CoRSuccGap_Supplement_TestSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:36:59.471712+00:00
-- url     : https://prove2.me/theorems/3c5daf15-07de-42d1-bd88-888ef810eb1d
-- title:
--   Abstract test systems, typed circuit semantics and gate--fold cost
-- statement:
--   A **test system** with palette $\Lambda$ consists of typed reference values closed under every permitted typed operation, a prediction $U^{(\lambda)}$ for every reference value and $\lambda\in\Lambda$, input values on the folded structure equal to the predictions of their reference-structure values, and an observation $\rho_\lambda$ fixed by prediction whose required answers on the two structures differ.
--
--   A circuit is a finite topologically ordered DAG of input and permitted-operation gates. For an operation gate $g$ with reference-structure operand tuple $U_g$, let
--
--   $$
--   D_g=\{\lambda\in\Lambda:\operatorname{op}_g(U_g^{(\lambda)})\ne
--   \operatorname{op}_g(U_g)^{(\lambda)}\},\qquad
--   \operatorname{cost}(C)=\sum_{g\ \mathrm{distinct}}|D_g|.
--   $$
--
--   Input gates have $D_g=\varnothing$. Correctness records the answer at both observations of every test. These definitions isolate the fold-counting principle used by Theorem 4.1 for deterministic and input-independent randomized circuits.
--
--   **Formalization Note** Value types are represented by a tagged dependent sum. Circuit gate values are stored together with a `Valid` coherence condition forcing them to be obtained from their input and operation labels. `Notices` uses predicted reference operands, not operands recomputed on the folded input.
-- source:
--   Uezato--Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), Section 4.1, pp.23--24 (PDF 25--26), conditions (i)--(iii), (Obs), and definition of cost(C)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace CoRSuccGap
namespace Supplement

/-!
# Abstract test systems and the gate--fold cost

Uezato--Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the
Calculus of Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Section 4.1,
pp.23--24 (PDF 25--26).

The paper permits several value types.  `PackedValue` is their tagged disjoint union.  An
operation records its input and output types, and a test system records the reference values,
their predictions, the input values on the reference and folded structures, and the two required
answers at each observation.  A circuit is a topologically numbered DAG.  Its stored gate values
are required by `Valid` to be the values obtained from the input and operation labels; storing the
values avoids imposing decidable equality on arbitrary semantic value types.
-/

/-- A value tagged by its type in a typed test system. -/
abbrev PackedValue (Ty : Type*) (Val : Ty → Type*) := Σ t, Val t

/-- A gate operation in a typed test system. -/
structure TestOperation (Ty : Type*) (Val : Ty → Type*) where
  inputTypes : List Ty
  outputType : Ty
  apply : List (PackedValue Ty Val) → PackedValue Ty Val
  typed : ∀ xs, xs.map Sigma.fst = inputTypes → (apply xs).fst = outputType

/-- The three conditions defining a test system in Section 4.1, including a palette of exactly
`2^k` tests and observations fixed by prediction. -/
structure TestSystem (k : ℕ) where
  Palette : Type
  paletteFintype : Fintype Palette
  paletteCard : @Fintype.card Palette paletteFintype = 2 ^ k
  Ty : Type
  Val : Ty → Type
  Operation : Type
  operation : Operation → TestOperation Ty Val
  reference : ∀ t, Set (Val t)
  predict : Palette → ∀ t, Val t → Val t
  reference_closed : ∀ (o : Operation) (xs : List (PackedValue Ty Val)),
    (h : xs.map Sigma.fst = (operation o).inputTypes) →
    (∀ x ∈ xs, reference x.fst x.snd) →
    reference (operation o).outputType
      (cast (congrArg Val ((operation o).typed xs h)) ((operation o).apply xs).snd)
  Input : Type
  inputType : Input → Ty
  inputBase : (a : Input) → Val (inputType a)
  inputFold : Palette → (a : Input) → Val (inputType a)
  input_reference : ∀ a, reference (inputType a) (inputBase a)
  input_prediction : ∀ lam a, inputFold lam a = predict lam (inputType a) (inputBase a)
  observe : Palette → PackedValue Ty Val → Bool
  requiredBase : Palette → Bool
  requiredFold : Palette → Bool
  observation_fixed : ∀ lam t (v : Val t), reference t v →
    observe lam ⟨t, predict lam t v⟩ = observe lam ⟨t, v⟩
  required_differ : ∀ lam, requiredBase lam ≠ requiredFold lam

namespace TestSystem

variable {k : ℕ} (S : TestSystem k)

/-- Prediction on the tagged union of all value types. -/
def predictPacked (lam : S.Palette) : PackedValue S.Ty S.Val → PackedValue S.Ty S.Val
  | ⟨t, v⟩ => ⟨t, S.predict lam t v⟩

/-- A packed input value on the reference structure. -/
def inputBasePacked (a : S.Input) : PackedValue S.Ty S.Val :=
  ⟨S.inputType a, S.inputBase a⟩

/-- A packed input value on the folded structure for `λ`. -/
def inputFoldPacked (lam : S.Palette) (a : S.Input) : PackedValue S.Ty S.Val :=
  ⟨S.inputType a, S.inputFold lam a⟩

end TestSystem

/-- An input gate or a permitted operation gate with ordered references to earlier gates. -/
inductive TestGate {k : ℕ} (S : TestSystem k) (ι : Type*) where
  | input (a : S.Input)
  | op (o : S.Operation) (args : List ι)

/-- A typed test circuit represented as a straight-line program.  `baseValue` and `foldValue`
are semantic values; `Valid` below forces them to agree gate-by-gate with the labels. -/
structure TestCircuit {k : ℕ} (S : TestSystem k) where
  size : ℕ
  gate : (i : Fin size) → TestGate S (Fin i)
  output : Fin size
  baseValue : Fin size → PackedValue S.Ty S.Val
  foldValue : S.Palette → Fin size → PackedValue S.Ty S.Val

namespace TestCircuit

variable {k : ℕ} {S : TestSystem k}

/-- Regard an earlier-gate index as an index of the whole circuit. -/
def earlier {C : TestCircuit S} (i : Fin C.size) (j : Fin i) : Fin C.size :=
  ⟨j.val, lt_trans j.isLt i.isLt⟩

/-- The tuple of reference-structure operand values of gate `i`. -/
def baseArgs (C : TestCircuit S) (i : Fin C.size) (args : List (Fin i)) :
    List (PackedValue S.Ty S.Val) :=
  args.map (fun j => C.baseValue (earlier i j))

/-- The tuple of folded-structure operand values of gate `i`. -/
def foldArgs (C : TestCircuit S) (lam : S.Palette) (i : Fin C.size) (args : List (Fin i)) :
    List (PackedValue S.Ty S.Val) :=
  args.map (fun j => C.foldValue lam (earlier i j))

/-- Predictions, componentwise, of the reference-structure operands of gate `i`. -/
def predictedArgs (C : TestCircuit S) (lam : S.Palette) (i : Fin C.size)
    (args : List (Fin i)) : List (PackedValue S.Ty S.Val) :=
  (C.baseArgs i args).map (S.predictPacked lam)

/-- Gate values are obtained from the circuit's input and operation labels, and every reference-
structure gate value is a reference value.  This is the semantic well-formedness condition for a
circuit over the test system's permitted operations. -/
def Valid (C : TestCircuit S) : Prop :=
  (∀ i,
    match C.gate i with
    | .input a =>
        C.baseValue i = S.inputBasePacked a ∧
        ∀ lam, C.foldValue lam i = S.inputFoldPacked lam a
    | .op o args =>
        (C.baseArgs i args).map Sigma.fst = (S.operation o).inputTypes ∧
        (∀ lam, (C.foldArgs lam i args).map Sigma.fst = (S.operation o).inputTypes) ∧
        C.baseValue i = (S.operation o).apply (C.baseArgs i args) ∧
        ∀ lam, C.foldValue lam i = (S.operation o).apply (C.foldArgs lam i args)) ∧
  ∀ i, S.reference (C.baseValue i).fst (C.baseValue i).snd

/-- Whether a gate notices the fold `λ`.  Input gates notice no fold.  At an operation gate this
compares the operation on predicted reference operands with the prediction of its reference output,
not with operands recomputed on the folded structure. -/
def Notices (C : TestCircuit S) (i : Fin C.size) (lam : S.Palette) : Prop :=
  match C.gate i with
  | .input _ => False
  | .op o args =>
      (S.operation o).apply (C.predictedArgs lam i args) ≠
        S.predictPacked lam ((S.operation o).apply (C.baseArgs i args))

/-- `D_g`, the set of folds noticed by a distinct gate. -/
noncomputable def noticedFolds (C : TestCircuit S) (i : Fin C.size) : Finset S.Palette := by
  classical
  letI := S.paletteFintype
  exact Finset.univ.filter (C.Notices i)

/-- `cost(C) = Σ_g |D_g|`, summed over distinct gates. -/
noncomputable def cost (C : TestCircuit S) : ℕ :=
  ∑ i : Fin C.size, (C.noticedFolds i).card

/-- Correctness at the reference observation of test `λ`. -/
def CorrectBase (C : TestCircuit S) (lam : S.Palette) : Prop :=
  S.observe lam (C.baseValue C.output) = S.requiredBase lam

/-- Correctness at the folded observation of test `λ`. -/
def CorrectFold (C : TestCircuit S) (lam : S.Palette) : Prop :=
  S.observe lam (C.foldValue lam C.output) = S.requiredFold lam

/-- Correctness at both observations of every test. -/
def Correct (C : TestCircuit S) : Prop := ∀ lam, C.CorrectBase lam ∧ C.CorrectFold lam

end TestCircuit

end Supplement
end CoRSuccGap


