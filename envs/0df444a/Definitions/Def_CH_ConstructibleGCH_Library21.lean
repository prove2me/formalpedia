-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library21
-- name    : CH_ConstructibleGCH_Library21
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:12:17.606781+00:00
-- url     : https://prove2.me/theorems/e120ea59-6140-4643-8f1b-4fa30b5afcf1
-- title:
--   Formula codes and uniform injection families
-- statement:
--   This library provides finite formula codes, hull closure data, uniformly represented injection families, and restriction and graph formulas. The stage-injection interfaces keep their representing graphs inside the constructible universe.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FormulaSyntaxCode.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FullSkolemHull.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/ParametricUniformOmegaInjectionFamily.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FormulaRestrictionLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FunctionGraphFormulaLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalStageInjectionFamily.lean#L1

import Definitions.Def_CH_ConstructibleAC_Library15
import Definitions.Def_CH_Constructible
import Mathlib.Data.List.Shortlex
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sigma.Lex
import Mathlib.Data.Sum.Order
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.ZFC.Ordinal
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.ZFC.Cardinal
import Mathlib.SetTheory.ZFC.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.SetTheory.Cardinal.Basic

import Definitions.Def_CH_ConstructibleGCH_Library20
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_FormulaSyntaxCode -/
section GCHSource_Work_CUGCH_FormulaSyntaxCode
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Goedel codes for the independent formula syntax

This file supplies a genuine enumeration of the intrinsically scoped syntax
`FOFormula n`.  It is separate from `FormulaGodel.lean`: that file represents
the relation defined by one fixed formula, whereas this file assigns a natural
number to the formula syntax itself.

The construction has three layers.

* `RawFormula` is an unscoped syntax tree whose variable names are natural
  numbers.  Its `Encodable` instance is a structural natural-number encoding.
* `formulaNatCode` erases the intrinsic scope information and encodes the raw
  tree.  `formulaNatDecode` restores a formula only when every variable is in
  scope.  The decoder is proved to be a left inverse.
* `PackedFormula = Sigma FOFormula` records the arity together with a formula,
  so formulas in different contexts also have distinct codes.

Finally, `formulaZFCode` and `packedFormulaZFCode` turn the natural codes into
von Neumann natural numbers in the internal `ZFSet` universe.  These codes are
members of the standard omega and are constructible.

This is the external syntax-enumeration layer needed before an object-language
uniform truth definition can be arithmetized.  It deliberately does not claim
that decoding or satisfaction is already represented by one `FOFormula`.
-/

section

universe u

namespace Constructible

namespace FOFormulaCode

/-! ## Unscoped syntax and scope checking -/

/--
An unscoped copy of the formula syntax.  Natural numbers replace `Fin n`
variables; quantifiers still use the convention that the new variable is the
last coordinate.
-/
inductive RawFormula : Type
  | mem (i j : Nat) : RawFormula
  | eq (i j : Nat) : RawFormula
  | neg (formula : RawFormula) : RawFormula
  | conj (left right : RawFormula) : RawFormula
  | ex (formula : RawFormula) : RawFormula
  deriving DecidableEq

/-- Forget the intrinsic scope proof carried by every variable. -/
def toRaw : {n : Nat} -> FOFormula n -> RawFormula
  | _, .mem i j => .mem i.1 j.1
  | _, .eq i j => .eq i.1 j.1
  | _, .neg formula => .neg (toRaw formula)
  | _, .conj left right => .conj (toRaw left) (toRaw right)
  | _, .ex formula => .ex (toRaw formula)

/-- Make a finite variable from a natural number exactly when it is in scope. -/
def finOfNat? (n i : Nat) : Option (Fin n) :=
  if hi : i < n then some ⟨i, hi⟩ else none

@[simp]
theorem finOfNat?_val {n : Nat} (i : Fin n) :
    finOfNat? n i.1 = some i := by
  simp [finOfNat?, i.2]

/--
Scope-check a raw tree in a context of size `n`.  The body of an existential
is checked in the extended context of size `n + 1`.
-/
def ofRaw : (n : Nat) -> RawFormula -> Option (FOFormula n)
  | n, .mem i j => do
      let i' <- finOfNat? n i
      let j' <- finOfNat? n j
      pure (.mem i' j')
  | n, .eq i j => do
      let i' <- finOfNat? n i
      let j' <- finOfNat? n j
      pure (.eq i' j')
  | n, .neg formula =>
      (ofRaw n formula).map FOFormula.neg
  | n, .conj left right => do
      let left' <- ofRaw n left
      let right' <- ofRaw n right
      pure (.conj left' right')
  | n, .ex formula =>
      (ofRaw (n + 1) formula).map FOFormula.ex

/-- Scope checking recovers every intrinsically scoped formula. -/
@[simp]
theorem ofRaw_toRaw {n : Nat} (formula : FOFormula n) :
    ofRaw n (toRaw formula) = some formula := by
  induction formula with
  | mem i j => simp [toRaw, ofRaw]
  | eq i j => simp [toRaw, ofRaw]
  | neg formula ih => simp [toRaw, ofRaw, ih]
  | conj left right ihLeft ihRight =>
      simp [toRaw, ofRaw, ihLeft, ihRight]
  | ex formula ih => simp [toRaw, ofRaw, ih]

/-- Erasing scope proofs loses no information at a fixed arity. -/
theorem toRaw_injective {n : Nat} :
    Function.Injective (toRaw : FOFormula n -> RawFormula) := by
  intro left right h
  have h' := congrArg (ofRaw n) h
  simpa using h'

/-! ## Natural-number codes -/

/-- Height of a raw syntax tree.  Atomic formulas have height zero. -/
def RawFormula.depth : RawFormula -> Nat
  | .mem _ _ => 0
  | .eq _ _ => 0
  | .neg formula => formula.depth + 1
  | .conj left right => max left.depth right.depth + 1
  | .ex formula => formula.depth + 1

/--
The structural natural-number code of a raw syntax tree.  The outer pair
records its height.  The inner pair records a constructor tag and its data;
recursive data are themselves complete codes.  Recording the height gives the
decoder an explicit structural recursion bound.
-/
def rawNatCode : RawFormula -> Nat
  | .mem i j => Nat.pair 0 (Nat.pair 0 (Nat.pair i j))
  | .eq i j => Nat.pair 0 (Nat.pair 1 (Nat.pair i j))
  | .neg formula =>
      Nat.pair (formula.depth + 1) (Nat.pair 2 (rawNatCode formula))
  | .conj left right =>
      Nat.pair (max left.depth right.depth + 1)
        (Nat.pair 3 (Nat.pair (rawNatCode left) (rawNatCode right)))
  | .ex formula =>
      Nat.pair (formula.depth + 1) (Nat.pair 4 (rawNatCode formula))

/-- Decode a raw syntax code using an explicit upper bound on tree height. -/
def rawNatDecodeAux : Nat -> Nat -> Option RawFormula
  | fuel, code =>
      let tagged := Nat.unpair (Nat.unpair code).2
      match tagged.1 with
      | 0 =>
          let indices := Nat.unpair tagged.2
          some (.mem indices.1 indices.2)
      | 1 =>
          let indices := Nat.unpair tagged.2
          some (.eq indices.1 indices.2)
      | 2 =>
          match fuel with
          | 0 => none
          | fuel + 1 => (rawNatDecodeAux fuel tagged.2).map RawFormula.neg
      | 3 =>
          match fuel with
          | 0 => none
          | fuel + 1 =>
              let children := Nat.unpair tagged.2
              (rawNatDecodeAux fuel children.1).bind fun left =>
                (rawNatDecodeAux fuel children.2).map fun right =>
                  .conj left right
      | 4 =>
          match fuel with
          | 0 => none
          | fuel + 1 => (rawNatDecodeAux fuel tagged.2).map RawFormula.ex
      | _ => none

/-- The height-bounded decoder recovers every code within its bound. -/
theorem rawNatDecodeAux_rawNatCode_of_depth_le (formula : RawFormula)
    {fuel : Nat} (h : formula.depth <= fuel) :
    rawNatDecodeAux fuel (rawNatCode formula) = some formula := by
  induction formula generalizing fuel with
  | mem i j =>
      rw [rawNatDecodeAux.eq_def]
      simp [rawNatCode]
  | eq i j =>
      rw [rawNatDecodeAux.eq_def]
      simp [rawNatCode]
  | neg formula ih =>
      cases fuel with
      | zero => simp [RawFormula.depth] at h
      | succ fuel =>
          have hFormula : formula.depth <= fuel := by
            exact Nat.succ_le_succ_iff.mp h
          simp [rawNatCode, rawNatDecodeAux, ih hFormula]
  | conj left right ihLeft ihRight =>
      cases fuel with
      | zero => simp [RawFormula.depth] at h
      | succ fuel =>
          have hMax : max left.depth right.depth <= fuel := by
            exact Nat.succ_le_succ_iff.mp h
          have hLeft : left.depth <= fuel :=
            (Nat.le_max_left _ _).trans hMax
          have hRight : right.depth <= fuel :=
            (Nat.le_max_right _ _).trans hMax
          simp [rawNatCode, rawNatDecodeAux,
            ihLeft hLeft, ihRight hRight]
  | ex formula ih =>
      cases fuel with
      | zero => simp [RawFormula.depth] at h
      | succ fuel =>
          have hFormula : formula.depth <= fuel := by
            exact Nat.succ_le_succ_iff.mp h
          simp [rawNatCode, rawNatDecodeAux, ih hFormula]

/-- A candidate decoder obtains its recursion bound from the encoded height. -/
def rawNatDecodeCandidate (code : Nat) : Option RawFormula :=
  rawNatDecodeAux (Nat.unpair code).1 code

@[simp]
theorem rawNatDecodeCandidate_rawNatCode (formula : RawFormula) :
    rawNatDecodeCandidate (rawNatCode formula) = some formula := by
  unfold rawNatDecodeCandidate
  have hDepth : (Nat.unpair (rawNatCode formula)).1 = formula.depth := by
    cases formula <;> simp [rawNatCode, RawFormula.depth]
  rw [hDepth]
  exact rawNatDecodeAux_rawNatCode_of_depth_le formula (Nat.le_refl _)

/-- Exact partial decoding: codes outside the encoder's range return `none`. -/
def rawNatDecode (code : Nat) : Option RawFormula :=
  (rawNatDecodeCandidate code).bind fun formula =>
    if rawNatCode formula = code then some formula else none

@[simp]
theorem rawNatDecode_rawNatCode (formula : RawFormula) :
    rawNatDecode (rawNatCode formula) = some formula := by
  simp [rawNatDecode]

/-- Raw syntax codes are injective. -/
theorem rawNatCode_injective : Function.Injective rawNatCode :=
  fun left right h => by
    have h' := congrArg rawNatDecode h
    simpa using h'

@[simp]
theorem rawNatCode_inj {left right : RawFormula} :
    rawNatCode left = rawNatCode right <-> left = right :=
  rawNatCode_injective.eq_iff

/-- The displayed structural code and exact decoder form an `Encodable`
instance; no generated or opaque coding function is involved. -/
instance rawFormulaEncodable : Encodable RawFormula where
  encode := rawNatCode
  decode := rawNatDecode
  encodek := rawNatDecode_rawNatCode

/-- Goedel code of a formula in one fixed variable context. -/
def formulaNatCode {n : Nat} (formula : FOFormula n) : Nat :=
  rawNatCode (toRaw formula)

/-- Decode and scope-check a formula code at arity `n`. -/
def formulaNatDecode (n code : Nat) : Option (FOFormula n) :=
  (rawNatDecode code).bind (ofRaw n)

/-- Formula decoding is a left inverse of formula coding. -/
@[simp]
theorem formulaNatDecode_formulaNatCode {n : Nat} (formula : FOFormula n) :
    formulaNatDecode n (formulaNatCode formula) = some formula := by
  simp [formulaNatDecode, formulaNatCode]

/-- Formula codes are injective at every fixed arity. -/
theorem formulaNatCode_injective {n : Nat} :
    Function.Injective (formulaNatCode : FOFormula n -> Nat) :=
  rawNatCode_injective.comp toRaw_injective

@[simp]
theorem formulaNatCode_inj {n : Nat} {left right : FOFormula n} :
    formulaNatCode left = formulaNatCode right <-> left = right :=
  formulaNatCode_injective.eq_iff

/-- The explicit coding and decoding functions give `FOFormula n` an
`Encodable` instance. -/
instance formulaEncodable (n : Nat) : Encodable (FOFormula n) where
  encode := formulaNatCode
  decode := formulaNatDecode n
  encodek := formulaNatDecode_formulaNatCode

/-! ## Total external enumerations -/

/--
A closed tautology, viewed in any free-variable context.  It supplies an
explicit value when a natural number is not the code of a well-scoped formula.
-/
def defaultFormula (n : Nat) : FOFormula n :=
  .ex (.eq (Fin.last n) (Fin.last n))

/--
A total enumeration of the formulas in one fixed context.  Invalid codes are
sent to `defaultFormula`; this does not turn them into valid syntax codes.
-/
def formulaNatEnumerate (n code : Nat) : FOFormula n :=
  (formulaNatDecode n code).getD (defaultFormula n)

/-- At the displayed code of a formula, total enumeration recovers it. -/
@[simp]
theorem formulaNatEnumerate_formulaNatCode {n : Nat}
    (formula : FOFormula n) :
    formulaNatEnumerate n (formulaNatCode formula) = formula := by
  simp [formulaNatEnumerate]



/-! ## A single type containing formulas of every arity -/

/-- A formula packaged together with the size of its free-variable context. -/
abbrev PackedFormula : Type := Sigma FOFormula

/-- Pair the arity with the fixed-arity formula code. -/
def packedFormulaNatCode (formula : PackedFormula) : Nat :=
  Nat.pair formula.1 (formulaNatCode formula.2)

/-- Recover both the arity and the formula from a packed code. -/
def packedFormulaNatDecode (code : Nat) : Option PackedFormula :=
  let data := Nat.unpair code
  (formulaNatDecode data.1 data.2).map fun formula => ⟨data.1, formula⟩

/-- Packed decoding is a left inverse, including across distinct arities. -/
@[simp]
theorem packedFormulaNatDecode_packedFormulaNatCode
    (formula : PackedFormula) :
    packedFormulaNatDecode (packedFormulaNatCode formula) = some formula := by
  rcases formula with ⟨n, formula⟩
  unfold packedFormulaNatDecode packedFormulaNatCode
  rw [Nat.unpair_pair]
  dsimp only
  rw [formulaNatDecode_formulaNatCode]
  rfl

/-- The arity/formula package has an injective natural-number code. -/
theorem packedFormulaNatCode_injective :
    Function.Injective packedFormulaNatCode := by
  intro left right h
  have h' := congrArg packedFormulaNatDecode h
  simpa using h'

@[simp]
theorem packedFormulaNatCode_inj {left right : PackedFormula} :
    packedFormulaNatCode left = packedFormulaNatCode right <-> left = right :=
  packedFormulaNatCode_injective.eq_iff

/-- The packed formulas have one explicit injective natural-number coding. -/
instance packedFormulaEncodable : Encodable PackedFormula where
  encode := packedFormulaNatCode
  decode := packedFormulaNatDecode
  encodek := packedFormulaNatDecode_packedFormulaNatCode

/-- A fixed packaged formula, used only as the value at invalid packed codes. -/
def defaultPackedFormula : PackedFormula :=
  ⟨0, defaultFormula 0⟩

/--
A single total enumeration containing formulas of every arity.  Pairing the
arity with the structural formula code prevents formulas in different
contexts from being identified.
-/
def packedFormulaNatEnumerate (code : Nat) : PackedFormula :=
  (packedFormulaNatDecode code).getD defaultPackedFormula

/-- Total packed enumeration recovers every packaged formula at its code. -/
@[simp]
theorem packedFormulaNatEnumerate_packedFormulaNatCode
    (formula : PackedFormula) :
    packedFormulaNatEnumerate (packedFormulaNatCode formula) = formula := by
  simp [packedFormulaNatEnumerate]



/-! ## Internal `ZFSet` codes -/





/-- The von Neumann natural-number code of a fixed-arity formula. -/
noncomputable def formulaZFCode {n : Nat} (formula : FOFormula n) : ZFSet.{u} :=
  FiniteSequenceZF.natCode (formulaNatCode formula)

/-- Formula `ZFSet` codes are injective. -/
theorem formulaZFCode_injective {n : Nat} :
    Function.Injective (formulaZFCode : FOFormula n -> ZFSet.{u}) :=
  FiniteSequenceZF.natCode_injective.comp formulaNatCode_injective

@[simp]
theorem formulaZFCode_inj {n : Nat} {left right : FOFormula n} :
    (formulaZFCode left : ZFSet.{u}) = formulaZFCode right <-> left = right :=
  formulaZFCode_injective.eq_iff







/-- The von Neumann natural-number code of an arity/formula package. -/
noncomputable def packedFormulaZFCode (formula : PackedFormula) : ZFSet.{u} :=
  FiniteSequenceZF.natCode (packedFormulaNatCode formula)

/-- Packed formula `ZFSet` codes are injective, including across arities. -/
theorem packedFormulaZFCode_injective :
    Function.Injective (packedFormulaZFCode : PackedFormula -> ZFSet.{u}) :=
  FiniteSequenceZF.natCode_injective.comp packedFormulaNatCode_injective

@[simp]
theorem packedFormulaZFCode_inj {left right : PackedFormula} :
    (packedFormulaZFCode left : ZFSet.{u}) = packedFormulaZFCode right <->
      left = right :=
  packedFormulaZFCode_injective.eq_iff







end FOFormulaCode

end Constructible

end
end GCHSource_Work_CUGCH_FormulaSyntaxCode


/- Source module: Solutions.Work_CUGCH_FullSkolemHull -/
section GCHSource_Work_CUGCH_FullSkolemHull
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Skolem witness-selection primitives

This file constructs one set-valued step used in the standard Skolem-hull
argument. Given a seed, an ambient constructible set `U`, and set-sized
families of internally represented relations and parameter-prefix codes, the
step adjoins their canonical least witnesses. The selected witnesses are an
actual member of `L`, obtained by Separation with one fixed first-order
formula.

This file does not yet enumerate every first-order formula, iterate the
selection step through omega, internalize that sequence by Replacement, or
prove that its union is fully elementary. Those are separate obligations for
a full cardinal-controlled Skolem hull. In particular, closure under every
relation in the unrestricted rudimentary closure of `U` is not a substitute:
nullary singleton relations would force the alleged hull to contain all of
`U`. The standard continuation must use the countable formula syntax,
formula-by-formula canonical witnesses, omega iteration, and the
Tarski--Vaught criterion.
-/

section

open Set

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## A fixed formula selecting a set-sized family of witnesses -/

/-- The graph predicate with arbitrary coordinates in a larger context. -/
def graphRelAt {n : Nat} (relation x y : Fin n) : FOFormula n :=
  FOFormula.rename ![relation, x, y] graphRelFormula

@[simp]
theorem satisfies_graphRelAt {n : Nat} (relation x y : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem (graphRelAt relation x y) s ↔
      GraphRel (s relation) (s x) (s y) := by
  rw [graphRelAt, FOFormula.satisfies_rename,
    satisfies_graphRelFormula]
  have hassign :
      (fun i => s (![relation, x, y] i)) =
        ![s relation, s x, s y] := by
    funext i
    fin_cases i <;> rfl
  have h0 := congrFun hassign (0 : Fin 3)
  have h1 := congrFun hassign (1 : Fin 3)
  have h2 := congrFun hassign (2 : Fin 3)
  change s (![relation, x, y] 0) = s relation at h0
  change s (![relation, x, y] 1) = s x at h1
  change s (![relation, x, y] 2) = s y at h2
  simp only [h0, h1, h2]

/-- In the context `[U, relations, prefixes, order, y, relation]`, assert
that `y` is the canonical least nullary witness belonging to `relation`.
-/
def nullaryRudimentaryWitnessFormula : FOFormula 6 :=
  .conj
    (.mem (4 : Fin 6) (5 : Fin 6))
    (.all
      (FOFormula.imp
        (.conj
          (.mem (6 : Fin 7) (0 : Fin 7))
          (.mem (6 : Fin 7) (5 : Fin 7)))
        (.neg (graphRelAt (3 : Fin 7) (6 : Fin 7) (4 : Fin 7)))))

/-- In the context
`[U, relations, prefixes, order, y, relation, prefix]`, assert that `y` is
the canonical least member of the `prefix`-fiber of `relation`.
-/
def positiveRudimentaryWitnessFormula : FOFormula 7 :=
  .conj
    (.mem (6 : Fin 7) (2 : Fin 7))
    (.conj
      (graphRelAt (5 : Fin 7) (4 : Fin 7) (6 : Fin 7))
      (.all
        (FOFormula.imp
          (.conj
            (.mem (7 : Fin 8) (0 : Fin 8))
            (graphRelAt (5 : Fin 8) (7 : Fin 8) (6 : Fin 8)))
          (.neg (graphRelAt (3 : Fin 8) (7 : Fin 8) (4 : Fin 8))))))

/-- Layout `[U, relations, prefixes, order, y]`.  The formula says that some
`relation ∈ relations` canonically selects `y`, either as a nullary witness or
from a fiber indexed by a member of `prefixes`.
-/
def rudimentaryWitnessSelectionFormula : FOFormula 5 :=
  .ex
    (.conj
      (.mem (5 : Fin 6) (1 : Fin 6))
      (.disj nullaryRudimentaryWitnessFormula
        (.ex positiveRudimentaryWitnessFormula)))

@[simp]
theorem satisfies_nullaryRudimentaryWitnessFormula
    (U relations prefixes order y relation : LCarrier.{u}) :
    FOFormula.Satisfies LMem nullaryRudimentaryWitnessFormula
        ![U, relations, prefixes, order, y, relation] ↔
      y.1 ∈ relation.1 ∧
        ∀ z : LCarrier.{u}, z.1 ∈ U.1 → z.1 ∈ relation.1 →
          ¬ GraphRel order z y := by
  simp only [nullaryRudimentaryWitnessFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt]
  constructor
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z hzU hzRelation
    have hz := hminimal z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation] z =
        ![U, relations, prefixes, order, y, relation, z] by
          funext i
          fin_cases i <;> rfl] at hz
    exact hz ⟨hzU, hzRelation⟩
  · rintro ⟨hy, hminimal⟩
    refine ⟨hy, ?_⟩
    intro z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation] z =
        ![U, relations, prefixes, order, y, relation, z] by
          funext i
          fin_cases i <;> rfl]
    intro hz
    exact hminimal z hz.1 hz.2

@[simp]
theorem satisfies_positiveRudimentaryWitnessFormula
    (U relations prefixes order y relation p : LCarrier.{u}) :
    FOFormula.Satisfies LMem positiveRudimentaryWitnessFormula
        ![U, relations, prefixes, order, y, relation, p] ↔
      p.1 ∈ prefixes.1 ∧ GraphRel relation y p ∧
        ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
          GraphRel relation z p → ¬ GraphRel order z y := by
  simp only [positiveRudimentaryWitnessFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt]
  constructor
  · rintro ⟨hp, hgraph, hminimal⟩
    refine ⟨hp, hgraph, ?_⟩
    intro z hzU hzGraph
    have hz := hminimal z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation, p] z =
        ![U, relations, prefixes, order, y, relation, p, z] by
          funext i
          fin_cases i <;> rfl] at hz
    exact hz ⟨hzU, hzGraph⟩
  · rintro ⟨hp, hgraph, hminimal⟩
    refine ⟨hp, hgraph, ?_⟩
    intro z
    rw [show
      snoc ![U, relations, prefixes, order, y, relation, p] z =
        ![U, relations, prefixes, order, y, relation, p, z] by
          funext i
          fin_cases i <;> rfl]
    intro hz
    exact hminimal z hz.1 hz.2

@[simp]
theorem satisfies_rudimentaryWitnessSelectionFormula
    (U relations prefixes order y : LCarrier.{u}) :
    FOFormula.Satisfies LMem rudimentaryWitnessSelectionFormula
        ![U, relations, prefixes, order, y] ↔
      ∃ relation : LCarrier.{u}, relation.1 ∈ relations.1 ∧
        ((y.1 ∈ relation.1 ∧
            ∀ z : LCarrier.{u}, z.1 ∈ U.1 → z.1 ∈ relation.1 →
              ¬ GraphRel order z y) ∨
          ∃ p : LCarrier.{u}, p.1 ∈ prefixes.1 ∧
            GraphRel relation y p ∧
              ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
                GraphRel relation z p → ¬ GraphRel order z y) := by
  simp only [rudimentaryWitnessSelectionFormula, FOFormula.Satisfies,
    FOFormula.satisfies_disj]
  apply exists_congr
  intro relation
  have hrelationAssignment :
      snoc ![U, relations, prefixes, order, y] relation =
        ![U, relations, prefixes, order, y, relation] := by
    funext i
    fin_cases i <;> rfl
  rw [hrelationAssignment,
    satisfies_nullaryRudimentaryWitnessFormula]
  apply and_congr_right
  intro _hrelation
  apply or_congr Iff.rfl
  apply exists_congr
  intro p
  have hpAssignment :
      snoc ![U, relations, prefixes, order, y, relation] p =
        ![U, relations, prefixes, order, y, relation, p] := by
    funext i
    fin_cases i <;> rfl
  rw [hpAssignment, satisfies_positiveRudimentaryWitnessFormula]

/-- The actual constructible set selected from one relation family and one
prefix-code family.  This operation is generic; controlled hulls instantiate
`relations` by the singleton containing one compiled formula relation, never
by all of `rudimentaryClosure U`.
-/
noncomputable def canonicalWitnessSelection
    (U relations prefixes : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    rudimentaryWitnessSelectionFormula
    ![U, relations, prefixes, canonicalWitnessOrder U]
    U)

@[simp]
theorem mem_canonicalWitnessSelection_iff
    (U relations prefixes y : LCarrier.{u}) :
    y.1 ∈ (canonicalWitnessSelection U relations prefixes).1 ↔
      y.1 ∈ U.1 ∧
        FOFormula.Satisfies LMem rudimentaryWitnessSelectionFormula
          ![U, relations, prefixes, canonicalWitnessOrder U, y] := by
  exact Classical.choose_spec (exists_separationLCarrier
    rudimentaryWitnessSelectionFormula
    ![U, relations, prefixes, canonicalWitnessOrder U]
    U) y







end

end Constructible.Model

end
end GCHSource_Work_CUGCH_FullSkolemHull


/- Source module: Solutions.Work_CUGCH_ParametricUniformOmegaInjectionFamily -/
section GCHSource_Work_CUGCH_ParametricUniformOmegaInjectionFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Canonically collecting injections along a uniform omega family

Suppose every value of a uniformly definable omega family has some internally
represented injection into `kappa`.  This file does not externally choose
those graphs.  It bounds all candidate graphs by the genuine internal
powerset of `H x kappa`, selects the least candidate in the canonical stage
order by one fixed first-order formula, and applies Replacement over the
internal omega.  The result is the actual indexed family of injection graphs
needed by the cardinal-union argument.
-/

section

universe u

namespace Constructible.Model

open Constructible.ContinuumFormula
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-- A common internal container for graphs from family values into `kappa`. -/
def parametricUniformOmegaInjectionGraphContainer
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) : LCarrier.{u} :=
  prodLCarrier (parametricUniformOmegaUnion spec) kappa

/-- The genuine internal powerset which bounds all constructible candidate
injection graphs. -/
noncomputable def parametricUniformOmegaInjectionPower
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_powerSetLCarrier
    (parametricUniformOmegaInjectionGraphContainer spec kappa))

@[simp]
theorem mem_parametricUniformOmegaInjectionPower_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa graph : LCarrier.{u}) :
    graph.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 <->
      graph.1 ⊆
        (parametricUniformOmegaInjectionGraphContainer spec kappa).1 :=
  Classical.choose_spec (exists_powerSetLCarrier
    (parametricUniformOmegaInjectionGraphContainer spec kappa)) graph

/-! ## Candidate sets for the minimum argument -/

/-- Layout `[stage,kappa,graph]`: `graph` is an injection from `stage` to
`kappa`. -/
def uniformOmegaInjectionCandidateFormula : FOFormula 3 :=
  injectionAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_uniformOmegaInjectionCandidateFormula
    (stage kappa graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem uniformOmegaInjectionCandidateFormula
        ![stage, kappa, graph] <->
      IsInjection LMem graph stage kappa := by
  exact satisfies_injectionAt LMem
    (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
      ![stage, kappa, graph]

/-- The actual subset of the common power consisting of injection graphs for
one displayed stage. -/
noncomputable def uniformOmegaInjectionCandidates
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa stage : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    uniformOmegaInjectionCandidateFormula ![stage, kappa]
    (parametricUniformOmegaInjectionPower spec kappa))

@[simp]
theorem mem_uniformOmegaInjectionCandidates_iff
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa stage graph : LCarrier.{u}) :
    graph.1 ∈ (uniformOmegaInjectionCandidates spec kappa stage).1 <->
      graph.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 /\
        IsInjection LMem graph stage kappa := by
  rw [uniformOmegaInjectionCandidates,
    Classical.choose_spec (exists_separationLCarrier
      uniformOmegaInjectionCandidateFormula ![stage, kappa]
      (parametricUniformOmegaInjectionPower spec kappa)) graph]
  change _ /\ FOFormula.Satisfies LMem
    uniformOmegaInjectionCandidateFormula ![stage, kappa, graph] <-> _
  rw [satisfies_uniformOmegaInjectionCandidateFormula]

/-! ## The fixed formula selecting the canonical graph -/

/-- Place the family-value formula in the context obtained after adjoining
the hidden stage variable to
`[specParams,H,kappa,power,order,index,injection]`. -/
def uniformOmegaInjectionStageRename (parameterCount : Nat) :
    Fin (parameterCount + 2) -> Fin (parameterCount + 7) :=
  Fin.lastCases (Fin.last (parameterCount + 6))
    (fun i => Fin.lastCases
      (⟨parameterCount + 4, by omega⟩ : Fin (parameterCount + 7))
      (fun j => Fin.castLE (by omega) j) i)

/--
Layout `[specParams,H,kappa,power,order,index,injection]`.  The hidden stage
is the value of the uniform family at `index`; `injection` is the least graph
in `power` which injects that stage into `kappa`.
-/
def canonicalUniformOmegaInjectionFormula
    {parameterCount : Nat}
    (familyFormula : FOFormula (parameterCount + 2)) :
    FOFormula (parameterCount + 6) :=
  let kappa : Fin (parameterCount + 6) := ⟨parameterCount + 1, by omega⟩
  let power : Fin (parameterCount + 6) := ⟨parameterCount + 2, by omega⟩
  let order : Fin (parameterCount + 6) := ⟨parameterCount + 3, by omega⟩
  let injection : Fin (parameterCount + 6) :=
    ⟨parameterCount + 5, by omega⟩
  .ex <| .conj
    (FOFormula.rename (uniformOmegaInjectionStageRename parameterCount)
      familyFormula)
    (.conj
      (.mem injection.castSucc power.castSucc)
      (.conj
        (injectionAt injection.castSucc (Fin.last (parameterCount + 6))
          kappa.castSucc)
        (.all <| FOFormula.imp
          (.conj
            (.mem (Fin.last (parameterCount + 7))
              power.castSucc.castSucc)
            (injectionAt (Fin.last (parameterCount + 7))
              (Fin.last (parameterCount + 6)).castSucc
              kappa.castSucc.castSucc))
          (.neg (graphRelAt order.castSucc.castSucc
            (Fin.last (parameterCount + 7))
            injection.castSucc.castSucc)))))

/-- Fixed parameters of the canonical-injection formula. -/
def canonicalUniformOmegaInjectionParams
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) : Tuple LCarrier.{u} (parameterCount + 4) :=
  snoc (snoc (snoc (snoc spec.params
    (parametricUniformOmegaUnion spec)) kappa)
    (parametricUniformOmegaInjectionPower spec kappa))
    (canonicalWitnessOrder
      (parametricUniformOmegaInjectionPower spec kappa))

/-- Semantic content of the canonical-injection formula. -/
def IsCanonicalUniformOmegaInjection
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) : Prop :=
  exists stage : LCarrier.{u},
    FOFormula.Satisfies LMem spec.formula
      (snoc (snoc spec.params index) stage) /\
    injection.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 /\
    IsInjection LMem injection stage kappa /\
    forall other : LCarrier.{u},
      other.1 ∈ (parametricUniformOmegaInjectionPower spec kappa).1 ->
      IsInjection LMem other stage kappa ->
        Not (GraphRel
          (canonicalWitnessOrder
            (parametricUniformOmegaInjectionPower spec kappa))
          other injection)

 theorem canonical_injection_stage_assignment
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection stage : LCarrier.{u}) :
    (fun i =>
      snoc
        (snoc
          (snoc (canonicalUniformOmegaInjectionParams spec kappa)
            index)
          injection)
        stage
        (uniformOmegaInjectionStageRename parameterCount i)) =
      snoc (snoc spec.params index) stage := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [uniformOmegaInjectionStageRename, Fin.lastCases_last,
      snoc_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [uniformOmegaInjectionStageRename,
        Fin.lastCases_castSucc, Fin.lastCases_last]
      rw [show (⟨parameterCount + 4, by omega⟩ :
          Fin (parameterCount + 7)) =
          (Fin.last (parameterCount + 4)).castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [snoc_castSucc, snoc_last]
    · simp only [uniformOmegaInjectionStageRename,
        Fin.lastCases_castSucc]
      rw [show Fin.castLE (by omega) k =
          k.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [canonicalUniformOmegaInjectionParams, snoc_castSucc]

 theorem canonical_injection_assignment_kappa
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 1, by omega⟩ :
          Fin (parameterCount + 6)) = kappa := by
  rw [show (⟨parameterCount + 1, by omega⟩ :
      Fin (parameterCount + 6)) =
      (Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [canonicalUniformOmegaInjectionParams,
    snoc_castSucc, snoc_last]

 theorem canonical_injection_assignment_power
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 2, by omega⟩ :
          Fin (parameterCount + 6)) =
      parametricUniformOmegaInjectionPower spec kappa := by
  rw [show (⟨parameterCount + 2, by omega⟩ :
      Fin (parameterCount + 6)) =
      (Fin.last (parameterCount + 2)).castSucc.castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [canonicalUniformOmegaInjectionParams,
    snoc_castSucc, snoc_last]

 theorem canonical_injection_assignment_order
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 3, by omega⟩ :
          Fin (parameterCount + 6)) =
      canonicalWitnessOrder
        (parametricUniformOmegaInjectionPower spec kappa) := by
  rw [show (⟨parameterCount + 3, by omega⟩ :
      Fin (parameterCount + 6)) =
      (Fin.last (parameterCount + 3)).castSucc.castSucc by
    apply Fin.ext
    rfl]
  simp only [canonicalUniformOmegaInjectionParams,
    snoc_castSucc, snoc_last]

 theorem canonical_injection_assignment_injection
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
        injection (⟨parameterCount + 5, by omega⟩ :
          Fin (parameterCount + 6)) = injection := by
  rw [show (⟨parameterCount + 5, by omega⟩ :
      Fin (parameterCount + 6)) = Fin.last (parameterCount + 5) by
    apply Fin.ext
    rfl]
  simp only [snoc_last]

@[simp]
theorem satisfies_canonicalUniformOmegaInjectionFormula
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa index injection : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (canonicalUniformOmegaInjectionFormula spec.formula)
        (snoc
          (snoc (canonicalUniformOmegaInjectionParams spec kappa) index)
          injection) <->
      IsCanonicalUniformOmegaInjection spec kappa index injection := by
  simp only [canonicalUniformOmegaInjectionFormula,
    FOFormula.Satisfies, FOFormula.satisfies_rename,
    satisfies_injectionAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, satisfies_graphRelAt,
    IsCanonicalUniformOmegaInjection, snoc_last, snoc_castSucc]
  apply exists_congr
  intro stage
  rw [canonical_injection_stage_assignment]
  rw [canonical_injection_assignment_injection,
    canonical_injection_assignment_power,
    canonical_injection_assignment_kappa,
    canonical_injection_assignment_order]
  change
    (FOFormula.Satisfies LMem spec.formula
        (snoc (snoc spec.params index) stage) /\
      injection.1 ∈
        (parametricUniformOmegaInjectionPower spec kappa).1 /\
      IsInjection LMem injection stage kappa /\
      forall other : LCarrier.{u},
        (other.1 ∈
          (parametricUniformOmegaInjectionPower spec kappa).1 /\
          IsInjection LMem other stage kappa) ->
          Not (GraphRel
            (canonicalWitnessOrder
              (parametricUniformOmegaInjectionPower spec kappa))
            other injection)) <-> _
  simp only [and_imp]

/-! ## Existence, uniqueness, and Replacement -/





/-- The internally collected canonical injection graphs. -/
structure ParametricUniformOmegaInjectionFamilyData
    {parameterCount : Nat}
    (spec : ParametricUniformOmegaFamilySpec.{u} parameterCount)
    (kappa : LCarrier.{u}) where
  injectionFamily : LCarrier.{u}
  graphFamily : LCarrier.{u}
  isFunctionGraph : IsFunctionGraph LMem injectionFamily
    omegaLCarrier graphFamily
  values_areInjections : forall n : Nat, forall injection : LCarrier.{u},
    GraphValue LMem injectionFamily (natLCarrier n) injection ->
      IsInjection LMem injection (spec.value n) kappa







end

end Constructible.Model

end
end GCHSource_Work_CUGCH_ParametricUniformOmegaInjectionFamily


/- Source module: Solutions.Work_CUGCH_FormulaRestrictionLCarrier -/
section GCHSource_Work_CUGCH_FormulaRestrictionLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Formula-defined restriction graphs in L

For an internally represented graph and one point `top`, Separation selects
exactly those graph pairs whose first coordinate lies in a displayed formula
class and is related to `top` by a displayed formula relation.  The selected
restriction is an actual `LCarrier` and has an exact elementwise semantics.
-/

section

universe u v

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Generic coordinate lemmas -/

theorem satisfies_classFormulaAt_generic
    {A : Type u} (E : A → A → Prop) {n m : Nat}
    (classFormula : FOFormula (n + 1))
    (params : Fin n → Fin m) (x : Fin m) (s : Tuple A m) :
    FOFormula.Satisfies E
        (classFormulaAt classFormula params x) s ↔
      FOFormula.Satisfies E classFormula
        (snoc (fun i => s (params i)) (s x)) := by
  rw [classFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (Fin.lastCases x params i)) =
        snoc (fun i => s (params i)) (s x) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [hassign]

theorem satisfies_relationFormulaAt_generic
    {A : Type u} (E : A → A → Prop) {n m : Nat}
    (relationFormula : FOFormula (n + 2))
    (params : Fin n → Fin m) (left right : Fin m)
    (s : Tuple A m) :
    FOFormula.Satisfies E
        (relationFormulaAt relationFormula params left right) s ↔
      FOFormula.Satisfies E relationFormula
        (snoc (snoc (fun i => s (params i)) (s left)) (s right)) := by
  rw [relationFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s
        (Fin.lastCases right (fun j => Fin.lastCases left params j) i)) =
        snoc (snoc (fun i => s (params i)) (s left)) (s right) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  rw [hassign]

@[simp]
theorem satisfies_kuratowskiPairEqAt_lCarrier_generic {n : Nat}
    (pair left right : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (Delta0Formula.kuratowskiPairEqAt pair left right).toFO s ↔
      (s pair).1 = ZFSet.pair (s left).1 (s right).1 := by
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]

/-! ## The Separation predicate -/

/-- In layout `(params,top,pair)`, the two witnesses are the input and output
coordinates of `pair`. -/
def formulaRestrictionMemberFormula {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2)) : FOFormula (n + 2) :=
  let params : Fin n → Fin (n + 4) :=
    fun i => i.castSucc.castSucc.castSucc.castSucc
  let top : Fin (n + 4) :=
    (Fin.last n).castSucc.castSucc.castSucc
  let pair : Fin (n + 4) :=
    (Fin.last (n + 1)).castSucc.castSucc
  let input : Fin (n + 4) := (Fin.last (n + 2)).castSucc
  let output : Fin (n + 4) := Fin.last (n + 3)
  .ex (.ex
    (.conj
      (Delta0Formula.kuratowskiPairEqAt pair input output).toFO
      (.conj
        (classFormulaAt classFormula params input)
        (relationFormulaAt relationFormula params input top))))

@[simp]
theorem satisfies_formulaRestrictionMemberFormula
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (top pair : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (formulaRestrictionMemberFormula classFormula relationFormula)
        (snoc (snoc params top) pair) ↔
      ∃ input output : LCarrier.{u},
        pair.1 = ZFSet.pair input.1 output.1 ∧
          FOFormula.Satisfies LMem classFormula
            (snoc params input) ∧
          FOFormula.Satisfies LMem relationFormula
            (snoc (snoc params input) top) := by
  simp only [formulaRestrictionMemberFormula, FOFormula.Satisfies]
  apply exists_congr
  intro input
  apply exists_congr
  intro output
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  let full := snoc (snoc (snoc (snoc params top) pair) input) output
  have hpair : full ((Fin.last (n + 1)).castSucc.castSucc) = pair := by
    simp only [full, snoc_castSucc, snoc_last]
  have hinput : full ((Fin.last (n + 2)).castSucc) = input := by
    simp only [full, snoc_castSucc, snoc_last]
  have houtput : full (Fin.last (n + 3)) = output := by
    simp only [full, snoc_last]
  rw [show
    snoc (snoc (snoc (snoc params top) pair) input) output = full by rfl]
  rw [hpair, hinput, houtput]
  rw [satisfies_classFormulaAt_generic,
    satisfies_relationFormulaAt_generic]
  have hparams :
      (fun i =>
        full
          (i.castSucc.castSucc.castSucc.castSucc)) = params := by
    funext i
    simp only [full, snoc_castSucc]
  have htop :
      full
          ((Fin.last n).castSucc.castSucc.castSucc) = top := by
    simp only [full, snoc_castSucc, snoc_last]
  rw [hparams, hinput, htop]

/-! ## The represented restriction -/

/-- Separation of a constructible graph by the formula-defined predecessor
condition. -/
def formulaRestrictionLCarrier {n : Nat}
    (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    (formulaRestrictionMemberFormula classFormula relationFormula)
    (snoc params top) graph)

@[simp]
theorem mem_formulaRestrictionLCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top pair : LCarrier.{u}) :
    pair.1 ∈ (formulaRestrictionLCarrier
      classFormula relationFormula params graph top).1 ↔
      pair.1 ∈ graph.1 ∧
        ∃ input output : LCarrier.{u},
          pair.1 = ZFSet.pair input.1 output.1 ∧
            FOFormula.Satisfies LMem classFormula
              (snoc params input) ∧
            FOFormula.Satisfies LMem relationFormula
              (snoc (snoc params input) top) := by
  rw [formulaRestrictionLCarrier]
  rw [Classical.choose_spec (exists_separationLCarrier
    (formulaRestrictionMemberFormula classFormula relationFormula)
    (snoc params top) graph) pair]
  rw [satisfies_formulaRestrictionMemberFormula]

/-- Raw membership form of the same restriction specification. -/
theorem mem_formulaRestrictionLCarrier_raw_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top : LCarrier.{u}) (pair : ZFSet.{u}) :
    pair ∈ (formulaRestrictionLCarrier
      classFormula relationFormula params graph top).1 ↔
      pair ∈ graph.1 ∧
        ∃ input output : LCarrier.{u},
          pair = ZFSet.pair input.1 output.1 ∧
            FOFormula.Satisfies LMem classFormula
              (snoc params input) ∧
            FOFormula.Satisfies LMem relationFormula
              (snoc (snoc params input) top) := by
  constructor
  · intro hpair
    let pairL : LCarrier.{u} :=
      ⟨pair, mem_L_of_mem hpair
        (formulaRestrictionLCarrier
          classFormula relationFormula params graph top).2⟩
    exact (mem_formulaRestrictionLCarrier_iff
      classFormula relationFormula params graph top pairL).mp hpair
  · rintro ⟨hpairGraph, input, output, hpair, hclass, hrelation⟩
    have hpairL : pair ∈ L := mem_L_of_mem hpairGraph graph.2
    let pairL : LCarrier.{u} := ⟨pair, hpairL⟩
    apply (mem_formulaRestrictionLCarrier_iff
      classFormula relationFormula params graph top pairL).mpr
    exact ⟨hpairGraph, input, output, hpair, hclass, hrelation⟩

/-! ## Compatibility with the textbook restriction formula -/

@[simp]
theorem satisfies_restrictionGraphFormulaAt_lCarrier_iff
    {n m : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Fin n → Fin m) (graph top restriction : Fin m)
    (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (restrictionGraphFormulaAt classFormula relationFormula
          params graph top restriction) s ↔
      ∀ pair : LCarrier.{u},
        pair.1 ∈ (s restriction).1 ↔
          pair.1 ∈ (s graph).1 ∧
            ∃ input output : LCarrier.{u},
              pair.1 = ZFSet.pair input.1 output.1 ∧
                FOFormula.Satisfies LMem classFormula
                  (snoc (fun i => s (params i)) input) ∧
                FOFormula.Satisfies LMem relationFormula
                  (snoc (snoc (fun i => s (params i)) input) (s top)) := by
  simp only [restrictionGraphFormulaAt,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    FOFormula.Satisfies, satisfies_classFormulaAt_generic,
    satisfies_relationFormulaAt_generic,
    satisfies_kuratowskiPairEqAt_lCarrier_generic,
    snoc_last, snoc_castSucc]

@[simp]
theorem satisfies_restrictionGraphFormula_lCarrier_iff
    {n : Nat} (classFormula : FOFormula (n + 1))
    (relationFormula : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n)
    (graph top restriction : LCarrier.{u}) :
    FOFormula.Satisfies LMem
        (restrictionGraphFormula classFormula relationFormula)
        (snoc (snoc (snoc params graph) top) restriction) ↔
      ∀ pair : LCarrier.{u},
        pair.1 ∈ restriction.1 ↔
          pair.1 ∈ graph.1 ∧
            ∃ input output : LCarrier.{u},
              pair.1 = ZFSet.pair input.1 output.1 ∧
                FOFormula.Satisfies LMem classFormula
                  (snoc params input) ∧
                FOFormula.Satisfies LMem relationFormula
                  (snoc (snoc params input) top) := by
  simpa only [restrictionGraphFormula, snoc_last, snoc_castSucc] using
    (satisfies_restrictionGraphFormulaAt_lCarrier_iff
      classFormula relationFormula
      (fun i => i.castSucc.castSucc.castSucc)
      (Fin.last n).castSucc.castSucc
      (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2))
      (snoc (snoc (snoc params graph) top) restriction))



end

end Constructible.Model

end
end GCHSource_Work_CUGCH_FormulaRestrictionLCarrier


/- Source module: Solutions.Work_CUGCH_FunctionGraphFormulaLCarrier -/
section GCHSource_Work_CUGCH_FunctionGraphFormulaLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Textbook function-graph formulas over L

This file gives the exact `LCarrier` semantics of the graph-value and
function-on-domain formulas used in the textbook local recursion predicate.
-/

section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

@[simp]
theorem satisfies_graphValueFormulaAt_lCarrier_iff {m : Nat}
    (graph input value : Fin m) (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (graphValueFormulaAt graph input value) s ↔
      ZFSet.pair (s input).1 (s value).1 ∈ (s graph).1 := by
  rw [graphValueFormulaAt]
  simp only [FOFormula.Satisfies]
  constructor
  · rintro ⟨pair, hpairEq, hpairGraph⟩
    have hpair :=
      (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last m) input.castSucc value.castSucc (snoc s pair)).mp
        hpairEq
    have hpairRaw : pair.1 = ZFSet.pair (s input).1 (s value).1 := by
      simpa only [snoc_last, snoc_castSucc] using hpair
    simp only [snoc_last, snoc_castSucc] at hpairGraph
    change pair.1 ∈ (s graph).1 at hpairGraph
    simpa only [hpairRaw] using hpairGraph
  · intro hpairGraph
    let pair : LCarrier.{u} :=
      ⟨ZFSet.pair (s input).1 (s value).1,
        mem_L_of_mem hpairGraph (s graph).2⟩
    refine ⟨pair, ?_, ?_⟩
    · apply (satisfies_kuratowskiPairEqAt_lCarrier_generic
        (Fin.last m) input.castSucc value.castSucc (snoc s pair)).mpr
      simp only [snoc_last, snoc_castSucc, pair]
    · simp only [snoc_last, snoc_castSucc]
      change pair.1 ∈ (s graph).1
      simpa only [pair] using hpairGraph

@[simp]
theorem satisfies_functionGraphOnFormulaAt_lCarrier_iff {m : Nat}
    (graph domain : Fin m) (s : Tuple LCarrier.{u} m) :
    FOFormula.Satisfies LMem
        (functionGraphOnFormulaAt graph domain) s ↔
      ((∀ input : LCarrier.{u}, input.1 ∈ (s domain).1 →
          ∃ value : LCarrier.{u},
            ZFSet.pair input.1 value.1 ∈ (s graph).1 ∧
              ∀ other : LCarrier.{u},
                ZFSet.pair input.1 other.1 ∈ (s graph).1 →
                  other = value) ∧
        ∀ pair : LCarrier.{u}, pair.1 ∈ (s graph).1 →
          ∃ input : LCarrier.{u}, input.1 ∈ (s domain).1 ∧
            ∃ value : LCarrier.{u},
              pair.1 = ZFSet.pair input.1 value.1) := by
  simp only [functionGraphOnFormulaAt, FOFormula.Satisfies,
    FOFormula.satisfies_boundedAll, FOFormula.satisfies_all,
    FOFormula.satisfies_imp,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    satisfies_kuratowskiPairEqAt_lCarrier_generic,
    snoc_last, snoc_castSucc]

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_FunctionGraphFormulaLCarrier


/- Source module: Solutions.Work_CUGCH_CanonicalStageInjectionFamily -/
section GCHSource_Work_CUGCH_CanonicalStageInjectionFamily
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Canonical internal injection families for constructible stages

Assume that every `L_alpha`, for `alpha < limit`, has an internally
represented injection into `kappa`.  All such graphs are subsets of
`L_limit x kappa`, so the genuine internal powerset of that product is a
single set bounding every candidate.

A fixed first-order formula obtains `L_alpha` through the already internal
`stageValueGraph limit`, and selects the least candidate injection graph in
the canonical witness order on the bounding powerset.  Replacement over the
internal ordinal `limit` then produces the actual family graph.  External
ordinal decoding is used only to prove totality and correctness of this fixed
formula; it is not used as the collected family.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model
open Constructible.FiniteSequenceZF

noncomputable section

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## A common internal bound for all candidate graphs -/

/-- Every candidate graph is bounded by `L_limit x kappa`. -/
def canonicalStageInjectionGraphContainer
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) : LCarrier.{u} :=
  prodLCarrier (stageLCarrier limit) kappa

/-- The genuine internal powerset of the common graph container. -/
noncomputable def canonicalStageInjectionPower
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose
    (exists_powerSetLCarrier
      (canonicalStageInjectionGraphContainer limit kappa))

@[simp]
theorem mem_canonicalStageInjectionPower_iff
    (limit : Ordinal.{u}) (kappa graph : LCarrier.{u}) :
    graph.1 ∈ (canonicalStageInjectionPower limit kappa).1 ↔
      graph.1 ⊆ (canonicalStageInjectionGraphContainer limit kappa).1 :=
  Classical.choose_spec
    (exists_powerSetLCarrier
      (canonicalStageInjectionGraphContainer limit kappa)) graph

/-! ## Candidate sets -/

/-- Layout `[stage,kappa,graph]`: `graph` injects `stage` into `kappa`. -/
def canonicalStageInjectionCandidateFormula : FOFormula 3 :=
  injectionAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

@[simp]
theorem satisfies_canonicalStageInjectionCandidateFormula
    (stage kappa graph : LCarrier.{u}) :
    FOFormula.Satisfies LMem canonicalStageInjectionCandidateFormula
        ![stage, kappa, graph] ↔
      IsInjection LMem graph stage kappa := by
  exact satisfies_injectionAt LMem
    (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
      ![stage, kappa, graph]

/-- The separated set of candidate injections for one displayed stage. -/
noncomputable def canonicalStageInjectionCandidates
    (limit : Ordinal.{u}) (kappa stage : LCarrier.{u}) :
    LCarrier.{u} :=
  Classical.choose
    (exists_separationLCarrier
      canonicalStageInjectionCandidateFormula ![stage, kappa]
      (canonicalStageInjectionPower limit kappa))

@[simp]
theorem mem_canonicalStageInjectionCandidates_iff
    (limit : Ordinal.{u}) (kappa stage graph : LCarrier.{u}) :
    graph.1 ∈ (canonicalStageInjectionCandidates limit kappa stage).1 ↔
      graph.1 ∈ (canonicalStageInjectionPower limit kappa).1 ∧
        IsInjection LMem graph stage kappa := by
  rw [canonicalStageInjectionCandidates,
    Classical.choose_spec
      (exists_separationLCarrier
        canonicalStageInjectionCandidateFormula ![stage, kappa]
        (canonicalStageInjectionPower limit kappa)) graph]
  change _ ∧ FOFormula.Satisfies LMem
    canonicalStageInjectionCandidateFormula ![stage, kappa, graph] ↔ _
  rw [satisfies_canonicalStageInjectionCandidateFormula]

/-! ## The fixed canonical-selection formula -/

/--
Layout `[stageGraph,kappa,power,order,index,injection]`.

The hidden variable is the exact value of `stageGraph` at `index`.
`injection` is the least member of `power` which injects that stage into
`kappa`.
-/
def canonicalStageInjectionFormula : FOFormula 6 :=
  let stageGraph : Fin 6 := 0
  let kappa : Fin 6 := 1
  let power : Fin 6 := 2
  let order : Fin 6 := 3
  let index : Fin 6 := 4
  let injection : Fin 6 := 5
  .ex <| .conj
    (graphValueFormulaAt stageGraph.castSucc index.castSucc (Fin.last 6))
    (.conj
      (.mem injection.castSucc power.castSucc)
      (.conj
        (injectionAt injection.castSucc (Fin.last 6) kappa.castSucc)
        (.all <| FOFormula.imp
          (.conj
            (.mem (Fin.last 7) power.castSucc.castSucc)
            (injectionAt (Fin.last 7) (Fin.last 6).castSucc
              kappa.castSucc.castSucc))
          (.neg
            (graphRelAt order.castSucc.castSucc
              (Fin.last 7) injection.castSucc.castSucc)))))

/-- The four fixed parameters of the canonical-selection formula. -/
def canonicalStageInjectionParams
    (limit : Ordinal.{u}) (kappa : LCarrier.{u}) :
    Tuple LCarrier.{u} 4 :=
  ![stageValueGraph limit, kappa,
    canonicalStageInjectionPower limit kappa,
    canonicalWitnessOrder (canonicalStageInjectionPower limit kappa)]

/-- Exact semantic content of the fixed selection formula. -/
def IsCanonicalStageInjection
    (limit : Ordinal.{u}) (kappa index injection : LCarrier.{u}) : Prop :=
  ∃ stage : LCarrier.{u},
    GraphRel (stageValueGraph limit) index stage ∧
      injection.1 ∈ (canonicalStageInjectionPower limit kappa).1 ∧
      IsInjection LMem injection stage kappa ∧
      ∀ other : LCarrier.{u},
        other.1 ∈ (canonicalStageInjectionPower limit kappa).1 →
        IsInjection LMem other stage kappa →
          ¬ GraphRel
            (canonicalWitnessOrder
              (canonicalStageInjectionPower limit kappa))
            other injection

 theorem canonicalStageInjection_assignment
    (limit : Ordinal.{u}) (kappa index injection : LCarrier.{u}) :
    snoc (snoc (canonicalStageInjectionParams limit kappa) index)
        injection =
      ![stageValueGraph limit, kappa,
        canonicalStageInjectionPower limit kappa,
        canonicalWitnessOrder
          (canonicalStageInjectionPower limit kappa),
        index, injection] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_canonicalStageInjectionFormula
    (limit : Ordinal.{u}) (kappa index injection : LCarrier.{u}) :
    FOFormula.Satisfies LMem canonicalStageInjectionFormula
        (snoc (snoc
          (canonicalStageInjectionParams limit kappa) index) injection) ↔
      IsCanonicalStageInjection limit kappa index injection := by
  rw [canonicalStageInjection_assignment]
  simp only [canonicalStageInjectionFormula, FOFormula.Satisfies,
    satisfies_graphValueFormulaAt_lCarrier_iff,
    satisfies_injectionAt, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, satisfies_graphRelAt,
    snoc_last, snoc_castSucc]
  simp only [and_imp]
  change
    IsCanonicalStageInjection limit kappa index injection ↔
      IsCanonicalStageInjection limit kappa index injection
  rfl

/-! ## Existence and uniqueness of the canonical graph -/

 theorem stageInjection_graph_mem_power
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    {ordinal : Ordinal.{u}} (hordinal : ordinal < limit)
    {graph : LCarrier.{u}}
    (hgraph :
      IsInjection LMem graph (stageLCarrier ordinal) kappa) :
    graph.1 ∈ (canonicalStageInjectionPower limit kappa).1 := by
  apply (mem_canonicalStageInjectionPower_iff
    limit kappa graph).mpr
  intro pairRaw hpair
  let pair : LCarrier.{u} :=
    ⟨pairRaw, mem_L_of_mem hpair graph.2⟩
  rcases hgraph.1 pair hpair with
    ⟨input, hinput, output, houtput, hpairCoordinates⟩
  have hinputLimit :
      input.1 ∈ (stageLCarrier limit).1 := by
    exact LStageZF_mono hordinal.le hinput
  apply ZFSet.mem_prod.mpr
  exact ⟨input.1, hinputLimit, output.1, houtput,
    (isKuratowskiPairOf_lCarrier_iff
      pair input output).mp hpairCoordinates⟩

/--
At each genuine ordinal index below `limit`, the fixed formula has exactly
one output: the canonical least injection graph.
-/
theorem canonicalStageInjectionFormula_existsUnique
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    (ordinal : Ordinal.{u}) (hordinal : ordinal < limit)
    (hinjects :
      Injects LMem (stageLCarrier ordinal) kappa) :
    ExistsUnique fun injection : LCarrier.{u} =>
      FOFormula.Satisfies LMem canonicalStageInjectionFormula
        (snoc (snoc (canonicalStageInjectionParams limit kappa)
          (ordinalLCarrier ordinal)) injection) := by
  let stage := stageLCarrier ordinal
  let power := canonicalStageInjectionPower limit kappa
  let candidates :=
    canonicalStageInjectionCandidates limit kappa stage
  have hcandidatesSubset : ∀ graph : LCarrier.{u},
      graph.1 ∈ candidates.1 →
        graph.1 ∈ (canonicalWitnessStage power).1 := by
    intro graph hgraph
    exact seed_subset_canonicalWitnessStage power
      ((mem_canonicalStageInjectionCandidates_iff
        limit kappa stage graph).mp hgraph).1
  have hcandidatesNonempty : ∃ graph : LCarrier.{u},
      graph.1 ∈ candidates.1 := by
    rcases hinjects with ⟨graph, hgraph⟩
    exact ⟨graph,
      (mem_canonicalStageInjectionCandidates_iff
        limit kappa stage graph).mpr
          ⟨stageInjection_graph_mem_power
            limit kappa hordinal hgraph, hgraph⟩⟩
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders power)
      hcandidatesSubset hcandidatesNonempty with
    ⟨minimum, hminimum, hminimumUnique⟩
  refine ⟨minimum, ?_, ?_⟩
  · apply (satisfies_canonicalStageInjectionFormula
      limit kappa (ordinalLCarrier ordinal) minimum).mpr
    have hstageGraph :
        GraphValue LMem (stageValueGraph limit)
          (ordinalLCarrier ordinal) stage := by
      apply (graphValue_stageValueGraph_iff
        limit (ordinalLCarrier ordinal) stage).mpr
      exact
        ⟨(ordinalLCarrier_mem_ordinalLCarrier_iff
            limit ordinal).mpr hordinal,
          (stageValueAt_ordinal_iff ordinal stage).mpr rfl⟩
    have hcandidate :=
      (mem_canonicalStageInjectionCandidates_iff
        limit kappa stage minimum).mp hminimum.1
    exact ⟨stage,
      (graphValue_lCarrier_iff_graphRel
        (stageValueGraph limit) (ordinalLCarrier ordinal) stage).mp
          hstageGraph,
      hcandidate.1, hcandidate.2,
      fun other hotherPower hotherInjection =>
        hminimum.2 other
          ((mem_canonicalStageInjectionCandidates_iff
            limit kappa stage other).mpr
              ⟨hotherPower, hotherInjection⟩)⟩
  · intro other hother
    rcases
        (satisfies_canonicalStageInjectionFormula
          limit kappa (ordinalLCarrier ordinal) other).mp hother with
      ⟨otherStage, hotherStageGraph, hotherPower,
        hotherInjection, hotherMinimal⟩
    have hotherStageValue :=
      (graphValue_stageValueGraph_iff
        limit (ordinalLCarrier ordinal) otherStage).mp
          ((graphValue_lCarrier_iff_graphRel
            (stageValueGraph limit) (ordinalLCarrier ordinal)
              otherStage).mpr hotherStageGraph)
    have hotherStageEq : otherStage = stage :=
      (stageValueAt_ordinal_iff ordinal otherStage).mp
        hotherStageValue.2
    subst otherStage
    apply hminimumUnique other
    exact
      ⟨(mem_canonicalStageInjectionCandidates_iff
          limit kappa stage other).mpr
            ⟨hotherPower, hotherInjection⟩,
        fun graph hgraph =>
          hotherMinimal graph
            ((mem_canonicalStageInjectionCandidates_iff
              limit kappa stage graph).mp hgraph).1
            ((mem_canonicalStageInjectionCandidates_iff
              limit kappa stage graph).mp hgraph).2⟩

/-! ## Formula data and the internally collected family -/

/--
The pointwise internal injections produce the exact fixed-formula data
required by `InternalStageInjectionFormulaData`.
-/
noncomputable def canonicalStageInjectionFormulaData
    (limit : Ordinal.{u}) (kappa : LCarrier.{u})
    (hinjects : ∀ ordinal : Ordinal.{u}, ordinal < limit →
      Injects LMem (stageLCarrier ordinal) kappa) :
    InternalStageInjectionFormulaData limit kappa where
  arity := 4
  formula := canonicalStageInjectionFormula
  params := canonicalStageInjectionParams limit kappa
  existsUnique_output := by
    intro index hindex
    rcases exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    exact canonicalStageInjectionFormula_existsUnique
      limit kappa ordinal hordinal (hinjects ordinal hordinal)
  output_isInjection := by
    intro ordinal hordinal injection hformula
    rcases
        (satisfies_canonicalStageInjectionFormula
          limit kappa (ordinalLCarrier ordinal) injection).mp hformula with
      ⟨stage, hstageGraph, _hpower, hinjection, _hminimal⟩
    have hstageValue :=
      (graphValue_stageValueGraph_iff
        limit (ordinalLCarrier ordinal) stage).mp
          ((graphValue_lCarrier_iff_graphRel
            (stageValueGraph limit) (ordinalLCarrier ordinal) stage).mpr
              hstageGraph)
    have hstageEq : stage = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal stage).mp hstageValue.2
    simpa only [hstageEq] using hinjection



/-! ## The exact Hartogs interface -/



end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_CanonicalStageInjectionFamily


