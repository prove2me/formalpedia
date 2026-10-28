-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library12
-- name    : CH_ConstructibleGCH_Library12
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:38:57.10228+00:00
-- url     : https://prove2.me/theorems/95581749-4ae6-41a1-a1d1-4b540264d7a7
-- title:
--   Multiplication graphs in transitive models
-- statement:
--   This library supplies a first-order description of multiplication on coded natural numbers and its evaluation interfaces in the relevant transitive models. These graphs are used by the arithmetic coding of finite formulas and requests.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookNaturalMultiplication.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library11
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookNaturalMultiplication -/
section GCHSource_Work_CUGCH_TextbookNaturalMultiplication
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The set-theoretic graph of multiplication on the standard natural numbers

Multiplication is defined in the pure membership language by finite recursion
from the already constructed addition graph.  With free-variable layout
`[omega, x, y, z]`, the formula asserts the existence of a finite function
`f : y + 1 -> omega` such that `f(0) = 0`, `f(y) = z`, and
`f(k + 1) = f(k) + x` for every `k in y`.

Lean's `Nat.mul` occurs only in the canonical witness and in the
metatheoretic statement of the exact semantics.  It is not an added symbol
of the object language.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookNatFormula

 theorem satisfiesIn_boundedEx_iff_TextbookNaturalMultiplication_gch
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedEx set formula) s <->
      exists value : ZFSet.{u}, value ∈ M /\ value ∈ s set /\
        Model.SatisfiesIn M formula (snoc s value) := by
  simp [FOFormula.boundedEx]

 theorem satisfiesIn_boundedAll_iff_TextbookNaturalMultiplication_gch
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall value : ZFSet.{u}, value ∈ M -> value ∈ s set ->
        Model.SatisfiesIn M formula (snoc s value) := by
  classical
  simp only [FOFormula.boundedAll, Model.SatisfiesIn,
    satisfiesIn_boundedEx_iff_TextbookNaturalMultiplication_gch]
  constructor
  · intro h value hvalueM hvalueSet
    by_contra hformula
    exact h ⟨value, hvalueM, hvalueSet, hformula⟩
  · intro h hex
    rcases hex with ⟨value, hvalueM, hvalueSet, hformula⟩
    exact hformula (h value hvalueM hvalueSet)

 theorem satisfiesIn_rename_iff_TextbookNaturalMultiplication_gch
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    Model.SatisfiesIn M (FOFormula.rename rename formula) s <->
      Model.SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, Model.SatisfiesIn, ih]
      constructor
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-! ## The finite-recursion formula -/

/--
Rename the addition formula into the innermost multiplication-step context.
The ambient context has four freshly bound variables after its original
variables: `k`, `kSucc`, `value`, and `nextValue`.  Addition receives
`[omega, value, x, nextValue]`.
-/
def natMulAddRenameAt {n : Nat} (omega x : Fin n) :
    Fin 4 -> Fin (n + 4) :=
  ![omega.castSucc.castSucc.castSucc.castSucc,
    (Fin.last (n + 2)).castSucc,
    x.castSucc.castSucc.castSucc.castSucc,
    Fin.last (n + 3)]

theorem comp_natMulAddRenameAt {A : Type u} {n : Nat}
    (s : Tuple A n) (omega x : Fin n)
    (k kSucc value nextValue : A) :
    (fun i =>
      snoc (snoc (snoc (snoc s k) kSucc) value) nextValue
        (natMulAddRenameAt omega x i)) =
      ![s omega, value, s x, nextValue] := by
  funext i
  fin_cases i <;> simp [natMulAddRenameAt]

/--
The recursive transition, in an arbitrary free-variable context.  It says
that for each `k in y`, the graph values at `k` and `k + 1` are related by
the independently defined addition formula.
-/
def natMulTransitionAt {n : Nat}
    (omega x y ySucc graph : Fin n) : FOFormula n :=
  FOFormula.boundedAll y
    (FOFormula.boundedEx ySucc.castSucc
      (.conj
        (Delta0Formula.successorAt
          (Fin.last (n + 1)) (Fin.last n).castSucc).toFO
        (FOFormula.boundedEx omega.castSucc.castSucc
          (.conj
            (TextbookDefFormula.graphValueDeltaAt
              graph.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 2))).toFO
            (FOFormula.boundedEx omega.castSucc.castSucc.castSucc
              (.conj
                (TextbookDefFormula.graphValueDeltaAt
                  graph.castSucc.castSucc.castSucc.castSucc
                  (Fin.last (n + 1)).castSucc.castSucc
                  (Fin.last (n + 3))).toFO
                (FOFormula.rename (natMulAddRenameAt omega x)
                  natAddFormula)))))))

/-- Fixed layout `[omega, x, y, z, ySucc, graph]`. -/
def natMulTransition : FOFormula 6 :=
  natMulTransitionAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/--
The bounded part of the graph condition.  It asserts that `graph` is a
function `ySucc -> omega`, sends zero to zero, and sends `y` to `z`.
-/
def natMulGraphShapeDeltaAt {n : Nat}
    (omega y z ySucc graph : Fin n) : Delta0Formula n :=
  .conj
    (TextbookDefFormula.isFunctionDeltaAt graph ySucc omega)
    (.conj
      (Delta0Formula.boundedEx ySucc
        (.conj
          (Delta0Formula.emptyDeltaAt (Fin.last n))
          (TextbookDefFormula.graphValueDeltaAt
            graph.castSucc (Fin.last n) (Fin.last n))))
      (TextbookDefFormula.graphValueDeltaAt graph y z))

/-- Fixed layout `[omega, x, y, z, ySucc, graph]`. -/
def natMulGraphShapeDelta : Delta0Formula 6 :=
  natMulGraphShapeDeltaAt
    (0 : Fin 6) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/-- Complete graph condition in layout `[omega, x, y, z, ySucc, graph]`. -/
def natMulGraphFormula : FOFormula 6 :=
  .conj natMulGraphShapeDelta.toFO natMulTransition

/--
Pure membership-language formula for natural-number multiplication.  The
free-variable layout is `[omega, x, y, z]`; `omega` is explicitly required
to be the internally least inductive set.
-/
def natMulFormula : FOFormula 4 :=
  .conj
    (Model.standardOmegaAt (0 : Fin 4))
    (.conj
      (.mem (1 : Fin 4) (0 : Fin 4))
      (.conj
        (.mem (2 : Fin 4) (0 : Fin 4))
        (.conj
          (.mem (3 : Fin 4) (0 : Fin 4))
          (.ex
            (.conj
              (Delta0Formula.successorAt
                (Fin.last 4) (2 : Fin 4).castSucc).toFO
              (.ex natMulGraphFormula))))))

/-- Safely place the fixed multiplication formula in an arbitrary larger
free-variable context. -/
def natMulFormulaAt {n : Nat} (omega x y z : Fin n) : FOFormula n :=
  FOFormula.rename ![omega, x, y, z] natMulFormula

theorem comp_natMulFormulaAtRename {A : Type u} {n : Nat}
    (s : Tuple A n) (omega x y z : Fin n) :
    (fun i => s (![omega, x, y, z] i)) =
      ![s omega, s x, s y, s z] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_natMulFormulaAt {A : Type u}
    (membership : A -> A -> Prop) {n : Nat}
    (s : Tuple A n) (omega x y z : Fin n) :
    FOFormula.Satisfies membership (natMulFormulaAt omega x y z) s <->
      FOFormula.Satisfies membership natMulFormula
        ![s omega, s x, s y, s z] := by
  rw [natMulFormulaAt, FOFormula.satisfies_rename,
    comp_natMulFormulaAtRename]

@[simp]
theorem satisfiesIn_natMulFormulaAt (M : Set ZFSet.{u}) {n : Nat}
    (s : Tuple ZFSet.{u} n) (omega x y z : Fin n) :
    Model.SatisfiesIn M (natMulFormulaAt omega x y z) s <->
      Model.SatisfiesIn M natMulFormula
        ![s omega, s x, s y, s z] := by
  rw [natMulFormulaAt, satisfiesIn_rename_iff_TextbookNaturalMultiplication_gch,
    comp_natMulFormulaAtRename]

/-! ## Ambient semantics -/

@[simp]
theorem satisfies_natMulTransitionAt {n : Nat}
    (omega x y ySucc graph : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (natMulTransitionAt omega x y ySucc graph) s <->
      forall k, k ∈ s y ->
        insert k k ∈ s ySucc /\
        exists value, value ∈ s omega /\
          ZFSet.pair k value ∈ s graph /\
          exists nextValue, nextValue ∈ s omega /\
            ZFSet.pair (insert k k) nextValue ∈ s graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
              ![s omega, value, s x, nextValue] := by
  simp only [natMulTransitionAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_boundedEx, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_successorAt,
    TextbookDefFormula.satisfies_graphValueDeltaAt,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_natMulAddRenameAt]
  constructor
  · intro h k hk
    rcases h k hk with
      ⟨kSucc, hkSuccDomain, rfl, value, hvalueOmega,
        hvalue, nextValue, hnextOmega, hnext, hadd⟩
    exact ⟨hkSuccDomain, value, hvalueOmega, hvalue,
      nextValue, hnextOmega, hnext, hadd⟩
  · intro h k hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalue,
        nextValue, hnextOmega, hnext, hadd⟩
    exact ⟨insert k k, hkSuccDomain, rfl, value, hvalueOmega,
      hvalue, nextValue, hnextOmega, hnext, hadd⟩

@[simp]
theorem satisfies_natMulTransition
    (omega x y z ySucc graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natMulTransition
        ![omega, x, y, z, ySucc, graph] <->
      forall k, k ∈ y ->
        insert k k ∈ ySucc /\
        exists value, value ∈ omega /\
          ZFSet.pair k value ∈ graph /\
          exists nextValue, nextValue ∈ omega /\
            ZFSet.pair (insert k k) nextValue ∈ graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
              ![omega, value, x, nextValue] := by
  exact
    (satisfies_natMulTransitionAt
      (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
      (4 : Fin 6) (5 : Fin 6)
      ![omega, x, y, z, ySucc, graph])

@[simp]
theorem satisfies_natMulGraphShapeDeltaAt {n : Nat}
    (omega y z ySucc graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (natMulGraphShapeDeltaAt omega y z ySucc graph) s <->
      ZFSet.IsFunc (s ySucc) (s omega) (s graph) /\
      ((∅ : ZFSet.{u}) ∈ s ySucc /\
        ZFSet.pair ∅ ∅ ∈ s graph) /\
      ZFSet.pair (s y) (s z) ∈ s graph := by
  simp [natMulGraphShapeDeltaAt]

@[simp]
theorem satisfies_natMulGraphShapeDelta
    (omega x y z ySucc graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natMulGraphShapeDelta
        ![omega, x, y, z, ySucc, graph] <->
      ZFSet.IsFunc ySucc omega graph /\
      ((∅ : ZFSet.{u}) ∈ ySucc /\ ZFSet.pair ∅ ∅ ∈ graph) /\
      ZFSet.pair y z ∈ graph := by
  simp [natMulGraphShapeDelta]

@[simp]
theorem satisfies_natMulGraphFormula
    (omega x y z ySucc graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natMulGraphFormula
        ![omega, x, y, z, ySucc, graph] <->
      ZFSet.IsFunc ySucc omega graph /\
      ((∅ : ZFSet.{u}) ∈ ySucc /\ ZFSet.pair ∅ ∅ ∈ graph) /\
      ZFSet.pair y z ∈ graph /\
      (forall k, k ∈ y ->
        insert k k ∈ ySucc /\
        exists value, value ∈ omega /\
          ZFSet.pair k value ∈ graph /\
          exists nextValue, nextValue ∈ omega /\
            ZFSet.pair (insert k k) nextValue ∈ graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
              ![omega, value, x, nextValue]) := by
  rw [natMulGraphFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    satisfies_natMulGraphShapeDelta, satisfies_natMulTransition]
  tauto

/-! ## Restricted semantics of the transition -/

theorem satisfiesIn_natMulTransition_iff_ambient
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (omega x y z ySucc graph : ZFSet.{u})
    (homegaM : omega ∈ M) (hxM : x ∈ M) (hyM : y ∈ M)
    (hzM : z ∈ M) (hySuccM : ySucc ∈ M) (hgraphM : graph ∈ M)
    (homega : omega = Ordinal.omega0.toZFSet) (hxOmega : x ∈ omega) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natMulTransition
        ![omega, x, y, z, ySucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natMulTransition
        ![omega, x, y, z, ySucc, graph] := by
  subst omega
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hxOmega with
    ⟨a, rfl⟩
  let s : Tuple ZFSet.{u} 6 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
      y, z, ySucc, graph]
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hxM
    · exact hyM
    · exact hzM
    · exact hySuccM
    · exact hgraphM
  change Model.SatisfiesIn (M : Set ZFSet.{u}) natMulTransition s <->
    FOFormula.Satisfies Delta0Formula.ZFMem natMulTransition s
  rw [satisfies_natMulTransition]
  rw [natMulTransition, natMulTransitionAt,
    satisfiesIn_boundedAll_iff_TextbookNaturalMultiplication_gch]
  simp only [s]
  constructor
  · intro h k hk
    have hkM : k ∈ M := hM.1.mem_trans hk hyM
    have hkbody := h k hkM hk
    rw [satisfiesIn_boundedEx_iff_TextbookNaturalMultiplication_gch] at hkbody
    rcases hkbody with
      ⟨kSucc, hkSuccM, hkSuccDomain, hsucc, hrest⟩
    have hskkM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc (snoc s k) kSucc) :=
      Model.tupleIn_snoc_iff.mpr
        ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
    have hsuccAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc s k) kSucc) hskkM).mp hsucc
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hsuccAmbient
    have hkSuccEq : kSucc = insert k k := by
      simpa only [snoc_last, snoc_castSucc] using hsuccAmbient
    rw [satisfiesIn_boundedEx_iff_TextbookNaturalMultiplication_gch] at hrest
    rcases hrest with
      ⟨value, hvalueM, hvalueOmega, hvalueFormula, hnextRest⟩
    have hskkvM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc (snoc (snoc s k) kSucc) value) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskkM, hvalueM⟩
    have hvalueAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc
          (Fin.last 6).castSucc.castSucc
          (Fin.last (6 + 2)))
        (snoc (snoc (snoc s k) kSucc) value) hskkvM).mp
          hvalueFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hvalueAmbient
    have hvalueAssign :
        snoc (snoc (snoc s k) kSucc) value =
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
            y, z, ySucc, graph, k, kSucc, value] := by
      funext i
      fin_cases i <;> rfl
    rw [hvalueAssign] at hvalueAmbient
    have hvalueGraph : ZFSet.pair k value ∈ graph := by
      exact hvalueAmbient
    rw [satisfiesIn_boundedEx_iff_TextbookNaturalMultiplication_gch] at hnextRest
    rcases hnextRest with
      ⟨nextValue, hnextM, hnextOmega, hnextFormula, haddRenamed⟩
    have hskkvnM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc (snoc (snoc (snoc s k) kSucc) value) nextValue) :=
      Model.tupleIn_snoc_iff.mpr ⟨hskkvM, hnextM⟩
    have hnextAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (TextbookDefFormula.graphValueDeltaAt
          (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
          (Fin.last (6 + 1)).castSucc.castSucc
          (Fin.last (6 + 3)))
        (snoc (snoc (snoc (snoc s k) kSucc) value) nextValue)
        hskkvnM).mp hnextFormula
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_graphValueDeltaAt] at hnextAmbient
    change ZFSet.pair kSucc nextValue ∈ graph at hnextAmbient
    have hnextGraph : ZFSet.pair kSucc nextValue ∈ graph := by
      exact hnextAmbient
    rw [satisfiesIn_rename_iff_TextbookNaturalMultiplication_gch,
      comp_natMulAddRenameAt] at haddRenamed
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
        hvalueOmega with ⟨c, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
        hnextOmega with ⟨d, rfl⟩
    have haddEq : (natCode d : ZFSet.{u}) = natCode (c + a) :=
      (satisfiesIn_natAddFormula_natCode_iff hM c a hnextM).mp
        haddRenamed
    have haddAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode c,
            natCode a, natCode d] :=
      (satisfies_natAddFormula_natCode_iff c a (natCode d)).mpr haddEq
    rw [hkSuccEq] at hkSuccDomain hnextGraph
    exact ⟨hkSuccDomain, natCode c, hvalueOmega, hvalueGraph,
      natCode d, hnextOmega, hnextGraph, haddAmbient⟩
  · intro h k hkM hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalueGraph,
        nextValue, hnextOmega, hnextGraph, haddAmbient⟩
    have hkSuccM : insert k k ∈ M :=
      hM.1.mem_trans hkSuccDomain hySuccM
    have hvalueM : value ∈ M := hM.1.mem_trans hvalueOmega homegaM
    have hnextM : nextValue ∈ M := hM.1.mem_trans hnextOmega homegaM
    refine ⟨insert k k, hkSuccM, hkSuccDomain, ?_, ?_⟩
    · have hskkM : Model.TupleIn (M : Set ZFSet.{u})
          (snoc (snoc s k) (insert k k)) :=
        Model.tupleIn_snoc_iff.mpr
          ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
      apply (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last (6 + 1)) (Fin.last 6).castSucc)
        (snoc (snoc s k) (insert k k)) hskkM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simp only [snoc_last, snoc_castSucc]
    · refine ⟨value, hvalueM, hvalueOmega, ?_,
        nextValue, hnextM, hnextOmega, ?_, ?_⟩
      · have hskkM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc s k) (insert k k)) :=
          Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
        have hassignM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc (snoc s k) (insert k k)) value) :=
          Model.tupleIn_snoc_iff.mpr ⟨hskkM, hvalueM⟩
        apply (Model.satisfiesIn_delta0_iff hM.1
          (TextbookDefFormula.graphValueDeltaAt
            (5 : Fin 6).castSucc.castSucc.castSucc
            (Fin.last 6).castSucc.castSucc
            (Fin.last (6 + 2)))
          (snoc (snoc (snoc s k) (insert k k)) value)
          hassignM).mpr
        rw [Delta0Formula.satisfies_toFO,
          TextbookDefFormula.satisfies_graphValueDeltaAt]
        have hvalueAssign :
            snoc (snoc (snoc s k) (insert k k)) value =
              ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
                y, z, ySucc, graph, k, insert k k, value] := by
          funext i
          fin_cases i <;> rfl
        rw [hvalueAssign]
        exact hvalueGraph
      · have hskkM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc s k) (insert k k)) :=
          Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, hkM⟩, hkSuccM⟩
        have hskkvM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc (snoc s k) (insert k k)) value) :=
          Model.tupleIn_snoc_iff.mpr ⟨hskkM, hvalueM⟩
        have hassignM : Model.TupleIn (M : Set ZFSet.{u})
            (snoc (snoc (snoc (snoc s k) (insert k k)) value)
              nextValue) :=
          Model.tupleIn_snoc_iff.mpr ⟨hskkvM, hnextM⟩
        apply (Model.satisfiesIn_delta0_iff hM.1
          (TextbookDefFormula.graphValueDeltaAt
            (5 : Fin 6).castSucc.castSucc.castSucc.castSucc
            (Fin.last (6 + 1)).castSucc.castSucc
            (Fin.last (6 + 3)))
          (snoc (snoc (snoc (snoc s k) (insert k k)) value)
            nextValue) hassignM).mpr
        rw [Delta0Formula.satisfies_toFO,
          TextbookDefFormula.satisfies_graphValueDeltaAt]
        change ZFSet.pair (insert k k) nextValue ∈ graph
        exact hnextGraph
      · rw [satisfiesIn_rename_iff_TextbookNaturalMultiplication_gch, comp_natMulAddRenameAt]
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
            hvalueOmega with ⟨c, rfl⟩
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
            hnextOmega with ⟨d, rfl⟩
        have haddEq : (natCode d : ZFSet.{u}) = natCode (c + a) :=
          (satisfies_natAddFormula_natCode_iff c a (natCode d)).mp
            haddAmbient
        exact (satisfiesIn_natAddFormula_natCode_iff hM c a hnextM).mpr
          haddEq

theorem satisfiesIn_natMulGraphFormula_iff_ambient
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (omega x y z ySucc graph : ZFSet.{u})
    (homegaM : omega ∈ M) (hxM : x ∈ M) (hyM : y ∈ M)
    (hzM : z ∈ M) (hySuccM : ySucc ∈ M) (hgraphM : graph ∈ M)
    (homega : omega = Ordinal.omega0.toZFSet) (hxOmega : x ∈ omega) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natMulGraphFormula
        ![omega, x, y, z, ySucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natMulGraphFormula
        ![omega, x, y, z, ySucc, graph] := by
  let s : Tuple ZFSet.{u} 6 := ![omega, x, y, z, ySucc, graph]
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hxM
    · exact hyM
    · exact hzM
    · exact hySuccM
    · exact hgraphM
  change
    (Model.SatisfiesIn (M : Set ZFSet.{u})
        natMulGraphShapeDelta.toFO s /\
      Model.SatisfiesIn (M : Set ZFSet.{u}) natMulTransition s) <->
    (FOFormula.Satisfies Delta0Formula.ZFMem
        natMulGraphShapeDelta.toFO s /\
      FOFormula.Satisfies Delta0Formula.ZFMem natMulTransition s)
  rw [Model.satisfiesIn_delta0_iff hM.1
    natMulGraphShapeDelta s hsM]
  have htransition := satisfiesIn_natMulTransition_iff_ambient
    hM omega x y z ySucc graph homegaM hxM hyM hzM
      hySuccM hgraphM homega hxOmega
  simpa only [s] using and_congr Iff.rfl htransition

/-! ## Canonical finite graphs -/

/-- The canonical tuple `k |-> natCode (a * k)` of length `b + 1`. -/
noncomputable def natMulCanonicalTuple (a b : Nat) :
    Tuple (ZFCarrier (Ordinal.omega0.toZFSet : ZFSet.{u})) (b + 1) :=
  fun i =>
    ⟨natCode (a * i.1),
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a * i.1))).mpr ⟨a * i.1, rfl⟩⟩

/-- The Kuratowski graph of the canonical multiplication recursion. -/
noncomputable def natMulCanonicalGraph (a b : Nat) : ZFSet.{u} :=
  textbookTupleGraph (natMulCanonicalTuple a b)

theorem natMulCanonicalGraph_isFunc (a b : Nat) :
    ZFSet.IsFunc (natCode (b + 1)) Ordinal.omega0.toZFSet
      (natMulCanonicalGraph a b) := by
  exact textbookTupleGraph_isFunc (natMulCanonicalTuple a b)

@[simp]
theorem natMulCanonicalGraph_value (a b : Nat) (i : Fin (b + 1)) :
    ZFSet.pair (natCode i.1) (natCode (a * i.1)) ∈
      natMulCanonicalGraph a b := by
  exact textbookTupleGraph_value (natMulCanonicalTuple a b) i

theorem natMulCanonicalGraph_satisfies (a b : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem natMulGraphFormula
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
        natCode (a * b), natCode (b + 1), natMulCanonicalGraph a b] := by
  rw [satisfies_natMulGraphFormula]
  refine ⟨natMulCanonicalGraph_isFunc a b, ?_, ?_, ?_⟩
  · constructor
    · apply (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (∅ : ZFSet.{u}) (b + 1)).mpr
      exact ⟨0, Nat.zero_lt_succ b, by simp [natCode]⟩
    · simpa [natCode] using
        (natMulCanonicalGraph_value a b ⟨0, Nat.zero_lt_succ b⟩)
  · simpa using
      (natMulCanonicalGraph_value a b ⟨b, Nat.lt_succ_self b⟩)
  · intro k hk
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt k b).mp hk with
      ⟨j, hj, rfl⟩
    refine ⟨?_, natCode (a * j), ?_, ?_,
      natCode (a * (j + 1)), ?_, ?_, ?_⟩
    · rw [← natCode_succ_eq_insert]
      exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode (j + 1)) (b + 1)).mpr
          ⟨j + 1, Nat.succ_lt_succ hj, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a * j))).mpr ⟨a * j, rfl⟩
    · exact natMulCanonicalGraph_value a b
        ⟨j, hj.trans (Nat.lt_succ_self b)⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a * (j + 1)))).mpr ⟨a * (j + 1), rfl⟩
    · rw [← natCode_succ_eq_insert]
      exact natMulCanonicalGraph_value a b
          ⟨j + 1, Nat.succ_lt_succ hj⟩
    · apply (satisfies_natAddFormula_natCode_iff (a * j) a
        (natCode (a * (j + 1)))).mpr
      simp [Nat.mul_succ]

theorem natMulCanonicalGraph_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (a b : Nat) : natMulCanonicalGraph a b ∈ M := by
  exact Model.finiteIsFunc_mem_of_isTransitiveZFModel hM
    (Model.omega_toZFSet_mem_of_isTransitiveZFModel hM)
    (natMulCanonicalGraph_isFunc a b)

theorem natMulCanonicalGraph_satisfiesIn
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (a b : Nat) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natMulGraphFormula
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
        natCode (a * b), natCode (b + 1), natMulCanonicalGraph a b] := by
  have homegaM := Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have haM := Model.natCode_mem_of_isTransitiveZFModel hM a
  have hbM := Model.natCode_mem_of_isTransitiveZFModel hM b
  have houtM := Model.natCode_mem_of_isTransitiveZFModel hM (a * b)
  have hsuccM := Model.natCode_mem_of_isTransitiveZFModel hM (b + 1)
  have hgraphM := natMulCanonicalGraph_mem_of_isTransitiveZFModel hM a b
  have haOmega : (natCode a : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode a)).mpr ⟨a, rfl⟩
  apply (satisfiesIn_natMulGraphFormula_iff_ambient hM
    Ordinal.omega0.toZFSet (natCode a) (natCode b)
    (natCode (a * b)) (natCode (b + 1)) (natMulCanonicalGraph a b)
    homegaM haM hbM houtM hsuccM hgraphM rfl haOmega).mpr
  exact natMulCanonicalGraph_satisfies a b

/-! ## Uniqueness of the finite recursion -/

theorem natMulGraphFormula_output_unique
    (a b : Nat) (z ySucc graph : ZFSet.{u})
    (hySucc : ySucc = natCode (b + 1))
    (hgraph :
      FOFormula.Satisfies Delta0Formula.ZFMem natMulGraphFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
          z, ySucc, graph]) :
    z = natCode (a * b) := by
  rw [satisfies_natMulGraphFormula] at hgraph
  rcases hgraph with ⟨hfunc, hzero, hyValue, hstep⟩
  have hvalues : forall j : Nat, j <= b ->
      ZFSet.pair (natCode j) (natCode (a * j)) ∈ graph := by
    intro j hj
    induction j with
    | zero =>
        simpa [natCode] using hzero.2
    | succ j ih =>
        have hjb : j < b := Nat.lt_of_succ_le hj
        rcases hstep (natCode j)
            ((IndexedSequenceZF.mem_natCode_iff_exists_lt
              (natCode j) b).mpr ⟨j, hjb, rfl⟩) with
          ⟨_hkSuccDomain, value, _hvalueOmega, hvalue,
            nextValue, _hnextOmega, hnext, hadd⟩
        have hjDomain : (natCode j : ZFSet.{u}) ∈ ySucc := by
          rw [hySucc]
          exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
            (natCode j) (b + 1)).mpr
              ⟨j, hjb.trans (Nat.lt_succ_self b), rfl⟩
        rcases hfunc.2 (natCode j) hjDomain with
          ⟨output, _houtput, hunique⟩
        have hprevious := ih (Nat.le_of_lt hjb)
        have hvalueEq : value = natCode (a * j) :=
          (hunique value hvalue).trans
            (hunique (natCode (a * j)) hprevious).symm
        have hnextValueEq : nextValue = natCode (a * (j + 1)) := by
          rw [hvalueEq] at hadd
          have haddEq :=
            (satisfies_natAddFormula_natCode_iff (a * j) a nextValue).mp hadd
          exact haddEq.trans (by rw [Nat.mul_succ])
        rw [← natCode_succ_eq_insert, hnextValueEq] at hnext
        simpa using hnext
  have hbDomain : (natCode b : ZFSet.{u}) ∈ ySucc := by
    rw [hySucc]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode b) (b + 1)).mpr ⟨b, Nat.lt_succ_self b, rfl⟩
  rcases hfunc.2 (natCode b) hbDomain with
    ⟨output, _houtput, hunique⟩
  exact (hunique z hyValue).trans
    (hunique (natCode (a * b)) (hvalues b le_rfl)).symm

@[simp]
theorem satisfies_natMulFormula_ambient
    (omega x y z : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
        ![omega, x, y, z] <->
      omega = Ordinal.omega0.toZFSet /\
      x ∈ omega /\ y ∈ omega /\ z ∈ omega /\
      exists ySucc, ySucc = insert y y /\
        exists graph,
          FOFormula.Satisfies Delta0Formula.ZFMem natMulGraphFormula
            ![omega, x, y, z, ySucc, graph] := by
  let s : Tuple ZFSet.{u} 4 := ![omega, x, y, z]
  have hs0 : s (0 : Fin 4) = omega := rfl
  have hs1 : s (1 : Fin 4) = x := rfl
  have hs2 : s (2 : Fin 4) = y := rfl
  have hs3 : s (3 : Fin 4) = z := rfl
  change
    (FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (Delta0Formula.ZFMem (s 1) (s 0) /\
      (Delta0Formula.ZFMem (s 2) (s 0) /\
      (Delta0Formula.ZFMem (s 3) (s 0) /\
      exists ySucc,
        FOFormula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s ySucc) /\
        exists graph,
          FOFormula.Satisfies Delta0Formula.ZFMem natMulGraphFormula
            (snoc (snoc s ySucc) graph))))) <-> _
  rw [satisfies_standardOmegaAt_ambient_iff]
  simp only [hs0, hs1, hs2, hs3]
  constructor
  · rintro ⟨homega, hx, hy, hz, ySucc, hySuccFormula,
      graph, hgraphFormula⟩
    have hySucc : ySucc = insert y y := by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt] at hySuccFormula
      simpa only [snoc_last, snoc_castSucc, hs2] using hySuccFormula
    have hassign : snoc (snoc s ySucc) graph =
        ![omega, x, y, z, ySucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at hgraphFormula
    exact ⟨homega, hx, hy, hz, ySucc, hySucc, graph, hgraphFormula⟩
  · rintro ⟨homega, hx, hy, hz, ySucc, hySucc, graph, hgraph⟩
    refine ⟨homega, hx, hy, hz, ySucc, ?_, graph, ?_⟩
    · rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simpa only [snoc_last, snoc_castSucc, hs2] using hySucc
    · have hassign : snoc (snoc s ySucc) graph =
          ![omega, x, y, z, ySucc, graph] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign]
      exact hgraph

@[simp]
theorem satisfies_natMulFormula_natCode_iff
    (a b : Nat) (z : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] <->
      z = natCode (a * b) := by
  rw [satisfies_natMulFormula_ambient]
  constructor
  · rintro ⟨_homega, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySucc, graph, hgraph⟩
    apply natMulGraphFormula_output_unique a b z ySucc graph
    · exact hySucc.trans (natCode_succ_eq_insert b).symm
    · exact hgraph
  · intro hz
    subst z
    refine ⟨rfl,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode a)).mpr ⟨a, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a * b))).mpr ⟨a * b, rfl⟩,
      natCode (b + 1), natCode_succ_eq_insert b,
      natMulCanonicalGraph a b, natMulCanonicalGraph_satisfies a b⟩

/-! ## Exact restricted semantics -/

theorem satisfiesIn_natMulFormula_natCode_iff
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (a b : Nat) {z : ZFSet.{u}} (hzM : z ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natMulFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] <->
      z = natCode (a * b) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let s : Tuple ZFSet.{u} 4 := ![omega, natCode a, natCode b, z]
  have homegaM : omega ∈ M :=
    Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have haM : (natCode a : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM a
  have hbM : (natCode b : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM b
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact haM
    · exact hbM
    · exact hzM
  have haOmega : (natCode a : ZFSet.{u}) ∈ omega :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode a)).mpr ⟨a, rfl⟩
  change
    ((Model.SatisfiesIn (M : Set ZFSet.{u})
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (natCode a : ZFSet.{u}) ∈ omega /\
      (natCode b : ZFSet.{u}) ∈ omega /\
      z ∈ omega /\
      exists ySucc, ySucc ∈ M /\
        Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s ySucc) /\
        exists graph, graph ∈ M /\
          Model.SatisfiesIn (M : Set ZFSet.{u}) natMulGraphFormula
            (snoc (snoc s ySucc) graph)) <-> _)
  constructor
  · rintro ⟨homegaFormula, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySuccM, hySuccFormula, graph, hgraphM, hgraphFormula⟩
    have homega : s (0 : Fin 4) = Ordinal.omega0.toZFSet :=
      (Model.satisfiesIn_standardOmegaAt_iff hM
        (0 : Fin 4) s hsM).mp homegaFormula
    have hsuccAssignM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc s ySucc) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsM, hySuccM⟩
    have hySuccAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s ySucc) hsuccAssignM).mp hySuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hySuccAmbient
    have hsuccAssign : snoc s ySucc =
        ![omega, natCode a, natCode b, z, ySucc] := by
      funext i
      fin_cases i <;> rfl
    rw [hsuccAssign] at hySuccAmbient
    have hySucc : ySucc = natCode (b + 1) := by
      have hraw : ySucc = insert (natCode b) (natCode b) := by
        exact hySuccAmbient
      exact hraw.trans (natCode_succ_eq_insert b).symm
    have hgraphAssign : snoc (snoc s ySucc) graph =
        ![omega, natCode a, natCode b, z, ySucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hgraphAssign] at hgraphFormula
    have hgraphAmbient :=
      (satisfiesIn_natMulGraphFormula_iff_ambient hM
        omega (natCode a) (natCode b) z ySucc graph
        homegaM haM hbM hzM hySuccM hgraphM
        rfl haOmega).mp hgraphFormula
    exact natMulGraphFormula_output_unique
      a b z ySucc graph hySucc hgraphAmbient
  · intro hz
    have hzEq : z = (natCode (a * b) : ZFSet.{u}) := hz
    have hySuccM : (natCode (b + 1) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (b + 1)
    have hgraphM : natMulCanonicalGraph a b ∈ M :=
      natMulCanonicalGraph_mem_of_isTransitiveZFModel hM a b
    refine ⟨(Model.satisfiesIn_standardOmegaAt_iff hM
      (0 : Fin 4) s hsM).mpr rfl,
      haOmega,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩, ?_,
      natCode (b + 1), hySuccM, ?_,
      natMulCanonicalGraph a b, hgraphM, ?_⟩
    · rw [hzEq]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a * b))).mpr ⟨a * b, rfl⟩
    · have hsuccAssignM : Model.TupleIn (M : Set ZFSet.{u})
          (snoc s (natCode (b + 1))) :=
        Model.tupleIn_snoc_iff.mpr ⟨hsM, hySuccM⟩
      have hsuccAssign : snoc s (natCode (b + 1)) =
          ![omega, natCode a, natCode b, z, natCode (b + 1)] := by
        funext i
        fin_cases i <;> rfl
      apply (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s (natCode (b + 1))) hsuccAssignM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      rw [hsuccAssign]
      exact natCode_succ_eq_insert b
    · have hgraphAssign :
          snoc (snoc s (natCode (b + 1)))
              (natMulCanonicalGraph a b) =
            ![omega, natCode a, natCode b, z,
              natCode (b + 1), natMulCanonicalGraph a b] := by
        funext i
        fin_cases i <;> rfl
      rw [hgraphAssign, hzEq]
      exact natMulCanonicalGraph_satisfiesIn hM a b

/-! ## Standard function-absoluteness packaging -/

/-- Total ambient multiplication on arbitrary set codes.  Invalid inputs are
sent to the empty set; the graph formula itself is restricted to standard
natural-number codes. -/
noncomputable def natMulCodeZF (x y : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode x, textbookNatDecode y with
  | some a, some b => natCode (a * b)
  | _, _ => ∅

@[simp]
theorem natMulCodeZF_natCode (a b : Nat) :
    natMulCodeZF (natCode a : ZFSet.{u}) (natCode b) =
      natCode (a * b) := by
  simp [natMulCodeZF]







end TextbookNatFormula

end Constructible

end
end GCHSource_Work_CUGCH_TextbookNaturalMultiplication


