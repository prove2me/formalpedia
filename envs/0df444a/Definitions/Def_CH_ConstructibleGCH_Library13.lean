-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library13
-- name    : CH_ConstructibleGCH_Library13
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:40:37.674389+00:00
-- url     : https://prove2.me/theorems/e4209080-cbc8-4ffe-b95b-71af2acb4741
-- title:
--   Powers and prime-power formula codes
-- statement:
--   Finite exponentiation and prime-power codes represent the finite data used by the textbook E recursion. This library provides their formula and decoding interfaces.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookNaturalPower.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookECodeFormula.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library12
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookNaturalPower -/
section GCHSource_Work_CUGCH_TextbookNaturalPower
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# The set-theoretic graph of exponentiation on the standard natural numbers

Exponentiation is defined in the pure membership language by finite recursion
from the already constructed multiplication graph.  With free-variable layout
`[omega, base, exponent, output]`, the formula asserts the existence of a
finite function `f : exponent + 1 -> omega` such that `f(0) = 1`,
`f(exponent) = output`, and `f(k + 1) = f(k) * base` for every
`k in exponent`.

The object-language formula contains only membership and equality.  Lean's
`Nat.pow` occurs only in canonical witnesses and in metatheoretic statements
of the exact semantics.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookNatFormula

 theorem satisfiesIn_boundedEx_iff_TextbookNaturalPower_gch
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedEx set formula) s <->
      exists value : ZFSet.{u}, value ∈ M /\ value ∈ s set /\
        Model.SatisfiesIn M formula (snoc s value) := by
  simp [FOFormula.boundedEx]

 theorem satisfiesIn_boundedAll_iff_TextbookNaturalPower_gch
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall value : ZFSet.{u}, value ∈ M -> value ∈ s set ->
        Model.SatisfiesIn M formula (snoc s value) := by
  classical
  simp only [FOFormula.boundedAll, Model.SatisfiesIn,
    satisfiesIn_boundedEx_iff_TextbookNaturalPower_gch]
  constructor
  · intro h value hvalueM hvalueSet
    by_contra hformula
    exact h ⟨value, hvalueM, hvalueSet, hformula⟩
  · intro h hex
    rcases hex with ⟨value, hvalueM, hvalueSet, hformula⟩
    exact hformula (h value hvalueM hvalueSet)

 theorem satisfiesIn_rename_iff_TextbookNaturalPower_gch
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

/-- Coordinate renaming for the multiplication step. -/
def natPowMulRenameAt {n : Nat} (omega base : Fin n) :
    Fin 4 -> Fin (n + 4) :=
  ![omega.castSucc.castSucc.castSucc.castSucc,
    (Fin.last (n + 2)).castSucc,
    base.castSucc.castSucc.castSucc.castSucc,
    Fin.last (n + 3)]

theorem comp_natPowMulRenameAt {A : Type u} {n : Nat}
    (s : Tuple A n) (omega base : Fin n)
    (k kSucc value nextValue : A) :
    (fun i =>
      snoc (snoc (snoc (snoc s k) kSucc) value) nextValue
        (natPowMulRenameAt omega base i)) =
      ![s omega, value, s base, nextValue] := by
  funext i
  fin_cases i <;> simp [natPowMulRenameAt]

/-- The recursive multiplication transition in an arbitrary context. -/
def natPowTransitionAt {n : Nat}
    (omega base exponent exponentSucc graph : Fin n) : FOFormula n :=
  FOFormula.boundedAll exponent
    (FOFormula.boundedEx exponentSucc.castSucc
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
                (FOFormula.rename (natPowMulRenameAt omega base)
                  natMulFormula)))))))

/-- Fixed layout `[omega, base, exponent, output, exponentSucc, graph]`. -/
def natPowTransition : FOFormula 6 :=
  natPowTransitionAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/--
The bounded graph shape.  It asserts that the graph is a function from
`exponentSucc` to `omega`, sends the standard literal zero to the standard
literal one, and sends `exponent` to `output`.
-/
def natPowGraphShapeDeltaAt {n : Nat}
    (omega exponent output exponentSucc graph : Fin n) : Delta0Formula n :=
  .conj
    (TextbookDefFormula.isFunctionDeltaAt graph exponentSucc omega)
    (.conj
      (Delta0Formula.boundedEx exponentSucc
        (.conj
          (Delta0Formula.natLiteralDeltaAt 0 (Fin.last n))
          (Delta0Formula.boundedEx omega.castSucc
            (.conj
              (Delta0Formula.natLiteralDeltaAt 1 (Fin.last (n + 1)))
              (TextbookDefFormula.graphValueDeltaAt
                graph.castSucc.castSucc
                (Fin.last n).castSucc
                (Fin.last (n + 1)))))))
      (TextbookDefFormula.graphValueDeltaAt graph exponent output))

/-- Fixed layout `[omega, base, exponent, output, exponentSucc, graph]`. -/
def natPowGraphShapeDelta : Delta0Formula 6 :=
  natPowGraphShapeDeltaAt
    (0 : Fin 6) (2 : Fin 6) (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/-- Complete graph condition in the fixed six-variable layout. -/
def natPowGraphFormula : FOFormula 6 :=
  .conj natPowGraphShapeDelta.toFO natPowTransition

/--
Pure membership-language formula for natural-number exponentiation.  Its
free-variable layout is `[omega, base, exponent, output]`.
-/
def natPowFormula : FOFormula 4 :=
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
              (.ex natPowGraphFormula))))))

/-! ## Safe reuse in larger variable contexts -/

/-- Coordinate map for embedding `[omega, base, exponent, output]`. -/
def natPowParametersAt {n : Nat}
    (omega base exponent output : Fin n) : Fin 4 -> Fin n :=
  ![omega, base, exponent, output]

/-- Exponentiation embedded into an arbitrary free-variable context. -/
def natPowFormulaAt {n : Nat}
    (omega base exponent output : Fin n) : FOFormula n :=
  FOFormula.rename (natPowParametersAt omega base exponent output)
    natPowFormula

theorem comp_natPowParametersAt {A : Type u} {n : Nat}
    (s : Tuple A n) (omega base exponent output : Fin n) :
    (fun i => s (natPowParametersAt omega base exponent output i)) =
      ![s omega, s base, s exponent, s output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_natPowFormulaAt {n : Nat}
    (omega base exponent output : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (natPowFormulaAt omega base exponent output) s <->
      FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
        ![s omega, s base, s exponent, s output] := by
  rw [natPowFormulaAt, FOFormula.satisfies_rename,
    comp_natPowParametersAt]

@[simp]
theorem satisfiesIn_natPowFormulaAt
    (M : Set ZFSet.{u}) {n : Nat}
    (omega base exponent output : Fin n) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M (natPowFormulaAt omega base exponent output) s <->
      Model.SatisfiesIn M natPowFormula
        ![s omega, s base, s exponent, s output] := by
  rw [natPowFormulaAt, satisfiesIn_rename_iff_TextbookNaturalPower_gch,
    comp_natPowParametersAt]

/-! ## Ambient semantics of the graph formula -/

@[simp]
theorem satisfies_natPowTransitionAt {n : Nat}
    (omega base exponent exponentSucc graph : Fin n)
    (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (natPowTransitionAt omega base exponent exponentSucc graph) s <->
      forall k, k ∈ s exponent ->
        insert k k ∈ s exponentSucc /\
        exists value, value ∈ s omega /\
          ZFSet.pair k value ∈ s graph /\
          exists nextValue, nextValue ∈ s omega /\
            ZFSet.pair (insert k k) nextValue ∈ s graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
              ![s omega, value, s base, nextValue] := by
  simp only [natPowTransitionAt, FOFormula.satisfies_boundedAll,
    FOFormula.satisfies_boundedEx, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_successorAt,
    TextbookDefFormula.satisfies_graphValueDeltaAt,
    FOFormula.satisfies_rename, snoc_last, snoc_castSucc,
    comp_natPowMulRenameAt]
  constructor
  · intro h k hk
    rcases h k hk with
      ⟨kSucc, hkSuccDomain, rfl, value, hvalueOmega,
        hvalue, nextValue, hnextOmega, hnext, hmul⟩
    exact ⟨hkSuccDomain, value, hvalueOmega, hvalue,
      nextValue, hnextOmega, hnext, hmul⟩
  · intro h k hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalue,
        nextValue, hnextOmega, hnext, hmul⟩
    exact ⟨insert k k, hkSuccDomain, rfl, value, hvalueOmega,
      hvalue, nextValue, hnextOmega, hnext, hmul⟩

@[simp]
theorem satisfies_natPowTransition
    (omega base exponent output exponentSucc graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition
        ![omega, base, exponent, output, exponentSucc, graph] <->
      forall k, k ∈ exponent ->
        insert k k ∈ exponentSucc /\
        exists value, value ∈ omega /\
          ZFSet.pair k value ∈ graph /\
          exists nextValue, nextValue ∈ omega /\
            ZFSet.pair (insert k k) nextValue ∈ graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
              ![omega, value, base, nextValue] := by
  exact satisfies_natPowTransitionAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (4 : Fin 6) (5 : Fin 6)
    ![omega, base, exponent, output, exponentSucc, graph]

@[simp]
theorem satisfies_natPowGraphShapeDeltaAt {n : Nat}
    (omega exponent output exponentSucc graph : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (natPowGraphShapeDeltaAt omega exponent output exponentSucc graph) s <->
      ZFSet.IsFunc (s exponentSucc) (s omega) (s graph) /\
      ((natCode 0 : ZFSet.{u}) ∈ s exponentSucc /\
        (natCode 1 : ZFSet.{u}) ∈ s omega /\
        ZFSet.pair (natCode 0) (natCode 1) ∈ s graph) /\
      ZFSet.pair (s exponent) (s output) ∈ s graph := by
  simp [natPowGraphShapeDeltaAt]

@[simp]
theorem satisfies_natPowGraphShapeDelta
    (omega base exponent output exponentSucc graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natPowGraphShapeDelta
        ![omega, base, exponent, output, exponentSucc, graph] <->
      ZFSet.IsFunc exponentSucc omega graph /\
      ((natCode 0 : ZFSet.{u}) ∈ exponentSucc /\
        (natCode 1 : ZFSet.{u}) ∈ omega /\
        ZFSet.pair (natCode 0) (natCode 1) ∈ graph) /\
      ZFSet.pair exponent output ∈ graph := by
  simp [natPowGraphShapeDelta]

@[simp]
theorem satisfies_natPowGraphFormula
    (omega base exponent output exponentSucc graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
        ![omega, base, exponent, output, exponentSucc, graph] <->
      ZFSet.IsFunc exponentSucc omega graph /\
      ((natCode 0 : ZFSet.{u}) ∈ exponentSucc /\
        (natCode 1 : ZFSet.{u}) ∈ omega /\
        ZFSet.pair (natCode 0) (natCode 1) ∈ graph) /\
      ZFSet.pair exponent output ∈ graph /\
      (forall k, k ∈ exponent ->
        insert k k ∈ exponentSucc /\
        exists value, value ∈ omega /\
          ZFSet.pair k value ∈ graph /\
          exists nextValue, nextValue ∈ omega /\
            ZFSet.pair (insert k k) nextValue ∈ graph /\
            FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
              ![omega, value, base, nextValue]) := by
  rw [natPowGraphFormula, FOFormula.Satisfies,
    Delta0Formula.satisfies_toFO,
    satisfies_natPowGraphShapeDelta, satisfies_natPowTransition]
  tauto

/-! ## Restricted semantics of the transition -/

theorem satisfiesIn_natPowTransition_iff_ambient
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (omega base exponent output exponentSucc graph : ZFSet.{u})
    (homegaM : omega ∈ M) (hbaseM : base ∈ M)
    (hexponentM : exponent ∈ M) (houtputM : output ∈ M)
    (hexponentSuccM : exponentSucc ∈ M) (hgraphM : graph ∈ M)
    (homega : omega = Ordinal.omega0.toZFSet)
    (hbaseOmega : base ∈ omega) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowTransition
        ![omega, base, exponent, output, exponentSucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition
        ![omega, base, exponent, output, exponentSucc, graph] := by
  subst omega
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode base).mp
      hbaseOmega with ⟨a, rfl⟩
  let s : Tuple ZFSet.{u} 6 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a,
      exponent, output, exponentSucc, graph]
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hbaseM
    · exact hexponentM
    · exact houtputM
    · exact hexponentSuccM
    · exact hgraphM
  change Model.SatisfiesIn (M : Set ZFSet.{u}) natPowTransition s <->
    FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition s
  rw [satisfies_natPowTransition]
  rw [natPowTransition, natPowTransitionAt,
    satisfiesIn_boundedAll_iff_TextbookNaturalPower_gch]
  simp only [s]
  constructor
  · intro h k hk
    have hkM : k ∈ M := hM.1.mem_trans hk hexponentM
    have hkbody := h k hkM hk
    rw [satisfiesIn_boundedEx_iff_TextbookNaturalPower_gch] at hkbody
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
    rw [satisfiesIn_boundedEx_iff_TextbookNaturalPower_gch] at hrest
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
            exponent, output, exponentSucc, graph, k, kSucc, value] := by
      funext i
      fin_cases i <;> rfl
    rw [hvalueAssign] at hvalueAmbient
    have hvalueGraph : ZFSet.pair k value ∈ graph := hvalueAmbient
    rw [satisfiesIn_boundedEx_iff_TextbookNaturalPower_gch] at hnextRest
    rcases hnextRest with
      ⟨nextValue, hnextM, hnextOmega, hnextFormula, hmulRenamed⟩
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
    have hnextGraph : ZFSet.pair kSucc nextValue ∈ graph := hnextAmbient
    rw [satisfiesIn_rename_iff_TextbookNaturalPower_gch,
      comp_natPowMulRenameAt] at hmulRenamed
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
        hvalueOmega with ⟨c, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
        hnextOmega with ⟨d, rfl⟩
    have hmulEq : (natCode d : ZFSet.{u}) = natCode (c * a) :=
      (satisfiesIn_natMulFormula_natCode_iff hM c a hnextM).mp
        hmulRenamed
    have hmulAmbient :
        FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode c,
            natCode a, natCode d] :=
      (satisfies_natMulFormula_natCode_iff c a (natCode d)).mpr hmulEq
    rw [hkSuccEq] at hkSuccDomain hnextGraph
    exact ⟨hkSuccDomain, natCode c, hvalueOmega, hvalueGraph,
      natCode d, hnextOmega, hnextGraph, hmulAmbient⟩
  · intro h k hkM hk
    rcases h k hk with
      ⟨hkSuccDomain, value, hvalueOmega, hvalueGraph,
        nextValue, hnextOmega, hnextGraph, hmulAmbient⟩
    have hkSuccM : insert k k ∈ M :=
      hM.1.mem_trans hkSuccDomain hexponentSuccM
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
                exponent, output, exponentSucc, graph,
                k, insert k k, value] := by
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
      · rw [satisfiesIn_rename_iff_TextbookNaturalPower_gch, comp_natPowMulRenameAt]
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode value).mp
            hvalueOmega with ⟨c, rfl⟩
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode nextValue).mp
            hnextOmega with ⟨d, rfl⟩
        have hmulEq : (natCode d : ZFSet.{u}) = natCode (c * a) :=
          (satisfies_natMulFormula_natCode_iff c a (natCode d)).mp
            hmulAmbient
        exact (satisfiesIn_natMulFormula_natCode_iff hM c a hnextM).mpr
          hmulEq

theorem satisfiesIn_natPowGraphFormula_iff_ambient
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (omega base exponent output exponentSucc graph : ZFSet.{u})
    (homegaM : omega ∈ M) (hbaseM : base ∈ M)
    (hexponentM : exponent ∈ M) (houtputM : output ∈ M)
    (hexponentSuccM : exponentSucc ∈ M) (hgraphM : graph ∈ M)
    (homega : omega = Ordinal.omega0.toZFSet)
    (hbaseOmega : base ∈ omega) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowGraphFormula
        ![omega, base, exponent, output, exponentSucc, graph] <->
      FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
        ![omega, base, exponent, output, exponentSucc, graph] := by
  let s : Tuple ZFSet.{u} 6 :=
    ![omega, base, exponent, output, exponentSucc, graph]
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hbaseM
    · exact hexponentM
    · exact houtputM
    · exact hexponentSuccM
    · exact hgraphM
  change
    (Model.SatisfiesIn (M : Set ZFSet.{u})
        natPowGraphShapeDelta.toFO s /\
      Model.SatisfiesIn (M : Set ZFSet.{u}) natPowTransition s) <->
    (FOFormula.Satisfies Delta0Formula.ZFMem
        natPowGraphShapeDelta.toFO s /\
      FOFormula.Satisfies Delta0Formula.ZFMem natPowTransition s)
  rw [Model.satisfiesIn_delta0_iff hM.1
    natPowGraphShapeDelta s hsM]
  have htransition := satisfiesIn_natPowTransition_iff_ambient
    hM omega base exponent output exponentSucc graph
      homegaM hbaseM hexponentM houtputM hexponentSuccM hgraphM
      homega hbaseOmega
  simpa only [s] using and_congr Iff.rfl htransition

/-! ## Canonical finite graph -/

/-- The canonical tuple `k |-> natCode (base ^ k)`. -/
noncomputable def natPowCanonicalTuple (base exponent : Nat) :
    Tuple (ZFCarrier (Ordinal.omega0.toZFSet : ZFSet.{u})) (exponent + 1) :=
  fun i =>
    ⟨natCode (base ^ i.1),
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ i.1))).mpr ⟨base ^ i.1, rfl⟩⟩

/-- Kuratowski graph of the canonical exponentiation recursion. -/
noncomputable def natPowCanonicalGraph
    (base exponent : Nat) : ZFSet.{u} :=
  textbookTupleGraph (natPowCanonicalTuple base exponent)

theorem natPowCanonicalGraph_isFunc (base exponent : Nat) :
    ZFSet.IsFunc (natCode (exponent + 1)) Ordinal.omega0.toZFSet
      (natPowCanonicalGraph base exponent) := by
  exact textbookTupleGraph_isFunc (natPowCanonicalTuple base exponent)

/-- The canonical graph belongs to every transitive ZF model. -/
theorem natPowCanonicalGraph_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (base exponent : Nat) :
    natPowCanonicalGraph base exponent ∈ M := by
  apply Model.finiteIsFunc_mem_of_isTransitiveZFModel hM
    (Model.omega_toZFSet_mem_of_isTransitiveZFModel hM)
  exact natPowCanonicalGraph_isFunc base exponent

@[simp]
theorem natPowCanonicalGraph_value
    (base exponent : Nat) (i : Fin (exponent + 1)) :
    ZFSet.pair (natCode i.1) (natCode (base ^ i.1)) ∈
      natPowCanonicalGraph base exponent := by
  exact textbookTupleGraph_value (natPowCanonicalTuple base exponent) i

theorem natPowCanonicalGraph_satisfies (base exponent : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
        natCode exponent, natCode (base ^ exponent),
        natCode (exponent + 1), natPowCanonicalGraph base exponent] := by
  rw [satisfies_natPowGraphFormula]
  refine ⟨natPowCanonicalGraph_isFunc base exponent, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode 0) (exponent + 1)).mpr
          ⟨0, Nat.zero_lt_succ exponent, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode 1)).mpr ⟨1, rfl⟩
    · simpa using
        (natPowCanonicalGraph_value base exponent
          ⟨0, Nat.zero_lt_succ exponent⟩)
  · simpa using
      (natPowCanonicalGraph_value base exponent
        ⟨exponent, Nat.lt_succ_self exponent⟩)
  · intro k hk
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt k exponent).mp hk with
      ⟨j, hj, rfl⟩
    refine ⟨?_, natCode (base ^ j), ?_, ?_,
      natCode (base ^ (j + 1)), ?_, ?_, ?_⟩
    · rw [← natCode_succ_eq_insert j]
      exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode (j + 1)) (exponent + 1)).mpr
          ⟨j + 1, Nat.succ_lt_succ hj, rfl⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ j))).mpr ⟨base ^ j, rfl⟩
    · exact natPowCanonicalGraph_value base exponent
        ⟨j, hj.trans (Nat.lt_succ_self exponent)⟩
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ (j + 1)))).mpr ⟨base ^ (j + 1), rfl⟩
    · rw [← natCode_succ_eq_insert j]
      exact natPowCanonicalGraph_value base exponent
        ⟨j + 1, Nat.succ_lt_succ hj⟩
    · apply (satisfies_natMulFormula_natCode_iff
        (base ^ j) base (natCode (base ^ (j + 1)))).mpr
      simp [pow_succ]

/-- The canonical graph also satisfies the graph formula internally. -/
theorem natPowCanonicalGraph_satisfiesIn
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (base exponent : Nat) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowGraphFormula
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
        natCode exponent, natCode (base ^ exponent),
        natCode (exponent + 1), natPowCanonicalGraph base exponent] := by
  have homegaM := Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have hbaseM := Model.natCode_mem_of_isTransitiveZFModel hM base
  have hexponentM := Model.natCode_mem_of_isTransitiveZFModel hM exponent
  have houtputM :=
    Model.natCode_mem_of_isTransitiveZFModel hM (base ^ exponent)
  have hsuccM :=
    Model.natCode_mem_of_isTransitiveZFModel hM (exponent + 1)
  have hgraphM :=
    natPowCanonicalGraph_mem_of_isTransitiveZFModel hM base exponent
  have hbaseOmega :
      (natCode base : ZFSet.{u}) ∈ Ordinal.omega0.toZFSet :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode base)).mpr ⟨base, rfl⟩
  apply (satisfiesIn_natPowGraphFormula_iff_ambient hM
    Ordinal.omega0.toZFSet (natCode base) (natCode exponent)
    (natCode (base ^ exponent)) (natCode (exponent + 1))
    (natPowCanonicalGraph base exponent)
    homegaM hbaseM hexponentM houtputM hsuccM hgraphM
    rfl hbaseOmega).mpr
  exact natPowCanonicalGraph_satisfies base exponent

/-! ## Uniqueness and exact ambient semantics -/

theorem natPowGraphFormula_output_unique
    (base exponent : Nat) (output exponentSucc graph : ZFSet.{u})
    (hexponentSucc : exponentSucc = natCode (exponent + 1))
    (hgraph :
      FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          natCode exponent, output, exponentSucc, graph]) :
    output = natCode (base ^ exponent) := by
  rw [satisfies_natPowGraphFormula] at hgraph
  rcases hgraph with ⟨hfunc, hzero, hexponentValue, hstep⟩
  have hvalues : forall j : Nat, j <= exponent ->
      ZFSet.pair (natCode j) (natCode (base ^ j)) ∈ graph := by
    intro j hj
    induction j with
    | zero =>
        simpa [natCode] using hzero.2.2
    | succ j ih =>
        have hjExponent : j < exponent := Nat.lt_of_succ_le hj
        rcases hstep (natCode j)
            ((IndexedSequenceZF.mem_natCode_iff_exists_lt
              (natCode j) exponent).mpr ⟨j, hjExponent, rfl⟩) with
          ⟨_hjSuccDomain, value, _hvalueOmega, hvalue,
            nextValue, _hnextOmega, hnext, hmul⟩
        have hjDomain : (natCode j : ZFSet.{u}) ∈ exponentSucc := by
          rw [hexponentSucc]
          exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
            (natCode j) (exponent + 1)).mpr
              ⟨j, hjExponent.trans (Nat.lt_succ_self exponent), rfl⟩
        rcases hfunc.2 (natCode j) hjDomain with
          ⟨graphValue, _hgraphValue, hunique⟩
        have hprevious := ih (Nat.le_of_lt hjExponent)
        have hvalueEq : value = natCode (base ^ j) :=
          (hunique value hvalue).trans
            (hunique (natCode (base ^ j)) hprevious).symm
        have hnextValueEq : nextValue = natCode (base ^ (j + 1)) := by
          rw [hvalueEq] at hmul
          have hmulEq :=
            (satisfies_natMulFormula_natCode_iff
              (base ^ j) base nextValue).mp hmul
          simpa [pow_succ] using hmulEq
        rw [← natCode_succ_eq_insert j, hnextValueEq] at hnext
        simpa using hnext
  have hexponentDomain : (natCode exponent : ZFSet.{u}) ∈ exponentSucc := by
    rw [hexponentSucc]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode exponent) (exponent + 1)).mpr
        ⟨exponent, Nat.lt_succ_self exponent, rfl⟩
  rcases hfunc.2 (natCode exponent) hexponentDomain with
    ⟨graphValue, _hgraphValue, hunique⟩
  exact (hunique output hexponentValue).trans
    (hunique (natCode (base ^ exponent))
      (hvalues exponent le_rfl)).symm

@[simp]
theorem satisfies_natPowFormula_ambient
    (omega base exponent output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
        ![omega, base, exponent, output] <->
      omega = Ordinal.omega0.toZFSet /\
      base ∈ omega /\ exponent ∈ omega /\ output ∈ omega /\
      exists exponentSucc, exponentSucc = insert exponent exponent /\
        exists graph,
          FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
            ![omega, base, exponent, output, exponentSucc, graph] := by
  let s : Tuple ZFSet.{u} 4 := ![omega, base, exponent, output]
  have hs0 : s (0 : Fin 4) = omega := rfl
  have hs1 : s (1 : Fin 4) = base := rfl
  have hs2 : s (2 : Fin 4) = exponent := rfl
  have hs3 : s (3 : Fin 4) = output := rfl
  change
    (FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      (Delta0Formula.ZFMem (s 1) (s 0) /\
      (Delta0Formula.ZFMem (s 2) (s 0) /\
      (Delta0Formula.ZFMem (s 3) (s 0) /\
      exists exponentSucc,
        FOFormula.Satisfies Delta0Formula.ZFMem
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s exponentSucc) /\
        exists graph,
          FOFormula.Satisfies Delta0Formula.ZFMem natPowGraphFormula
            (snoc (snoc s exponentSucc) graph))))) <-> _
  rw [satisfies_standardOmegaAt_ambient_iff]
  simp only [hs0, hs1, hs2, hs3]
  constructor
  · rintro ⟨homega, hbase, hexponent, houtput, exponentSucc,
      hsuccFormula, graph, hgraphFormula⟩
    have hsucc : exponentSucc = insert exponent exponent := by
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt] at hsuccFormula
      simpa only [snoc_last, snoc_castSucc, hs2] using hsuccFormula
    have hassign : snoc (snoc s exponentSucc) graph =
        ![omega, base, exponent, output, exponentSucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign] at hgraphFormula
    exact ⟨homega, hbase, hexponent, houtput,
      exponentSucc, hsucc, graph, hgraphFormula⟩
  · rintro ⟨homega, hbase, hexponent, houtput,
      exponentSucc, hsucc, graph, hgraph⟩
    refine ⟨homega, hbase, hexponent, houtput, exponentSucc, ?_, graph, ?_⟩
    · rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simpa only [snoc_last, snoc_castSucc, hs2] using hsucc
    · have hassign : snoc (snoc s exponentSucc) graph =
          ![omega, base, exponent, output, exponentSucc, graph] := by
        funext i
        fin_cases i <;> rfl
      rw [hassign]
      exact hgraph

@[simp]
theorem satisfies_natPowFormula_natCode_iff
    (base exponent : Nat) (output : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          natCode exponent, output] <->
      output = natCode (base ^ exponent) := by
  rw [satisfies_natPowFormula_ambient]
  constructor
  · rintro ⟨_homega, _hbaseOmega, _hexponentOmega, _houtputOmega,
      exponentSucc, hsucc, graph, hgraph⟩
    apply natPowGraphFormula_output_unique
      base exponent output exponentSucc graph
    · exact hsucc.trans (natCode_succ_eq_insert exponent).symm
    · exact hgraph
  · intro houtput
    subst output
    refine ⟨rfl,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode base)).mpr ⟨base, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode exponent)).mpr ⟨exponent, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ exponent))).mpr ⟨base ^ exponent, rfl⟩,
      natCode (exponent + 1), natCode_succ_eq_insert exponent,
      natPowCanonicalGraph base exponent,
      natPowCanonicalGraph_satisfies base exponent⟩

/-! ## Exact restricted semantics -/

theorem satisfiesIn_natPowFormula_natCode_iff
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (base exponent : Nat) {output : ZFSet.{u}} (houtputM : output ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natPowFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode base,
          natCode exponent, output] <->
      output = natCode (base ^ exponent) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let s : Tuple ZFSet.{u} 4 :=
    ![omega, natCode base, natCode exponent, output]
  have hsExponent : s (2 : Fin 4) = natCode exponent := rfl
  have homegaM : omega ∈ M :=
    Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have hbaseM : (natCode base : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM base
  have hexponentM : (natCode exponent : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM exponent
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro i
    fin_cases i
    · exact homegaM
    · exact hbaseM
    · exact hexponentM
    · exact houtputM
  have hbaseOmega : (natCode base : ZFSet.{u}) ∈ omega :=
    (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode base)).mpr ⟨base, rfl⟩
  change
    ((Model.SatisfiesIn (M : Set ZFSet.{u})
        (Model.standardOmegaAt (0 : Fin 4)) s /\
      ((natCode base : ZFSet.{u}) ∈ omega /\
      ((natCode exponent : ZFSet.{u}) ∈ omega /\
      (output ∈ omega /\
      exists exponentSucc, exponentSucc ∈ M /\
        (Model.SatisfiesIn (M : Set ZFSet.{u})
          (Delta0Formula.successorAt
            (Fin.last 4) (2 : Fin 4).castSucc).toFO
          (snoc s exponentSucc) /\
        exists graph, graph ∈ M /\
          Model.SatisfiesIn (M : Set ZFSet.{u}) natPowGraphFormula
            (snoc (snoc s exponentSucc) graph)))))) <-> _)
  constructor
  · rintro ⟨omegaFormula, _hbaseOmega, _hexponentOmega, _houtputOmega,
      exponentSucc, hexponentSuccM, hsuccFormula,
      graph, hgraphM, hgraphFormula⟩
    have homega : s (0 : Fin 4) = Ordinal.omega0.toZFSet :=
      (Model.satisfiesIn_standardOmegaAt_iff hM
        (0 : Fin 4) s hsM).mp omegaFormula
    have hsuccAssignM : Model.TupleIn (M : Set ZFSet.{u})
        (snoc s exponentSucc) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsM, hexponentSuccM⟩
    have hsuccAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s exponentSucc) hsuccAssignM).mp hsuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hsuccAmbient
    have hexponentSucc : exponentSucc = natCode (exponent + 1) := by
      have hraw :
          exponentSucc = insert (natCode exponent) (natCode exponent) := by
        simpa only [snoc_last, snoc_castSucc, hsExponent] using
          hsuccAmbient
      exact hraw.trans (natCode_succ_eq_insert exponent).symm
    have hgraphAssign : snoc (snoc s exponentSucc) graph =
        ![omega, natCode base, natCode exponent,
          output, exponentSucc, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hgraphAssign] at hgraphFormula
    have hgraphAmbient :=
      (satisfiesIn_natPowGraphFormula_iff_ambient hM
        omega (natCode base) (natCode exponent) output
        exponentSucc graph homegaM hbaseM hexponentM houtputM
        hexponentSuccM hgraphM rfl
        hbaseOmega).mp hgraphFormula
    exact natPowGraphFormula_output_unique
      base exponent output exponentSucc graph
      hexponentSucc hgraphAmbient
  · intro houtput
    have houtputEq : output = (natCode (base ^ exponent) : ZFSet.{u}) :=
      houtput
    have hexponentSuccM : (natCode (exponent + 1) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (exponent + 1)
    have hgraphM : natPowCanonicalGraph base exponent ∈ M :=
      natPowCanonicalGraph_mem_of_isTransitiveZFModel
        hM base exponent
    refine ⟨(Model.satisfiesIn_standardOmegaAt_iff hM
      (0 : Fin 4) s hsM).mpr rfl,
      hbaseOmega,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode exponent)).mpr ⟨exponent, rfl⟩, ?_,
      natCode (exponent + 1), hexponentSuccM, ?_,
      natPowCanonicalGraph base exponent, hgraphM, ?_⟩
    · rw [houtputEq]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (base ^ exponent))).mpr ⟨base ^ exponent, rfl⟩
    · have hsuccAssignM : Model.TupleIn (M : Set ZFSet.{u})
          (snoc s (natCode (exponent + 1))) :=
        Model.tupleIn_snoc_iff.mpr ⟨hsM, hexponentSuccM⟩
      apply (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s (natCode (exponent + 1))) hsuccAssignM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      simpa only [snoc_last, snoc_castSucc, hsExponent] using
        (natCode_succ_eq_insert exponent)
    · have hgraphAssign :
          snoc (snoc s (natCode (exponent + 1)))
              (natPowCanonicalGraph base exponent) =
            ![omega, natCode base, natCode exponent, output,
              natCode (exponent + 1), natPowCanonicalGraph base exponent] := by
        funext i
        fin_cases i <;> rfl
      rw [hgraphAssign, houtputEq]
      exact natPowCanonicalGraph_satisfiesIn hM base exponent

/-! ## Standard function-absoluteness packaging -/

/-- Total ambient operation on arbitrary set codes.  Invalid inputs map to
the empty set; the formula's domain predicate excludes them. -/
noncomputable def natPowCodeZF (base exponent : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode base, textbookNatDecode exponent with
  | some a, some b => natCode (a ^ b)
  | _, _ => ∅

@[simp]
theorem natPowCodeZF_natCode (base exponent : Nat) :
    natPowCodeZF (natCode base : ZFSet.{u}) (natCode exponent) =
      natCode (base ^ exponent) := by
  simp [natPowCodeZF]







end TextbookNatFormula

end Constructible

end
end GCHSource_Work_CUGCH_TextbookNaturalPower


/- Source module: Solutions.Work_CUGCH_TextbookECodeFormula -/
section GCHSource_Work_CUGCH_TextbookECodeFormula
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The object-language graph of the textbook enumeration code

Wang's enumeration of the five clauses defining `E` uses the natural number

`2 ^ i * 3 ^ j * 5 ^ tag`.

This file represents that operation in the pure language of membership.  The
formula does not use Lean multiplication or exponentiation: it first defines
the literals `2`, `3`, and `5`, invokes the previously constructed
object-language exponentiation graph three times, and invokes the
object-language multiplication graph twice.  Lean arithmetic occurs only in
the metatheoretic statement of the exact semantics and in canonical witnesses.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookNatFormula

 theorem satisfiesIn_rename_iff_eCode
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

/-! ## The pure membership-language formula -/

def textbookECodeFinalFormula : FOFormula 12 :=
  .conj
    (natMulFormulaAt
      (0 : Fin 12) (8 : Fin 12) (9 : Fin 12) (11 : Fin 12))
    (natMulFormulaAt
      (0 : Fin 12) (11 : Fin 12) (10 : Fin 12) (4 : Fin 12))

def textbookECodeAfterPowFiveFormula : FOFormula 11 :=
  .ex textbookECodeFinalFormula

def textbookECodeAfterPowThreeFormula : FOFormula 10 :=
  .ex <| .conj
    (natPowFormulaAt
      (0 : Fin 11) (7 : Fin 11) (3 : Fin 11) (10 : Fin 11))
    textbookECodeAfterPowFiveFormula

def textbookECodeAfterPowTwoFormula : FOFormula 9 :=
  .ex <| .conj
    (natPowFormulaAt
      (0 : Fin 10) (6 : Fin 10) (2 : Fin 10) (9 : Fin 10))
    textbookECodeAfterPowThreeFormula

def textbookECodeAfterFiveFormula : FOFormula 8 :=
  .ex <| .conj
    (natPowFormulaAt
      (0 : Fin 9) (5 : Fin 9) (1 : Fin 9) (8 : Fin 9))
    textbookECodeAfterPowTwoFormula

def textbookECodeAfterThreeFormula : FOFormula 7 :=
  .ex <| .conj
    (Delta0Formula.natLiteralDeltaAt 5 (7 : Fin 8)).toFO
    textbookECodeAfterFiveFormula

def textbookECodeAfterTwoFormula : FOFormula 6 :=
  .ex <| .conj
    (Delta0Formula.natLiteralDeltaAt 3 (6 : Fin 7)).toFO
    textbookECodeAfterThreeFormula

/--
The graph formula for the textbook constructor code.  Its free-variable layout
is `[omega, i, j, tag, m]`.

The seven existential witnesses, in order, are
`2`, `3`, `5`, `2 ^ i`, `3 ^ j`, `5 ^ tag`, and
`(2 ^ i) * (3 ^ j)`.  The final multiplication has output `m`.
-/
def textbookECodeFormula : FOFormula 5 :=
  .ex <| .conj
    (Delta0Formula.natLiteralDeltaAt 2 (5 : Fin 6)).toFO
    textbookECodeAfterTwoFormula

/-! The following coordinate lemmas make every use of a quantified witness
explicit.  In particular, no arithmetic semantic lemma is applied to a tuple
until its four designated coordinates have been checked. -/

theorem textbookECode_powTwo_assignment {A : Type u}
    (s : Tuple A 5) (two three five powTwo : A) :
    let t := snoc (snoc (snoc (snoc s two) three) five) powTwo
    ![t (0 : Fin 9), t (5 : Fin 9), t (1 : Fin 9), t (8 : Fin 9)] =
      ![s 0, two, s 1, powTwo] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]

theorem textbookECode_powThree_assignment {A : Type u}
    (s : Tuple A 5) (two three five powTwo powThree : A) :
    let t := snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree
    ![t (0 : Fin 10), t (6 : Fin 10), t (2 : Fin 10),
      t (9 : Fin 10)] = ![s 0, three, s 2, powThree] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]
  apply congrArg s
  apply Fin.ext
  rfl

theorem textbookECode_powFive_assignment {A : Type u}
    (s : Tuple A 5)
    (two three five powTwo powThree powFive : A) :
    let t := snoc (snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree)
      powFive
    ![t (0 : Fin 11), t (7 : Fin 11), t (3 : Fin 11),
      t (10 : Fin 11)] = ![s 0, five, s 3, powFive] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]
  apply congrArg s
  apply Fin.ext
  rfl

theorem textbookECode_product_assignment {A : Type u}
    (s : Tuple A 5)
    (two three five powTwo powThree powFive product : A) :
    let t := snoc (snoc (snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree)
      powFive) product
    ![t (0 : Fin 12), t (8 : Fin 12), t (9 : Fin 12),
      t (11 : Fin 12)] = ![s 0, powTwo, powThree, product] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]

theorem textbookECode_final_assignment {A : Type u}
    (s : Tuple A 5)
    (two three five powTwo powThree powFive product : A) :
    let t := snoc (snoc (snoc
      (snoc (snoc (snoc (snoc s two) three) five) powTwo) powThree)
      powFive) product
    ![t (0 : Fin 12), t (11 : Fin 12), t (10 : Fin 12),
      t (4 : Fin 12)] = ![s 0, product, powFive, s 4] := by
  simp [Model.snoc_eq_finSnoc, Fin.snoc]
  apply congrArg s
  apply Fin.ext
  rfl

/-! ## Safe reuse in larger contexts -/

/-- Coordinate map for the free layout `[omega, i, j, tag, m]`. -/
def textbookECodeParametersAt {n : Nat}
    (omega i j tag m : Fin n) : Fin 5 -> Fin n :=
  ![omega, i, j, tag, m]

/-- The textbook code formula embedded into an arbitrary context. -/
def textbookECodeFormulaAt {n : Nat}
    (omega i j tag m : Fin n) : FOFormula n :=
  FOFormula.rename (textbookECodeParametersAt omega i j tag m)
    textbookECodeFormula

theorem comp_textbookECodeParametersAt {A : Type u} {n : Nat}
    (s : Tuple A n) (omega i j tag m : Fin n) :
    (fun k => s (textbookECodeParametersAt omega i j tag m k)) =
      ![s omega, s i, s j, s tag, s m] := by
  funext k
  fin_cases k <;> rfl

@[simp]
theorem satisfies_textbookECodeFormulaAt {A : Type u}
    (membership : A -> A -> Prop) {n : Nat}
    (omega i j tag m : Fin n) (s : Tuple A n) :
    FOFormula.Satisfies membership
        (textbookECodeFormulaAt omega i j tag m) s <->
      FOFormula.Satisfies membership textbookECodeFormula
        ![s omega, s i, s j, s tag, s m] := by
  rw [textbookECodeFormulaAt, FOFormula.satisfies_rename,
    comp_textbookECodeParametersAt]

@[simp]
theorem satisfiesIn_textbookECodeFormulaAt
    (M : Set ZFSet.{u}) {n : Nat}
    (omega i j tag m : Fin n) (s : Tuple ZFSet.{u} n) :
    Model.SatisfiesIn M
        (textbookECodeFormulaAt omega i j tag m) s <->
      Model.SatisfiesIn M textbookECodeFormula
        ![s omega, s i, s j, s tag, s m] := by
  rw [textbookECodeFormulaAt, satisfiesIn_rename_iff_eCode,
    comp_textbookECodeParametersAt]

/-! ## Exact ambient semantics -/

@[simp]
theorem satisfies_textbookECodeFormula_natCode_iff
    (i j tag : Nat) (m : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem textbookECodeFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
          natCode j, natCode tag, m] <->
      m = natCode (textbookECode i j tag) := by
  rw [textbookECodeFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨two, htwoFormula, htail⟩
    have htwo : two = (natCode 2 : ZFSet.{u}) := by
      have h :=
        (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          2 (5 : Fin 6)
          (snoc ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
            natCode j, natCode tag, m] two)).mp htwoFormula
      change two = (natCode 2 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterTwoFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨three, hthreeFormula, htail⟩
    have hthree : three = (natCode 3 : ZFSet.{u}) := by
      have h :=
        (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          3 (6 : Fin 7)
          (snoc (snoc
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
              natCode j, natCode tag, m] two) three)).mp hthreeFormula
      change three = (natCode 3 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterThreeFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨five, hfiveFormula, htail⟩
    have hfive : five = (natCode 5 : ZFSet.{u}) := by
      have h :=
        (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          5 (7 : Fin 8)
          (snoc (snoc (snoc
            ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
              natCode j, natCode tag, m] two) three) five)).mp hfiveFormula
      change five = (natCode 5 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterFiveFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powTwo, hpowTwoFormula, htail⟩
    have hpowTwo :
        FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), two, natCode i,
            powTwo] := by
      rw [satisfies_natPowFormulaAt,
        textbookECode_powTwo_assignment] at hpowTwoFormula
      exact hpowTwoFormula
    rw [textbookECodeAfterPowTwoFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powThree, hpowThreeFormula, htail⟩
    have hpowThree :
        FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), three, natCode j,
            powThree] := by
      rw [satisfies_natPowFormulaAt,
        textbookECode_powThree_assignment] at hpowThreeFormula
      exact hpowThreeFormula
    rw [textbookECodeAfterPowThreeFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨powFive, hpowFiveFormula, htail⟩
    have hpowFive :
        FOFormula.Satisfies Delta0Formula.ZFMem natPowFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), five, natCode tag,
            powFive] := by
      rw [satisfies_natPowFormulaAt,
        textbookECode_powFive_assignment] at hpowFiveFormula
      exact hpowFiveFormula
    rw [textbookECodeAfterPowFiveFormula, FOFormula.Satisfies] at htail
    rcases htail with ⟨product, hfinalConjunction⟩
    rw [textbookECodeFinalFormula, FOFormula.Satisfies] at hfinalConjunction
    rcases hfinalConjunction with ⟨hproductFormula, hfinalFormula⟩
    have hproduct :
        FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), powTwo, powThree,
            product] := by
      rw [satisfies_natMulFormulaAt,
        textbookECode_product_assignment] at hproductFormula
      exact hproductFormula
    have hfinal :
        FOFormula.Satisfies Delta0Formula.ZFMem natMulFormula
          ![(Ordinal.omega0.toZFSet : ZFSet.{u}), product, powFive, m] := by
      rw [satisfies_natMulFormulaAt,
        textbookECode_final_assignment] at hfinalFormula
      exact hfinalFormula
    subst two
    subst three
    subst five
    have hpowTwo' : powTwo = (natCode (2 ^ i) : ZFSet.{u}) :=
      (satisfies_natPowFormula_natCode_iff 2 i powTwo).mp hpowTwo
    have hpowThree' : powThree = (natCode (3 ^ j) : ZFSet.{u}) :=
      (satisfies_natPowFormula_natCode_iff 3 j powThree).mp hpowThree
    have hpowFive' : powFive = (natCode (5 ^ tag) : ZFSet.{u}) :=
      (satisfies_natPowFormula_natCode_iff 5 tag powFive).mp hpowFive
    subst powTwo
    subst powThree
    subst powFive
    have hproduct' :
        product = (natCode ((2 ^ i) * (3 ^ j)) : ZFSet.{u}) :=
      (satisfies_natMulFormula_natCode_iff
        (2 ^ i) (3 ^ j) product).mp hproduct
    subst product
    have hm :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) :=
      (satisfies_natMulFormula_natCode_iff
        ((2 ^ i) * (3 ^ j)) (5 ^ tag) m).mp hfinal
    simpa only [textbookECode, Nat.mul_assoc] using hm
  · intro hm
    have hm' :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) := by
      simpa only [textbookECode, Nat.mul_assoc] using hm
    refine ⟨natCode 2, ?_, ?_⟩
    · apply (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
        2 (5 : Fin 6) _).mpr
      change (natCode 2 : ZFSet.{u}) = natCode 2
      rfl
    · rw [textbookECodeAfterTwoFormula, FOFormula.Satisfies]
      refine ⟨natCode 3, ?_, ?_⟩
      · apply (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
          3 (6 : Fin 7) _).mpr
        change (natCode 3 : ZFSet.{u}) = natCode 3
        rfl
      · rw [textbookECodeAfterThreeFormula, FOFormula.Satisfies]
        refine ⟨natCode 5, ?_, ?_⟩
        · apply (Delta0Formula.satisfies_natLiteralDeltaAt_toFO
            5 (7 : Fin 8) _).mpr
          change (natCode 5 : ZFSet.{u}) = natCode 5
          rfl
        · rw [textbookECodeAfterFiveFormula, FOFormula.Satisfies]
          refine ⟨natCode (2 ^ i), ?_, ?_⟩
          · rw [satisfies_natPowFormulaAt,
              textbookECode_powTwo_assignment]
            exact (satisfies_natPowFormula_natCode_iff
              2 i (natCode (2 ^ i))).mpr rfl
          · rw [textbookECodeAfterPowTwoFormula, FOFormula.Satisfies]
            refine ⟨natCode (3 ^ j), ?_, ?_⟩
            · rw [satisfies_natPowFormulaAt,
                textbookECode_powThree_assignment]
              exact (satisfies_natPowFormula_natCode_iff
                3 j (natCode (3 ^ j))).mpr rfl
            · rw [textbookECodeAfterPowThreeFormula, FOFormula.Satisfies]
              refine ⟨natCode (5 ^ tag), ?_, ?_⟩
              · rw [satisfies_natPowFormulaAt,
                  textbookECode_powFive_assignment]
                exact (satisfies_natPowFormula_natCode_iff
                  5 tag (natCode (5 ^ tag))).mpr rfl
              · rw [textbookECodeAfterPowFiveFormula,
                  FOFormula.Satisfies]
                refine ⟨natCode ((2 ^ i) * (3 ^ j)), ?_⟩
                rw [textbookECodeFinalFormula, FOFormula.Satisfies]
                constructor
                · rw [satisfies_natMulFormulaAt,
                    textbookECode_product_assignment]
                  exact (satisfies_natMulFormula_natCode_iff
                    (2 ^ i) (3 ^ j)
                    (natCode ((2 ^ i) * (3 ^ j)))).mpr rfl
                · rw [satisfies_natMulFormulaAt,
                    textbookECode_final_assignment]
                  exact (satisfies_natMulFormula_natCode_iff
                    ((2 ^ i) * (3 ^ j)) (5 ^ tag) m).mpr hm'

/-! ## Exact restricted semantics -/

theorem satisfiesIn_textbookECodeFormula_natCode_iff
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (i j tag : Nat) {m : ZFSet.{u}} (hmM : m ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) textbookECodeFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
          natCode j, natCode tag, m] <->
      m = natCode (textbookECode i j tag) := by
  let s : Tuple ZFSet.{u} 5 :=
    ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode i,
      natCode j, natCode tag, m]
  have homegaM : (Ordinal.omega0.toZFSet : ZFSet.{u}) ∈ M :=
    Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have hiM : (natCode i : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM i
  have hjM : (natCode j : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM j
  have htagM : (natCode tag : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM tag
  have hsM : Model.TupleIn (M : Set ZFSet.{u}) s := by
    intro k
    fin_cases k
    · exact homegaM
    · exact hiM
    · exact hjM
    · exact htagM
    · exact hmM
  change Model.SatisfiesIn (M : Set ZFSet.{u}) textbookECodeFormula s <-> _
  rw [textbookECodeFormula, Model.SatisfiesIn]
  constructor
  · rintro ⟨two, htwoM, htwoFormula, htail⟩
    have hsTwoM : Model.TupleIn (M : Set ZFSet.{u}) (snoc s two) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩
    have htwo : two = (natCode 2 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        2 (5 : Fin 6) (snoc s two) hsTwoM).mp htwoFormula
      change two = (natCode 2 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterTwoFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨three, hthreeM, hthreeFormula, htail⟩
    have hsThreeM :
        Model.TupleIn (M : Set ZFSet.{u})
          (snoc (snoc s two) three) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsTwoM, hthreeM⟩
    have hthree : three = (natCode 3 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        3 (6 : Fin 7) (snoc (snoc s two) three) hsThreeM).mp
          hthreeFormula
      change three = (natCode 3 : ZFSet.{u}) at h
      exact h
    rw [textbookECodeAfterThreeFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨five, hfiveM, hfiveFormula, htail⟩
    have hsFiveM :
        Model.TupleIn (M : Set ZFSet.{u})
          (snoc (snoc (snoc s two) three) five) :=
      Model.tupleIn_snoc_iff.mpr ⟨hsThreeM, hfiveM⟩
    have hfive : five = (natCode 5 : ZFSet.{u}) := by
      have h := (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        5 (7 : Fin 8) (snoc (snoc (snoc s two) three) five)
          hsFiveM).mp hfiveFormula
      change five = (natCode 5 : ZFSet.{u}) at h
      exact h
    subst two
    subst three
    subst five
    rw [textbookECodeAfterFiveFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨powTwo, hpowTwoM, hpowTwoFormula, htail⟩
    rw [satisfiesIn_natPowFormulaAt,
      textbookECode_powTwo_assignment] at hpowTwoFormula
    have hpowTwo :
        powTwo = (natCode (2 ^ i) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_natCode_iff
        hM 2 i hpowTwoM).mp hpowTwoFormula
    subst powTwo
    rw [textbookECodeAfterPowTwoFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨powThree, hpowThreeM, hpowThreeFormula, htail⟩
    rw [satisfiesIn_natPowFormulaAt,
      textbookECode_powThree_assignment] at hpowThreeFormula
    have hpowThree :
        powThree = (natCode (3 ^ j) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_natCode_iff
        hM 3 j hpowThreeM).mp hpowThreeFormula
    subst powThree
    rw [textbookECodeAfterPowThreeFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨powFive, hpowFiveM, hpowFiveFormula, htail⟩
    rw [satisfiesIn_natPowFormulaAt,
      textbookECode_powFive_assignment] at hpowFiveFormula
    have hpowFive :
        powFive = (natCode (5 ^ tag) : ZFSet.{u}) :=
      (satisfiesIn_natPowFormula_natCode_iff
        hM 5 tag hpowFiveM).mp hpowFiveFormula
    subst powFive
    rw [textbookECodeAfterPowFiveFormula, Model.SatisfiesIn] at htail
    rcases htail with ⟨product, hproductM, hfinalConjunction⟩
    rw [textbookECodeFinalFormula, Model.SatisfiesIn] at hfinalConjunction
    rcases hfinalConjunction with ⟨hproductFormula, hfinalFormula⟩
    rw [satisfiesIn_natMulFormulaAt,
      textbookECode_product_assignment] at hproductFormula
    have hproduct :
        product = (natCode ((2 ^ i) * (3 ^ j)) : ZFSet.{u}) :=
      (satisfiesIn_natMulFormula_natCode_iff
        hM (2 ^ i) (3 ^ j) hproductM).mp hproductFormula
    subst product
    rw [satisfiesIn_natMulFormulaAt,
      textbookECode_final_assignment] at hfinalFormula
    have hm :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) :=
      (satisfiesIn_natMulFormula_natCode_iff
        hM ((2 ^ i) * (3 ^ j)) (5 ^ tag) hmM).mp hfinalFormula
    simpa only [textbookECode, Nat.mul_assoc] using hm
  · intro hm
    have hm' :
        m = (natCode (((2 ^ i) * (3 ^ j)) * (5 ^ tag)) : ZFSet.{u}) := by
      simpa only [textbookECode, Nat.mul_assoc] using hm
    have htwoM : (natCode 2 : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM 2
    have hthreeM : (natCode 3 : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM 3
    have hfiveM : (natCode 5 : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM 5
    have hpowTwoM : (natCode (2 ^ i) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (2 ^ i)
    have hpowThreeM : (natCode (3 ^ j) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (3 ^ j)
    have hpowFiveM : (natCode (5 ^ tag) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (5 ^ tag)
    have hproductM :
        (natCode ((2 ^ i) * (3 ^ j)) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM
        ((2 ^ i) * (3 ^ j))
    refine ⟨natCode 2, htwoM, ?_, ?_⟩
    · apply (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
        2 (5 : Fin 6) (snoc s (natCode 2))
        (Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩)).mpr
      change (natCode 2 : ZFSet.{u}) = natCode 2
      rfl
    · rw [textbookECodeAfterTwoFormula, Model.SatisfiesIn]
      refine ⟨natCode 3, hthreeM, ?_, ?_⟩
      · apply (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
          3 (6 : Fin 7) _ ?_).mpr
        · change (natCode 3 : ZFSet.{u}) = natCode 3
          rfl
        · exact Model.tupleIn_snoc_iff.mpr
            ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩, hthreeM⟩
      · rw [textbookECodeAfterThreeFormula, Model.SatisfiesIn]
        refine ⟨natCode 5, hfiveM, ?_, ?_⟩
        · apply (Model.satisfiesIn_natLiteralDeltaAt_iff hM.1
            5 (7 : Fin 8) _ ?_).mpr
          · change (natCode 5 : ZFSet.{u}) = natCode 5
            rfl
          · exact Model.tupleIn_snoc_iff.mpr
              ⟨Model.tupleIn_snoc_iff.mpr
                ⟨Model.tupleIn_snoc_iff.mpr ⟨hsM, htwoM⟩,
                  hthreeM⟩,
                hfiveM⟩
        · rw [textbookECodeAfterFiveFormula, Model.SatisfiesIn]
          refine ⟨natCode (2 ^ i), hpowTwoM, ?_, ?_⟩
          · rw [satisfiesIn_natPowFormulaAt,
              textbookECode_powTwo_assignment]
            exact (satisfiesIn_natPowFormula_natCode_iff
              hM 2 i hpowTwoM).mpr rfl
          · rw [textbookECodeAfterPowTwoFormula, Model.SatisfiesIn]
            refine ⟨natCode (3 ^ j), hpowThreeM, ?_, ?_⟩
            · rw [satisfiesIn_natPowFormulaAt,
                textbookECode_powThree_assignment]
              exact (satisfiesIn_natPowFormula_natCode_iff
                hM 3 j hpowThreeM).mpr rfl
            · rw [textbookECodeAfterPowThreeFormula, Model.SatisfiesIn]
              refine ⟨natCode (5 ^ tag), hpowFiveM, ?_, ?_⟩
              · rw [satisfiesIn_natPowFormulaAt,
                  textbookECode_powFive_assignment]
                exact (satisfiesIn_natPowFormula_natCode_iff
                  hM 5 tag hpowFiveM).mpr rfl
              · rw [textbookECodeAfterPowFiveFormula,
                  Model.SatisfiesIn]
                refine ⟨natCode ((2 ^ i) * (3 ^ j)), hproductM, ?_⟩
                rw [textbookECodeFinalFormula, Model.SatisfiesIn]
                constructor
                · rw [satisfiesIn_natMulFormulaAt,
                    textbookECode_product_assignment]
                  exact (satisfiesIn_natMulFormula_natCode_iff
                    hM (2 ^ i) (3 ^ j) hproductM).mpr rfl
                · rw [satisfiesIn_natMulFormulaAt,
                    textbookECode_final_assignment]
                  exact (satisfiesIn_natMulFormula_natCode_iff
                    hM ((2 ^ i) * (3 ^ j)) (5 ^ tag) hmM).mpr hm'



/-! ## Total set-coded operation and function absoluteness -/

/-- Total ambient operation on arbitrary set codes.  Exactly as for the
arithmetic operations used to construct it, nonstandard inputs are sent to
the empty set; the represented domain below excludes those inputs. -/
noncomputable def textbookECodeZF
    (i j tag : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode i, textbookNatDecode j,
      textbookNatDecode tag with
  | some i, some j, some tag => natCode (textbookECode i j tag)
  | _, _, _ => ∅

@[simp]
theorem textbookECodeZF_natCode (i j tag : Nat) :
    textbookECodeZF (natCode i : ZFSet.{u}) (natCode j) (natCode tag) =
      natCode (textbookECode i j tag) := by
  simp [textbookECodeZF]







end TextbookNatFormula

end Constructible

end
end GCHSource_Work_CUGCH_TextbookECodeFormula


