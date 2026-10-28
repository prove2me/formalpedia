-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library25
-- name    : CH_ConstructibleGCH_Library25
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:41:34.938601+00:00
-- url     : https://prove2.me/theorems/a1489a15-c3f7-40e4-8cdd-a71b30964f97
-- title:
--   Exact E formulas and uniform witness requests
-- statement:
--   This library supplies exact first-order descriptions for the E operations used here, together with single-witness, uniform-request and definable-power-set injection data. These descriptions use fixed formulas with explicit parameters.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEFormulaExactLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookESingleWitnessStep.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEUniformWitnessFormula.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalDefZFInjection.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library24
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookEFormulaExactLCarrier -/
section GCHSource_Work_CUGCH_TextbookEFormulaExactLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# Exact semantics of the textbook E formula over L

The public first-order formula for the textbook enumeration is now proved
equivalent, over `LCarrier`, to the original recursively defined function.
The reverse implication uses the actual constructible local graph; the
forward implication decodes any formula witness and applies textbook local
solution agreement.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace Model

local notation "LMem" => lCarrierMem

/-- Exact semantics at externally indexed standard natural-number codes. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_natCode_iff
    (a output : LCarrier.{u}) (n m : Nat) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, TextbookNatFormula.textbookNatCodeLCarrier n,
          TextbookNatFormula.textbookNatCodeLCarrier m, output] <->
      output.1 = textbookEZF a.1 (natCode n) (natCode m) := by
  let nL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let mL : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier m
  have hkey : orderedPairLCarrier mL nL =
      textbookEKeyLCarrier m n := by
    apply Subtype.ext
    rfl
  have hkeyVal : ZFSet.pair mL.1 nL.1 =
      (textbookEKeyLCarrier m n).1 := by
    rw [← orderedPairLCarrier_val, hkey]
  have hsemantic :=
    satisfies_textbookEZFFormula_lCarrier_iff_localSolution
      a nL mL output
  change FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
      ![a, nL, mL, output] <-> _
  constructor
  · intro hformula
    rcases hsemantic.mp hformula with
      ⟨_homega, graph, hlocal, hpair⟩
    rw [hkey] at hlocal
    have hpair' :
        ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈ graph.1 := by
      simpa only [hkeyVal] using hpair
    have hvalue :=
      textbookEByKey_eq_of_satisfies_localSolution_lCarrier
        a graph output m n hlocal hpair'
    simpa only [textbookEKeyLCarrier_val, textbookEZF] using hvalue
  · intro hvalue
    have hnOmega : nL.1 ∈ textbookEOmegaZF := by
      apply (IndexedSequenceZF.mem_omega_iff_exists_natCode nL.1).mpr
      exact ⟨n, by simp only [nL,
        TextbookNatFormula.textbookNatCodeLCarrier_val]⟩
    have hmOmega : mL.1 ∈ textbookEOmegaZF := by
      apply (IndexedSequenceZF.mem_omega_iff_exists_natCode mL.1).mpr
      exact ⟨m, by simp only [mL,
        TextbookNatFormula.textbookNatCodeLCarrier_val]⟩
    let graph : LCarrier.{u} := textbookELocalGraphLCarrier a m n
    have hlocal :=
      textbookECanonicalLocalGraph_satisfies_localSolution
        a graph m n (by rfl)
    have htop : (textbookEKeyLCarrier m n).1 ∈
        (textbookELocalDomainLCarrier m n).1 := by
      change (textbookEKeyLCarrier m n).1 ∈
        localRecursionDomain TextbookEDomain TextbookERelation
          textbookERelation_hasSetPredecessorsOn
          (textbookEKeyLCarrier m n).1
      exact mem_localRecursionDomain_iff.mpr (Or.inl rfl)
    have hpair :
        ZFSet.pair (textbookEKeyLCarrier m n).1 output.1 ∈ graph.1 := by
      have hcanonical := pair_mem_predecessorRestrictionGraph
        (textbookEByKey a.1) htop
      have houtput : output.1 =
          textbookEByKey a.1 (textbookEKeyLCarrier m n).1 := by
        simpa only [textbookEKeyLCarrier_val, textbookEZF] using hvalue
      rw [← houtput] at hcanonical
      simpa only [graph, textbookELocalGraphLCarrier_val] using hcanonical
    apply hsemantic.mpr
    refine ⟨⟨hnOmega, hmOmega⟩, graph, ?_, ?_⟩
    · rw [hkey]
      exact hlocal
    · simpa only [hkeyVal] using hpair

/-- Full exact semantics for arbitrary `LCarrier` arguments.  Membership in
the standard internal omega supplies the unique external natural-number
codes used by the preceding theorem. -/
@[simp]
theorem satisfies_textbookEZFFormula_lCarrier_iff
    (a n m output : LCarrier.{u}) :
    FOFormula.Satisfies LMem TextbookEFormula.textbookEZFFormula
        ![a, n, m, output] <->
      (n.1 ∈ textbookEOmegaZF /\ m.1 ∈ textbookEOmegaZF) /\
        output.1 = textbookEZF a.1 n.1 m.1 := by
  constructor
  · intro hformula
    have homega :=
      (satisfies_textbookEZFFormula_lCarrier_iff_localSolution
        a n m output).mp hformula |>.1
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n.1).mp
        homega.1 with ⟨nCode, hnCode⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m.1).mp
        homega.2 with ⟨mCode, hmCode⟩
    have hn : n = TextbookNatFormula.textbookNatCodeLCarrier nCode :=
      Subtype.ext hnCode
    have hm : m = TextbookNatFormula.textbookNatCodeLCarrier mCode :=
      Subtype.ext hmCode
    subst n
    subst m
    have hvalue :=
      (satisfies_textbookEZFFormula_lCarrier_natCode_iff
        a output nCode mCode).mp hformula
    refine ⟨homega, ?_⟩
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using hvalue
  · rintro ⟨homega, hvalue⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode n.1).mp
        homega.1 with ⟨nCode, hnCode⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode m.1).mp
        homega.2 with ⟨mCode, hmCode⟩
    have hn : n = TextbookNatFormula.textbookNatCodeLCarrier nCode :=
      Subtype.ext hnCode
    have hm : m = TextbookNatFormula.textbookNatCodeLCarrier mCode :=
      Subtype.ext hmCode
    subst n
    subst m
    apply (satisfies_textbookEZFFormula_lCarrier_natCode_iff
      a output nCode mCode).mpr
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using hvalue

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEFormulaExactLCarrier


/- Source module: Solutions.Work_CUGCH_TextbookESingleWitnessStep -/
section GCHSource_Work_CUGCH_TextbookESingleWitnessStep
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# One internal witness step for a decoded textbook E task

For a decoded task `(n,m)`, `textbookEZFLCarrier U (n+1) m` is now an actual
member of `L`.  This file constructs the corresponding one-task witness step.
Its parameter prefixes are the textbook finite function graphs in `seed^n`.
A candidate `y` extends a prefix graph `p` by the pair `<n,y>`, exactly as in
the projection clause defining `E`.

One fixed first-order formula separates from `U` the canonical least witness
for every nonempty prefix fiber.  Thus both the selected witness set and the
step adjoining it to the seed are actual `LCarrier`s.  This remains a
single decoded task.  No uniform graph in the task variable and no omega
iteration are asserted here.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## The textbook tuple-extension predicate -/

/-- Layout `[relation,prefix,arity,value]`: extending `prefix` by
`<arity,value>` is a member of `relation`. -/
def textbookETupleExtensionFormula : FOFormula 4 :=
  .ex
    (.conj
      (.mem (Fin.last 4) (0 : Fin 4).castSucc)
      (TextbookDefFormula.insertPairEqDeltaAt
        (Fin.last 4)
        (1 : Fin 4).castSucc
        (2 : Fin 4).castSucc
        (3 : Fin 4).castSucc).toFO)

@[simp]
theorem satisfies_textbookETupleExtensionFormula
    (relation prefixGraph arity value : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookETupleExtensionFormula
        ![relation, prefixGraph, arity, value] ↔
      insert (ZFSet.pair arity.1 value.1) prefixGraph.1 ∈ relation.1 := by
  rw [textbookETupleExtensionFormula, FOFormula.Satisfies]
  constructor
  · rintro ⟨extended, hextended, heqFormula⟩
    have heq : extended.1 =
        insert (ZFSet.pair arity.1 value.1) prefixGraph.1 := by
      apply (TextbookDefFormula.satisfies_insertPairEqDeltaAt
        (Fin.last 4)
        (1 : Fin 4).castSucc
        (2 : Fin 4).castSucc
        (3 : Fin 4).castSucc
        ![relation.1, prefixGraph.1, arity.1, value.1, extended.1]).mp
      apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
        (TextbookDefFormula.insertPairEqDeltaAt
          (Fin.last 4)
          (1 : Fin 4).castSucc
          (2 : Fin 4).castSucc
          (3 : Fin 4).castSucc)
        ![relation, prefixGraph, arity, value, extended]).mp
      exact heqFormula
    rwa [← heq]
  · intro hextended
    let extended : LCarrier.{u} :=
      ⟨insert (ZFSet.pair arity.1 value.1) prefixGraph.1,
        mem_L_of_mem hextended relation.2⟩
    refine ⟨extended, hextended, ?_⟩
    apply (Delta0Formula.satisfies_toFO_lCarrier_absolute
      (TextbookDefFormula.insertPairEqDeltaAt
        (Fin.last 4)
        (1 : Fin 4).castSucc
        (2 : Fin 4).castSucc
        (3 : Fin 4).castSucc)
      ![relation, prefixGraph, arity, value, extended]).mpr
    apply (TextbookDefFormula.satisfies_insertPairEqDeltaAt
      (Fin.last 4)
      (1 : Fin 4).castSucc
      (2 : Fin 4).castSucc
      (3 : Fin 4).castSucc
      ![relation.1, prefixGraph.1, arity.1, value.1, extended.1]).mpr
    rfl

/-- The extension predicate placed at arbitrary coordinates. -/
def textbookETupleExtensionAt {n : Nat}
    (relation prefixGraph arity value : Fin n) : FOFormula n :=
  FOFormula.rename ![relation, prefixGraph, arity, value]
    textbookETupleExtensionFormula

@[simp]
theorem satisfies_textbookETupleExtensionAt {n : Nat}
    (relation prefixGraph arity value : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (textbookETupleExtensionAt relation prefixGraph arity value) s ↔
      insert (ZFSet.pair (s arity).1 (s value).1) (s prefixGraph).1 ∈
        (s relation).1 := by
  rw [textbookETupleExtensionAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![relation, prefixGraph, arity, value] i)) =
        ![s relation, s prefixGraph, s arity, s value] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, satisfies_textbookETupleExtensionFormula]

/-! ## One internally represented candidate fiber -/

/-- Candidates in `U` for one represented relation and one textbook prefix. -/
def textbookEWitnessCandidates
    (U relation prefixGraph arity : LCarrier.{u}) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    textbookETupleExtensionFormula ![relation, prefixGraph, arity] U)

@[simp]
theorem mem_textbookEWitnessCandidates_iff
    (U relation prefixGraph arity y : LCarrier.{u}) :
    y.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 ↔
      y.1 ∈ U.1 ∧
        insert (ZFSet.pair arity.1 y.1) prefixGraph.1 ∈ relation.1 := by
  rw [textbookEWitnessCandidates]
  rw [Classical.choose_spec (exists_separationLCarrier
    textbookETupleExtensionFormula ![relation, prefixGraph, arity] U) y]
  rw [show snoc ![relation, prefixGraph, arity] y =
      ![relation, prefixGraph, arity, y] by
    funext i
    fin_cases i <;> rfl]
  rw [satisfies_textbookETupleExtensionFormula]

theorem textbookEWitnessCandidates_subset
    (U relation prefixGraph arity : LCarrier.{u}) :
    (textbookEWitnessCandidates U relation prefixGraph arity).1 ⊆ U.1 := by
  intro y hy
  let yL : LCarrier.{u} :=
      ⟨y, mem_L_of_mem hy
      (textbookEWitnessCandidates U relation prefixGraph arity).2⟩
  exact (mem_textbookEWitnessCandidates_iff
    U relation prefixGraph arity yL).mp hy |>.1

/-- A nonempty textbook E fiber has a unique least candidate in the
canonical internal stage order. -/
theorem existsUnique_textbookEWitnessMinimum
    (U relation prefixGraph arity : LCarrier.{u})
    (hnonempty : ∃ y : LCarrier.{u},
      y.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1) :
    ∃! y : LCarrier.{u},
      y.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 ∧
        ∀ z : LCarrier.{u},
          z.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 →
            ¬ GraphRel (canonicalWitnessOrder U) z y := by
  have hsub : ∀ z : LCarrier.{u},
      z.1 ∈ (textbookEWitnessCandidates U relation prefixGraph arity).1 →
        z.1 ∈ (canonicalWitnessStage U).1 := by
    intro z hz
    exact seed_subset_canonicalWitnessStage U
      (textbookEWitnessCandidates_subset U relation prefixGraph arity hz)
  rcases exists_unique_graph_minimum
      (canonicalWitnessOrder_internallyWellOrders U) hsub hnonempty with
    ⟨y, hy, hunique⟩
  exact ⟨y, hy, fun y' hy' => hunique y' hy'⟩

/-! ## Simultaneous selection over all seed prefixes for one task -/

/-- The internally represented family of textbook prefix graphs `seed^n`. -/
def textbookEWitnessPrefixFamily
    (seed : LCarrier.{u}) (arity : Nat) : LCarrier.{u} :=
  ⟨textbookTupleSpace seed.1 arity,
    textbookTupleSpace_mem_L seed.2 arity⟩

@[simp]
theorem textbookEWitnessPrefixFamily_val
    (seed : LCarrier.{u}) (arity : Nat) :
    (textbookEWitnessPrefixFamily seed arity).1 =
      textbookTupleSpace seed.1 arity :=
  rfl

/-- Layout `[U,relation,prefixes,order,arity,y]`.  Some prefix in the
internal family has `y` as its canonical least E-witness. -/
def textbookEWitnessSelectionFormula : FOFormula 6 :=
  .ex
    (.conj
      (.mem (Fin.last 6) (2 : Fin 6).castSucc)
      (.conj
        (textbookETupleExtensionAt
          (1 : Fin 6).castSucc
          (Fin.last 6)
          (4 : Fin 6).castSucc
          (5 : Fin 6).castSucc)
        (.all
          (FOFormula.imp
            (.conj
              (.mem (Fin.last 7) (0 : Fin 7).castSucc)
              (textbookETupleExtensionAt
                (1 : Fin 7).castSucc
                (Fin.last 6).castSucc
                (4 : Fin 7).castSucc
                (Fin.last 7)))
            (.neg
              (graphRelAt
                (3 : Fin 7).castSucc
                (Fin.last 7)
                (5 : Fin 7).castSucc))))))

@[simp]
theorem satisfies_textbookEWitnessSelectionFormula
    (U relation prefixes order arity y : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEWitnessSelectionFormula
        ![U, relation, prefixes, order, arity, y] ↔
      ∃ prefixGraph : LCarrier.{u}, prefixGraph.1 ∈ prefixes.1 ∧
        insert (ZFSet.pair arity.1 y.1) prefixGraph.1 ∈ relation.1 ∧
          ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
            insert (ZFSet.pair arity.1 z.1) prefixGraph.1 ∈ relation.1 →
              ¬ GraphRel order z y := by
  simp only [textbookEWitnessSelectionFormula, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_textbookETupleExtensionAt, satisfies_graphRelAt,
    snoc_last, snoc_castSucc]
  apply exists_congr
  intro prefixGraph
  apply and_congr_right
  intro _hprefix
  apply and_congr_right
  intro _hy
  constructor
  · intro hminimal z hzU hzRelation
    exact hminimal z ⟨hzU, hzRelation⟩
  · intro hminimal z
    rintro ⟨hzU, hzRelation⟩
    exact hminimal z hzU hzRelation

/-- The canonical witnesses for every nonempty prefix fiber of one decoded
`E` task, constructed by Separation from `U`. -/
def textbookECanonicalWitnessSelection
    (seed U : LCarrier.{u}) (arity code : Nat) : LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    textbookEWitnessSelectionFormula
    ![U, textbookEZFLCarrier U (arity + 1) code,
      textbookEWitnessPrefixFamily seed arity,
      canonicalWitnessOrder U,
      ⟨natCode arity, natCode_mem_L arity⟩]
    U)

@[simp]
theorem mem_textbookECanonicalWitnessSelection_iff
    (seed U : LCarrier.{u}) (arity code : Nat) (y : LCarrier.{u}) :
    y.1 ∈ (textbookECanonicalWitnessSelection seed U arity code).1 ↔
      y.1 ∈ U.1 ∧
        ∃ prefixGraph : LCarrier.{u},
          prefixGraph.1 ∈ (textbookEWitnessPrefixFamily seed arity).1 ∧
            insert (ZFSet.pair (natCode arity) y.1) prefixGraph.1 ∈
                (textbookEZFLCarrier U (arity + 1) code).1 ∧
              ∀ z : LCarrier.{u}, z.1 ∈ U.1 →
                insert (ZFSet.pair (natCode arity) z.1) prefixGraph.1 ∈
                    (textbookEZFLCarrier U (arity + 1) code).1 →
                  ¬ GraphRel (canonicalWitnessOrder U) z y := by
  rw [textbookECanonicalWitnessSelection]
  rw [Classical.choose_spec (exists_separationLCarrier
    textbookEWitnessSelectionFormula
    ![U, textbookEZFLCarrier U (arity + 1) code,
      textbookEWitnessPrefixFamily seed arity,
      canonicalWitnessOrder U,
      ⟨natCode arity, natCode_mem_L arity⟩]
    U) y]
  rw [show snoc
      ![U, textbookEZFLCarrier U (arity + 1) code,
        textbookEWitnessPrefixFamily seed arity,
        canonicalWitnessOrder U,
        ⟨natCode arity, natCode_mem_L arity⟩] y =
      ![U, textbookEZFLCarrier U (arity + 1) code,
        textbookEWitnessPrefixFamily seed arity,
        canonicalWitnessOrder U,
        ⟨natCode arity, natCode_mem_L arity⟩, y] by
    funext i
    fin_cases i <;> rfl]
  rw [satisfies_textbookEWitnessSelectionFormula]











end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookESingleWitnessStep


/- Source module: Solutions.Work_CUGCH_TextbookEUniformWitnessFormula -/
section GCHSource_Work_CUGCH_TextbookEUniformWitnessFormula
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/






/-!
# A uniform first-order selector for all textbook E witness requests

A request is the Kuratowski pair

`<<code, arity + 1>, prefixGraph>`.

The selected formula decodes this pair internally, verifies that `prefixGraph`
belongs to `seed^arity`, computes the corresponding textbook relation
`E(U, arity + 1, code)`, and selects the canonical least witness in its
fiber.  The total formula returns that witness when it exists and the empty
set otherwise.  Both are fixed first-order formulas; no external decoder or
choice function occurs in their definitions.
-/

section

open Set

universe u

namespace Constructible.Model

open FiniteSequenceZF

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Coordinate embeddings -/

/-- Put the four-place textbook E formula at arbitrary coordinates. -/
def textbookEZFFormulaAt {n : Nat}
    (ambient positiveArity code relation : Fin n) : FOFormula n :=
  FOFormula.rename ![ambient, positiveArity, code, relation]
    TextbookEFormula.textbookEZFFormula

@[simp]
theorem satisfies_textbookEZFFormulaAt_lCarrier {n : Nat}
    (ambient positiveArity code relation : Fin n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (textbookEZFFormulaAt ambient positiveArity code relation) s <->
      ((s positiveArity).1 ∈ textbookEOmegaZF /\
        (s code).1 ∈ textbookEOmegaZF) /\
        (s relation).1 =
          textbookEZF (s ambient).1 (s positiveArity).1 (s code).1 := by
  rw [textbookEZFFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![ambient, positiveArity, code, relation] i)) =
        ![s ambient, s positiveArity, s code, s relation] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign, satisfies_textbookEZFFormula_lCarrier_iff]

/-- Put the finite tuple-space formula at arbitrary coordinates. -/
def finiteTupleSpaceFormulaAt {n : Nat}
    (seed arity space : Fin n) : FOFormula n :=
  FOFormula.rename ![seed, arity, space]
    ContinuumFormula.finiteTupleSpaceFormula

theorem satisfies_finiteTupleSpaceFormulaAt_lCarrier {n : Nat}
    (seed arity space : Fin n) (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies LMem
        (finiteTupleSpaceFormulaAt seed arity space) s <->
      FOFormula.Satisfies LMem
        ContinuumFormula.finiteTupleSpaceFormula
        ![s seed, s arity, s space] := by
  rw [finiteTupleSpaceFormulaAt, FOFormula.satisfies_rename]
  have hassign :
      (fun i => s (![seed, arity, space] i)) =
        ![s seed, s arity, s space] := by
    funext i
    fin_cases i <;> rfl
  rw [hassign]

/-! ## The selected-witness formula -/

/--
The quantifier-free core of the uniform selector.

The layout is

`[U, seed, order, request, output, task, prefixGraph, code,
  positiveArity, arity, relation, space]`.
-/
def textbookEUniformSelectedBody : FOFormula 12 :=
  .conj
    (Delta0Formula.kuratowskiPairEqAt
      (3 : Fin 12) (5 : Fin 12) (6 : Fin 12)).toFO
    <| .conj
      (Delta0Formula.kuratowskiPairEqAt
        (5 : Fin 12) (7 : Fin 12) (8 : Fin 12)).toFO
    <| .conj
      (Delta0Formula.successorAt
        (8 : Fin 12) (9 : Fin 12)).toFO
    <| .conj
      (textbookEZFFormulaAt
        (0 : Fin 12) (8 : Fin 12) (7 : Fin 12) (10 : Fin 12))
    <| .conj
      (finiteTupleSpaceFormulaAt
        (1 : Fin 12) (9 : Fin 12) (11 : Fin 12))
    <| .conj
      (.mem (6 : Fin 12) (11 : Fin 12))
    <| .conj
      (.mem (4 : Fin 12) (0 : Fin 12))
    <| .conj
      (textbookETupleExtensionAt
        (10 : Fin 12) (6 : Fin 12)
        (9 : Fin 12) (4 : Fin 12))
      (.all
        (FOFormula.imp
          (.conj
            (.mem (Fin.last 12) (0 : Fin 12).castSucc)
            (textbookETupleExtensionAt
              (10 : Fin 12).castSucc
              (6 : Fin 12).castSucc
              (9 : Fin 12).castSucc
              (Fin.last 12)))
          (.neg
            (graphRelAt
              (2 : Fin 12).castSucc
              (Fin.last 12)
              (4 : Fin 12).castSucc))))

/--
Layout `[U, seed, order, request, output]`.  The seven existentially bound
coordinates are respectively `task`, `prefixGraph`, `code`, positive arity,
predecessor arity, the E relation, and `seed^arity`.
-/
def textbookEUniformSelectedFormula : FOFormula 5 :=
  .ex <| .ex <| .ex <| .ex <| .ex <| .ex <| .ex
    textbookEUniformSelectedBody

@[simp]
theorem satisfies_textbookEUniformSelectedFormula
    (U seed order request output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, order, request, output] <->
      ∃ task prefixGraph code positiveArity arity relation space : LCarrier.{u},
        request.1 = ZFSet.pair task.1 prefixGraph.1 /\
        task.1 = ZFSet.pair code.1 positiveArity.1 /\
        positiveArity.1 = insert arity.1 arity.1 /\
        ((positiveArity.1 ∈ textbookEOmegaZF /\
            code.1 ∈ textbookEOmegaZF) /\
          relation.1 =
            textbookEZF U.1 positiveArity.1 code.1) /\
        FOFormula.Satisfies LMem
          ContinuumFormula.finiteTupleSpaceFormula
          ![seed, arity, space] /\
        prefixGraph.1 ∈ space.1 /\
        output.1 ∈ U.1 /\
        insert (ZFSet.pair arity.1 output.1) prefixGraph.1 ∈ relation.1 /\
        ∀ z : LCarrier.{u}, z.1 ∈ U.1 ->
          insert (ZFSet.pair arity.1 z.1) prefixGraph.1 ∈ relation.1 ->
            ¬ GraphRel order z output := by
  simp only [textbookEUniformSelectedFormula, FOFormula.Satisfies]
  apply exists_congr
  intro task
  apply exists_congr
  intro prefixGraph
  apply exists_congr
  intro code
  apply exists_congr
  intro positiveArity
  apply exists_congr
  intro arity
  apply exists_congr
  intro relation
  apply exists_congr
  intro space
  simp only [textbookEUniformSelectedBody, FOFormula.Satisfies,
    satisfies_kuratowskiPairEqAt_lCarrier,
    satisfies_successorAt_lCarrier,
    satisfies_textbookEZFFormulaAt_lCarrier,
    satisfies_finiteTupleSpaceFormulaAt_lCarrier,
    satisfies_textbookETupleExtensionAt,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    satisfies_graphRelAt, snoc_last, snoc_castSucc]
  aesop

/-! ## Exact semantics at a decoded request -/



/--
At a decoded request, the selected formula is exactly the canonical
least-witness condition for the intended E fiber.
-/
theorem satisfies_textbookEUniformSelectedFormula_decoded_iff
    (U seed order prefixGraph output : LCarrier.{u}) (arity code : Nat) :
    FOFormula.Satisfies LMem textbookEUniformSelectedFormula
        ![U, seed, order,
          orderedPairLCarrier
            (orderedPairLCarrier
              (TextbookNatFormula.textbookNatCodeLCarrier code)
              (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)))
            prefixGraph,
          output] <->
      prefixGraph.1 ∈ textbookTupleSpace seed.1 arity /\
      output.1 ∈ U.1 /\
      insert (ZFSet.pair (natCode arity) output.1) prefixGraph.1 ∈
        textbookEZF U.1 (natCode (arity + 1)) (natCode code) /\
      ∀ z : LCarrier.{u}, z.1 ∈ U.1 ->
        insert (ZFSet.pair (natCode arity) z.1) prefixGraph.1 ∈
          textbookEZF U.1 (natCode (arity + 1)) (natCode code) ->
            ¬ GraphRel order z output := by
  rw [satisfies_textbookEUniformSelectedFormula]
  constructor
  · rintro ⟨task, prefixGraph', code', positiveArity, arity', relation, space,
      hrequest, htask, hsuccessor, hrelation, hspace, hprefix,
      houtput, hextension, hminimal⟩
    have hrequestRaw :
        (orderedPairLCarrier
          (orderedPairLCarrier
            (TextbookNatFormula.textbookNatCodeLCarrier code)
            (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)))
          prefixGraph).1 =
          ZFSet.pair
            (ZFSet.pair (natCode code) (natCode (arity + 1)))
            prefixGraph.1 := by
      rfl
    have houter := ZFSet.pair_inj.mp (hrequest.symm.trans hrequestRaw)
    have hprefixEq : prefixGraph' = prefixGraph := by
      exact Subtype.ext houter.2
    subst prefixGraph'
    have hinner :
        ZFSet.pair code'.1 positiveArity.1 =
          ZFSet.pair (natCode code) (natCode (arity + 1)) := by
      exact htask.symm.trans houter.1
    have hcoordinates := ZFSet.pair_inj.mp hinner
    have hcodeEq :
        code' = TextbookNatFormula.textbookNatCodeLCarrier code := by
      exact Subtype.ext hcoordinates.1
    have hpositiveEq :
        positiveArity =
          TextbookNatFormula.textbookNatCodeLCarrier (arity + 1) := by
      exact Subtype.ext hcoordinates.2
    subst code'
    subst positiveArity
    have harityRaw : arity'.1 = natCode arity := by
      apply insert_self_injective
      calc
        insert arity'.1 arity'.1 =
            (TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)).1 :=
          hsuccessor.symm
        _ = natCode (arity + 1) := rfl
        _ = insert (natCode arity) (natCode arity) :=
          natCode_succ_eq_insert arity
    have harityEq :
        arity' =
          TextbookNatFormula.textbookNatCodeLCarrier arity := by
      exact Subtype.ext harityRaw
    subst arity'
    have hrelationRaw :
        relation.1 =
          textbookEZF U.1 (natCode (arity + 1)) (natCode code) := by
      simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using
        hrelation.2
    have hspaceRaw :
        space.1 = textbookTupleSpace seed.1 arity := by
      exact (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
        seed space arity).mp hspace
    rw [hspaceRaw] at hprefix
    rw [hrelationRaw] at hextension
    rw [hrelationRaw] at hminimal
    refine ⟨hprefix, houtput, hextension, ?_⟩
    intro z hzU hzRelation
    apply hminimal z hzU
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using
      hzRelation
  · rintro ⟨hprefix, houtput, hextension, hminimal⟩
    let codeL : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier code
    let positiveArityL : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier (arity + 1)
    let arityL : LCarrier.{u} :=
      TextbookNatFormula.textbookNatCodeLCarrier arity
    let task : LCarrier.{u} := orderedPairLCarrier codeL positiveArityL
    let request : LCarrier.{u} := orderedPairLCarrier task prefixGraph
    let relation : LCarrier.{u} := textbookEZFLCarrier U (arity + 1) code
    let space : LCarrier.{u} :=
      ContinuumFormula.finiteTupleSpaceLCarrier seed arity
    refine ⟨task, prefixGraph, codeL, positiveArityL, arityL, relation, space,
      ?_, ?_, ?_, ?_, ?_, ?_, houtput, ?_, ?_⟩
    · rfl
    · rfl
    · exact natCode_succ_eq_insert arity
    · constructor
      · constructor
        · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode (arity + 1))).mpr ⟨arity + 1, rfl⟩
        · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
            (natCode code)).mpr ⟨code, rfl⟩
      · rfl
    · exact
        (ContinuumFormula.satisfies_finiteTupleSpaceFormula_natCode_iff
          seed space arity).mpr rfl
    · exact hprefix
    · exact hextension
    · intro z hzU hzRelation
      exact hminimal z hzU hzRelation

/-! ## The total output formula -/

/--
Layout `[U, seed, order, request, output]`.  Return the selected witness if
one exists; otherwise return the empty set.
-/
def textbookEUniformTotalFormula : FOFormula 5 :=
  .disj textbookEUniformSelectedFormula
    (.conj
      (Delta0Formula.emptyDeltaAt (4 : Fin 5)).toFO
      (.neg (.ex
        (FOFormula.rename
          ![(0 : Fin 5).castSucc, (1 : Fin 5).castSucc,
            (2 : Fin 5).castSucc, (3 : Fin 5).castSucc, Fin.last 5]
          textbookEUniformSelectedFormula))))

 theorem total_selected_assignment
    (U seed order request output y : LCarrier.{u}) :
    (fun i =>
      (snoc ![U, seed, order, request, output] y)
        (![((0 : Fin 5).castSucc), ((1 : Fin 5).castSucc),
          ((2 : Fin 5).castSucc), ((3 : Fin 5).castSucc),
          (Fin.last 5)] i)) =
      ![U, seed, order, request, y] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_textbookEUniformTotalFormula
    (U seed order request output : LCarrier.{u}) :
    FOFormula.Satisfies LMem textbookEUniformTotalFormula
        ![U, seed, order, request, output] <->
      FOFormula.Satisfies LMem textbookEUniformSelectedFormula
          ![U, seed, order, request, output] \/
        (output = emptyLCarrier /\
          ¬ ∃ y : LCarrier.{u},
            FOFormula.Satisfies LMem textbookEUniformSelectedFormula
              ![U, seed, order, request, y]) := by
  simp only [textbookEUniformTotalFormula, FOFormula.satisfies_disj,
    FOFormula.Satisfies, satisfies_emptyDeltaAt_lCarrier,
    FOFormula.satisfies_rename]
  simp only [total_selected_assignment]
  constructor
  · rintro (hselected | ⟨hempty, hnone⟩)
    · exact Or.inl hselected
    · right
      refine ⟨Subtype.ext hempty, ?_⟩
      intro h
      exact hnone h
  · rintro (hselected | ⟨hempty, hnone⟩)
    · exact Or.inl hselected
    · right
      constructor
      · exact congrArg Subtype.val hempty
      · exact hnone

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TextbookEUniformWitnessFormula


/- Source module: Solutions.Work_CUGCH_InternalDefZFInjection -/
section GCHSource_Work_CUGCH_InternalDefZFInjection
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/








/-!
# An internal cardinal bound for `DefZF`

This file internalizes the textbook coding of a definable subset by

`<arity, <prefixGraph, formulaCode>>`.

The candidate triples form a genuine internal set.  Separation retains
exactly the triples that define a section, and Replacement constructs the
actual Kuratowski graph from valid triples to their sections.  The range is
proved extensionally equal to `DefZF a`; no external enumeration or external
cardinal comparison is used as the graph witness.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The positive-arity reverse bridge -/

/--
At every nonzero arity, each relation in a finite textbook `D` stage is the
relation of an intrinsically scoped first-order formula.

The nonzero hypothesis is essential: the textbook convention makes
zero-arity existential projection empty, whereas ordinary sentence
satisfaction need not be false.
-/
theorem exists_formula_of_mem_textbookDStageZF_of_ne_zero
    (a : ZFSet.{u}) (k n : Nat) (hn : n ≠ 0)
    {relation : ZFSet.{u}}
    (hrelation : relation ∈ textbookDStageZF a k n) :
    ∃ formula : FOFormula n,
      ∀ assignment : Tuple (ZFCarrier a) n,
        textbookTupleGraph assignment ∈ relation ↔
          FOFormula.Satisfies (zfCarrierMem a) formula assignment := by
  induction k generalizing n relation with
  | zero =>
      rw [textbookDStageZF_zero] at hrelation
      rcases mem_textbookDZeroZF_iff.mp hrelation with
        ⟨i, j, hrelation⟩ | ⟨i, j, hrelation⟩
      · subst relation
        exact ⟨.mem i j, fun assignment =>
          textbookTupleGraph_mem_DInZF_iff assignment i j⟩
      · subst relation
        exact ⟨.eq i j, fun assignment =>
          textbookTupleGraph_mem_DEqZF_iff assignment i j⟩
  | succ k ih =>
      rcases mem_textbookDStageZF_succ_iff.mp hrelation with
        hprevious |
        ⟨previous, hprevious, hrelation⟩ |
        ⟨left, hleft, right, hright, hrelation⟩ |
        ⟨previous, hprevious, hrelation⟩
      · exact ih n hn hprevious
      · subst relation
        rcases ih n hn hprevious with ⟨formula, hformula⟩
        refine ⟨.neg formula, ?_⟩
        intro assignment
        simp only [ZFSet.mem_sdiff, textbookTupleGraph_mem_tupleSpace,
          true_and, FOFormula.Satisfies, hformula]
      · subst relation
        rcases ih n hn hleft with ⟨leftFormula, hleftFormula⟩
        rcases ih n hn hright with ⟨rightFormula, hrightFormula⟩
        refine ⟨.conj leftFormula rightFormula, ?_⟩
        intro assignment
        simp only [ZFSet.mem_inter, FOFormula.Satisfies,
          hleftFormula, hrightFormula]
      · subst relation
        rcases ih (n + 1) (Nat.succ_ne_zero n) hprevious with
          ⟨formula, hformula⟩
        refine ⟨.ex formula, ?_⟩
        intro assignment
        rw [textbookTupleGraph_mem_existsProjZF_iff hn]
        simp only [FOFormula.Satisfies]
        apply exists_congr
        intro value
        exact hformula (snoc assignment value)

/-- Every positive-arity textbook `E` value has ordinary formula semantics. -/
theorem exists_formula_for_textbookEZF_positive
    (a : ZFSet.{u}) (n code : Nat) :
    ∃ formula : FOFormula (n + 1),
      ∀ assignment : Tuple (ZFCarrier a) (n + 1),
        textbookTupleGraph assignment ∈
            textbookEZF a (natCode (n + 1)) (natCode code) ↔
          FOFormula.Satisfies (zfCarrierMem a) formula assignment := by
  have hrelation :=
    textbookEZF_mem_textbookDfZF a (n + 1) code
  rcases mem_textbookDfZF_iff.mp hrelation with ⟨k, hk⟩
  exact exists_formula_of_mem_textbookDStageZF_of_ne_zero
    a k (n + 1) (Nat.succ_ne_zero n) hk

/--
A genuine textbook `E` section, with a valid finite prefix graph, belongs to
the original formula-based `DefZF`.
-/
theorem textbookE_section_mem_DefZF
    {a subset prefixGraph : ZFSet.{u}} (n code : Nat)
    (hsubset : subset ⊆ a)
    (hprefix : prefixGraph ∈ textbookTupleSpace a n)
    (hsection : ∀ x : ZFSet.{u}, x ∈ a →
      (x ∈ subset ↔
        textbookTupleSnocGraph prefixGraph n x ∈
          textbookEZF a (natCode (n + 1)) (natCode code))) :
    subset ∈ DefZF a := by
  have hprefixFunction :
      ZFSet.IsFunc (natCode n) a prefixGraph :=
    mem_textbookTupleSpace_iff.mp hprefix
  rcases exists_textbookTupleGraph_eq_of_isFunc hprefixFunction with
    ⟨params, hparams⟩
  rcases exists_formula_for_textbookEZF_positive a n code with
    ⟨formula, hformula⟩
  apply mem_DefZF_iff_exists_satisfies.mpr
  refine ⟨hsubset, n, params, formula, ?_⟩
  intro x
  calc
    x.1 ∈ subset ↔
        textbookTupleSnocGraph prefixGraph n x.1 ∈
          textbookEZF a (natCode (n + 1)) (natCode code) :=
      hsection x.1 x.2
    _ ↔ textbookTupleGraph (snoc params x) ∈
          textbookEZF a (natCode (n + 1)) (natCode code) := by
      rw [textbookTupleGraph_snoc, hparams]
    _ ↔ FOFormula.Satisfies (zfCarrierMem a) formula
          (snoc params x) :=
      hformula (snoc params x)

namespace ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

/-! ## One fixed formula for a coded section -/

/--
The body layout is

`[a, candidate, output, arity, inner, prefixGraph, code,
  positiveArity, relation, tupleSpace]`.
-/
def internalDefZFOutputBody : FOFormula 10 :=
  .conj
    (Delta0Formula.kuratowskiPairEqAt
      (1 : Fin 10) (3 : Fin 10) (4 : Fin 10)).toFO
  <| .conj
    (Delta0Formula.kuratowskiPairEqAt
      (4 : Fin 10) (5 : Fin 10) (6 : Fin 10)).toFO
  <| .conj
    (Delta0Formula.successorAt
      (7 : Fin 10) (3 : Fin 10)).toFO
  <| .conj
    (Model.textbookEZFFormulaAt
      (0 : Fin 10) (7 : Fin 10) (6 : Fin 10) (8 : Fin 10))
  <| .conj
    (Model.finiteTupleSpaceFormulaAt
      (0 : Fin 10) (3 : Fin 10) (9 : Fin 10))
  <| .conj
    (.mem (5 : Fin 10) (9 : Fin 10))
    (.all
      (FOFormula.biimp
        (.mem (Fin.last 10) (2 : Fin 10).castSucc)
        (.conj
          (.mem (Fin.last 10) (0 : Fin 10).castSucc)
          (Model.textbookETupleExtensionAt
            (8 : Fin 10).castSucc
            (5 : Fin 10).castSucc
            (3 : Fin 10).castSucc
            (Fin.last 10)))))

/--
Layout `[a,candidate,output]`.  The seven witnesses decode the candidate and
compute the corresponding textbook relation and finite tuple space.
-/
def internalDefZFOutputFormula : FOFormula 3 :=
  .ex <| .ex <| .ex <| .ex <| .ex <| .ex <| .ex
    internalDefZFOutputBody

 theorem internalDefZFBody_assignment
    (a candidate output arity inner prefixGraph code positiveArity
      relation tupleSpace : LCarrier.{u}) :
    snoc
      (snoc
        (snoc
          (snoc
            (snoc
              (snoc
                (snoc ![a, candidate, output] arity)
                inner)
              prefixGraph)
            code)
          positiveArity)
        relation)
      tupleSpace =
      ![a, candidate, output, arity, inner, prefixGraph, code,
        positiveArity, relation, tupleSpace] := by
  simp only [snoc_eq_finSnoc, Matrix.Fin.snoc_vecCons,
    Matrix.Fin.snoc_vecEmpty]

@[simp]
theorem satisfies_internalDefZFOutputFormula
    (a candidate output : LCarrier.{u}) :
    FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] ↔
      ∃ arity inner prefixGraph code positiveArity relation tupleSpace :
          LCarrier.{u},
        candidate.1 = ZFSet.pair arity.1 inner.1 ∧
        inner.1 = ZFSet.pair prefixGraph.1 code.1 ∧
        positiveArity.1 = insert arity.1 arity.1 ∧
        (((positiveArity.1 ∈ textbookEOmegaZF ∧
              code.1 ∈ textbookEOmegaZF) ∧
            relation.1 =
              textbookEZF a.1 positiveArity.1 code.1)) ∧
        FOFormula.Satisfies LMem
          finiteTupleSpaceFormula ![a, arity, tupleSpace] ∧
        prefixGraph.1 ∈ tupleSpace.1 ∧
        ∀ x : LCarrier.{u},
          (x.1 ∈ output.1 ↔
            x.1 ∈ a.1 ∧
              insert (ZFSet.pair arity.1 x.1) prefixGraph.1 ∈
                relation.1) := by
  simp only [internalDefZFOutputFormula, FOFormula.Satisfies]
  apply exists_congr
  intro arity
  apply exists_congr
  intro inner
  apply exists_congr
  intro prefixGraph
  apply exists_congr
  intro code
  apply exists_congr
  intro positiveArity
  apply exists_congr
  intro relation
  apply exists_congr
  intro tupleSpace
  rw [internalDefZFBody_assignment]
  simp only [internalDefZFOutputBody, FOFormula.Satisfies,
    satisfies_kuratowskiPairEqAt_lCarrier,
    satisfies_successorAt_lCarrier,
    Model.satisfies_textbookEZFFormulaAt_lCarrier,
    Model.satisfies_finiteTupleSpaceFormulaAt_lCarrier,
    FOFormula.satisfies_all, FOFormula.satisfies_biimp,
    Model.satisfies_textbookETupleExtensionAt,
    snoc_last, snoc_castSucc]
  change
    (candidate.1 = ZFSet.pair arity.1 inner.1 ∧
      inner.1 = ZFSet.pair prefixGraph.1 code.1 ∧
      positiveArity.1 = insert arity.1 arity.1 ∧
      (((positiveArity.1 ∈ textbookEOmegaZF ∧
            code.1 ∈ textbookEOmegaZF) ∧
          relation.1 =
            textbookEZF a.1 positiveArity.1 code.1)) ∧
      FOFormula.Satisfies LMem
        finiteTupleSpaceFormula ![a, arity, tupleSpace] ∧
      prefixGraph.1 ∈ tupleSpace.1 ∧
      ∀ x : LCarrier.{u},
        (x.1 ∈ output.1 ↔
          x.1 ∈ a.1 ∧
            insert (ZFSet.pair arity.1 x.1) prefixGraph.1 ∈
              relation.1)) ↔ _
  rfl

/-! ## The separated domain of valid codes -/

/-- Layout `[a,candidate]`: the candidate has a represented section output. -/
def internalDefZFHasOutputFormula : FOFormula 2 :=
  .ex internalDefZFOutputFormula

 theorem internalDefZFOutput_assignment
    (a candidate output : LCarrier.{u}) :
    snoc ![a, candidate] output = ![a, candidate, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_internalDefZFHasOutputFormula
    (a candidate : LCarrier.{u}) :
    FOFormula.Satisfies LMem internalDefZFHasOutputFormula
        ![a, candidate] ↔
      ∃ output : LCarrier.{u},
        FOFormula.Satisfies LMem internalDefZFOutputFormula
          ![a, candidate, output] := by
  simp only [internalDefZFHasOutputFormula, FOFormula.Satisfies]
  apply exists_congr
  intro output
  rw [internalDefZFOutput_assignment]

/-- The ambient internal set containing every possible coded triple. -/
def internalDefZFCandidateContainer (a : LCarrier.{u}) :
    LCarrier.{u} :=
  prodLCarrier (omegaLCarrier : LCarrier.{u})
    (prodLCarrier (internalFiniteTupleSpaces a) omegaLCarrier)

/--
Separation retains exactly the triples in the candidate container that have
an output according to the fixed section formula.
-/
noncomputable def internalDefZFCandidateDomain (a : LCarrier.{u}) :
    LCarrier.{u} :=
  Classical.choose (exists_separationLCarrier
    internalDefZFHasOutputFormula ![a]
    (internalDefZFCandidateContainer a))

 theorem internalDefZFCandidate_assignment
    (a candidate : LCarrier.{u}) :
    snoc ![a] candidate = ![a, candidate] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem mem_internalDefZFCandidateDomain_iff
    (a candidate : LCarrier.{u}) :
    candidate.1 ∈ (internalDefZFCandidateDomain a).1 ↔
      candidate.1 ∈ (internalDefZFCandidateContainer a).1 ∧
        ∃ output : LCarrier.{u},
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            ![a, candidate, output] := by
  rw [internalDefZFCandidateDomain]
  rw [Classical.choose_spec (exists_separationLCarrier
    internalDefZFHasOutputFormula ![a]
    (internalDefZFCandidateContainer a)) candidate]
  rw [internalDefZFCandidate_assignment,
    satisfies_internalDefZFHasOutputFormula]

/-! ## Functionality of the coded-section relation -/

theorem internalDefZFOutputFormula_unique
    (a candidate first second : LCarrier.{u})
    (hfirst : FOFormula.Satisfies LMem internalDefZFOutputFormula
      ![a, candidate, first])
    (hsecond : FOFormula.Satisfies LMem internalDefZFOutputFormula
      ![a, candidate, second]) :
    first = second := by
  rcases (satisfies_internalDefZFOutputFormula
    a candidate first).mp hfirst with
    ⟨firstArity, firstInner, firstPrefix, firstCode,
      firstPositiveArity, firstRelation, firstTupleSpace,
      hfirstCandidate, hfirstInner, hfirstSuccessor,
      hfirstRelation, _hfirstSpace, _hfirstPrefix, hfirstMembers⟩
  rcases (satisfies_internalDefZFOutputFormula
    a candidate second).mp hsecond with
    ⟨secondArity, secondInner, secondPrefix, secondCode,
      secondPositiveArity, secondRelation, secondTupleSpace,
      hsecondCandidate, hsecondInner, hsecondSuccessor,
      hsecondRelation, _hsecondSpace, _hsecondPrefix, hsecondMembers⟩
  have houter := ZFSet.pair_inj.mp
    (hfirstCandidate.symm.trans hsecondCandidate)
  have harity : secondArity = firstArity :=
    Subtype.ext houter.1.symm
  have hinner : secondInner = firstInner :=
    Subtype.ext houter.2.symm
  subst secondArity
  subst secondInner
  have hinnerCoordinates := ZFSet.pair_inj.mp
    (hfirstInner.symm.trans hsecondInner)
  have hprefix : secondPrefix = firstPrefix :=
    Subtype.ext hinnerCoordinates.1.symm
  have hcode : secondCode = firstCode :=
    Subtype.ext hinnerCoordinates.2.symm
  subst secondPrefix
  subst secondCode
  have hpositive : secondPositiveArity = firstPositiveArity :=
    Subtype.ext (hsecondSuccessor.trans hfirstSuccessor.symm)
  subst secondPositiveArity
  have hrelation : secondRelation = firstRelation := by
    apply Subtype.ext
    exact hsecondRelation.2.trans hfirstRelation.2.symm
  subst secondRelation
  apply Subtype.ext
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx first.2⟩
    exact (hsecondMembers xL).mpr ((hfirstMembers xL).mp hx)
  · intro hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx second.2⟩
    exact (hfirstMembers xL).mpr ((hsecondMembers xL).mp hx)

theorem internalDefZFOutputFormula_existsUnique
    (a candidate : LCarrier.{u})
    (hcandidate :
      candidate.1 ∈ (internalDefZFCandidateDomain a).1) :
    ∃! output : LCarrier.{u},
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] := by
  rcases (mem_internalDefZFCandidateDomain_iff
    a candidate).mp hcandidate with
    ⟨_hcandidateContainer, output, houtput⟩
  refine ⟨output, houtput, ?_⟩
  intro other hother
  exact internalDefZFOutputFormula_unique
    a candidate other output hother houtput

/-! ## Soundness of every represented output -/

theorem mem_DefZF_of_satisfies_internalDefZFOutputFormula
    (a candidate output : LCarrier.{u})
    (hcandidateContainer :
      candidate.1 ∈ (internalDefZFCandidateContainer a).1)
    (hformula :
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output]) :
    output.1 ∈ DefZF a.1 := by
  rcases (satisfies_internalDefZFOutputFormula
    a candidate output).mp hformula with
    ⟨arity, inner, prefixGraph, code, positiveArity, relation,
      tupleSpace, hcandidate, hinner, hsuccessor, hrelation,
      hspace, hprefix, hmembers⟩
  have hcontainer := hcandidateContainer
  change candidate.1 ∈
      ZFSet.prod (omegaLCarrier : LCarrier.{u}).1
        (ZFSet.prod (internalFiniteTupleSpaces a).1
          (omegaLCarrier : LCarrier.{u}).1) at hcontainer
  rw [hcandidate, ZFSet.pair_mem_prod] at hcontainer
  have harityOmega : arity.1 ∈
      (omegaLCarrier : LCarrier.{u}).1 :=
    hcontainer.1
  have hinnerContainer := hcontainer.2
  rw [hinner, ZFSet.pair_mem_prod] at hinnerContainer
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      arity.1).mp harityOmega with
    ⟨n, harityValue⟩
  have harityEq :
      arity = TextbookNatFormula.textbookNatCodeLCarrier n := by
    apply Subtype.ext
    exact harityValue
  subst arity
  have hpositiveEq :
      positiveArity =
        TextbookNatFormula.textbookNatCodeLCarrier (n + 1) := by
    apply Subtype.ext
    exact hsuccessor.trans (natCode_succ_eq_insert n).symm
  subst positiveArity
  have hcodeOmega :
      code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    exact hrelation.1.2
  rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode
      code.1).mp hcodeOmega with
    ⟨m, hcodeValue⟩
  have hcodeEq :
      code = TextbookNatFormula.textbookNatCodeLCarrier m := by
    apply Subtype.ext
    exact hcodeValue
  subst code
  have hrelationValue :
      relation.1 =
        textbookEZF a.1 (natCode (n + 1)) (natCode m) := by
    simpa only [TextbookNatFormula.textbookNatCodeLCarrier_val] using
      hrelation.2
  have hspaceValue :
      tupleSpace.1 = textbookTupleSpace a.1 n :=
    (satisfies_finiteTupleSpaceFormula_natCode_iff
      a tupleSpace n).mp hspace
  have hprefixValue :
      prefixGraph.1 ∈ textbookTupleSpace a.1 n := by
    rwa [hspaceValue] at hprefix
  have houtputSubset : output.1 ⊆ a.1 := by
    intro x hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx output.2⟩
    exact (hmembers xL).mp hx |>.1
  apply textbookE_section_mem_DefZF n m houtputSubset hprefixValue
  intro x hx
  let xL : LCarrier.{u} :=
    ⟨x, mem_L_of_mem hx a.2⟩
  calc
    x ∈ output.1 ↔
        x ∈ a.1 ∧
          insert (ZFSet.pair (natCode n) x) prefixGraph.1 ∈
            relation.1 := by
      simpa only [xL,
        TextbookNatFormula.textbookNatCodeLCarrier_val] using
          hmembers xL
    _ ↔ insert (ZFSet.pair (natCode n) x) prefixGraph.1 ∈
          relation.1 :=
      and_iff_right hx
    _ ↔ textbookTupleSnocGraph prefixGraph.1 n x ∈
          textbookEZF a.1 (natCode (n + 1)) (natCode m) := by
      rw [textbookTupleSnocGraph, hrelationValue]

/-! ## Completeness of the coded candidates -/

theorem exists_internalDefZFCandidate_of_mem_DefZF
    (a : LCarrier.{u}) {z : ZFSet.{u}}
    (hz : z ∈ DefZF a.1) :
    ∃ candidate output : LCarrier.{u},
      candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] ∧
      output.1 = z := by
  rcases exists_textbookE_section_of_mem_DefZF hz with
    ⟨n, m, prefixRaw, hprefixRaw, hsection⟩
  let arity : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier n
  let code : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier m
  let positiveArity : LCarrier.{u} :=
    TextbookNatFormula.textbookNatCodeLCarrier (n + 1)
  let prefixGraph : LCarrier.{u} :=
    ⟨prefixRaw,
      mem_L_of_mem hprefixRaw (textbookTupleSpace_mem_L a.2 n)⟩
  let inner : LCarrier.{u} :=
    orderedPairLCarrier prefixGraph code
  let candidate : LCarrier.{u} :=
    orderedPairLCarrier arity inner
  let relation : LCarrier.{u} :=
    textbookEZFLCarrier a (n + 1) m
  let tupleSpace : LCarrier.{u} :=
    finiteTupleSpaceLCarrier a n
  let output : LCarrier.{u} :=
    textbookEWitnessCandidates a relation prefixGraph arity
  have harityOmega :
      arity.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode n)).mpr ⟨n, rfl⟩
  have hpositiveOmega :
      positiveArity.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode (n + 1) : ZFSet.{u}) ∈ textbookEOmegaZF
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode (n + 1))).mpr ⟨n + 1, rfl⟩
  have hcodeOmega :
      code.1 ∈ (omegaLCarrier : LCarrier.{u}).1 := by
    change (natCode m : ZFSet.{u}) ∈ textbookEOmegaZF
    exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
      (natCode m)).mpr ⟨m, rfl⟩
  have hprefixFinite :
      prefixGraph.1 ∈ (internalFiniteTupleSpaces a).1 := by
    apply (mem_internalFiniteTupleSpaces_iff a prefixGraph).mpr
    refine ⟨n, ?_⟩
    simpa only [prefixGraph, finiteTupleSpaceLCarrier_val] using
      hprefixRaw
  have hcandidateContainer :
      candidate.1 ∈ (internalDefZFCandidateContainer a).1 := by
    change ZFSet.pair arity.1 inner.1 ∈
      ZFSet.prod (omegaLCarrier : LCarrier.{u}).1
        (ZFSet.prod (internalFiniteTupleSpaces a).1
          (omegaLCarrier : LCarrier.{u}).1)
    rw [ZFSet.pair_mem_prod]
    refine ⟨harityOmega, ?_⟩
    change ZFSet.pair prefixGraph.1 code.1 ∈
      ZFSet.prod (internalFiniteTupleSpaces a).1
        (omegaLCarrier : LCarrier.{u}).1
    rw [ZFSet.pair_mem_prod]
    exact ⟨hprefixFinite, hcodeOmega⟩
  have hformula :
      FOFormula.Satisfies LMem internalDefZFOutputFormula
        ![a, candidate, output] := by
    apply (satisfies_internalDefZFOutputFormula
      a candidate output).mpr
    refine ⟨arity, inner, prefixGraph, code, positiveArity,
      relation, tupleSpace, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact natCode_succ_eq_insert n
    · exact ⟨⟨hpositiveOmega, hcodeOmega⟩, rfl⟩
    · exact (satisfies_finiteTupleSpaceFormula_natCode_iff
        a tupleSpace n).mpr rfl
    · exact hprefixRaw
    · intro x
      exact mem_textbookEWitnessCandidates_iff
        a relation prefixGraph arity x
  have hcandidate :
      candidate.1 ∈ (internalDefZFCandidateDomain a).1 :=
    (mem_internalDefZFCandidateDomain_iff a candidate).mpr
      ⟨hcandidateContainer, output, hformula⟩
  refine ⟨candidate, output, hcandidate, hformula, ?_⟩
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hx output.2⟩
    have hxData := (mem_textbookEWitnessCandidates_iff
      a relation prefixGraph arity xL).mp hx
    apply (hsection x hxData.1).mpr
    simpa only [relation, textbookEZFLCarrier_val, prefixGraph,
      arity, TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookTupleSnocGraph] using hxData.2
  · intro hx
    have hza : z ⊆ a.1 := (mem_DefZF_iff.mp hz).1
    have hxa : x ∈ a.1 := hza hx
    let xL : LCarrier.{u} :=
      ⟨x, mem_L_of_mem hxa a.2⟩
    apply (mem_textbookEWitnessCandidates_iff
      a relation prefixGraph arity xL).mpr
    refine ⟨hxa, ?_⟩
    have hxSection := (hsection x hxa).mp hx
    simpa only [relation, textbookEZFLCarrier_val, prefixGraph,
      arity, TextbookNatFormula.textbookNatCodeLCarrier_val,
      textbookTupleSnocGraph] using hxSection

/-! ## Replacement and the genuine internal `DefZF` set -/

/--
The represented data produced by Replacement.  Its range is not merely a
surrogate: `range_eq_DefZF` identifies its underlying set with the original
`DefZF a`.
-/
structure InternalDefZFData (a : LCarrier.{u}) where
  graph : LCarrier.{u}
  range : LCarrier.{u}
  isFunctionGraph :
    IsFunctionGraph LMem graph (internalDefZFCandidateDomain a) range
  mem_range_iff : ∀ output : LCarrier.{u},
    output.1 ∈ range.1 ↔
      ∃ candidate : LCarrier.{u},
        candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            ![a, candidate, output]
  graphValue_iff : ∀ candidate output : LCarrier.{u},
    GraphValue LMem graph candidate output ↔
      candidate.1 ∈ (internalDefZFCandidateDomain a).1 ∧
        FOFormula.Satisfies LMem internalDefZFOutputFormula
          ![a, candidate, output]
  range_eq_DefZF : range.1 = DefZF a.1

 theorem internalDefZFReplacement_assignment
    (a candidate output : LCarrier.{u}) :
    snoc (snoc ![a] candidate) output =
      ![a, candidate, output] := by
  funext i
  fin_cases i <;> rfl

/--
Replacement simultaneously constructs the actual function graph and the
actual set representing `DefZF a`.
-/
theorem exists_internalDefZFData (a : LCarrier.{u}) :
    Nonempty (InternalDefZFData a) := by
  let params : Tuple LCarrier.{u} 1 := ![a]
  let domain : LCarrier.{u} := internalDefZFCandidateDomain a
  have hfun : ∀ candidate : LCarrier.{u},
      candidate.1 ∈ domain.1 →
        ∃! output : LCarrier.{u},
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            (snoc (snoc params candidate) output) := by
    intro candidate hcandidate
    simpa only [params, domain,
      internalDefZFReplacement_assignment] using
        internalDefZFOutputFormula_existsUnique
          a candidate hcandidate
  rcases exists_replacementFunctionGraphAndRangeLCarrier
      internalDefZFOutputFormula params domain hfun with
    ⟨graph, range, hfunction, hrange, hvalue⟩
  have hrangeVector : ∀ output : LCarrier.{u},
      output.1 ∈ range.1 ↔
        ∃ candidate : LCarrier.{u},
          candidate.1 ∈ domain.1 ∧
            FOFormula.Satisfies LMem internalDefZFOutputFormula
              ![a, candidate, output] := by
    intro output
    simpa only [params,
      internalDefZFReplacement_assignment] using hrange output
  have hvalueVector : ∀ candidate output : LCarrier.{u},
      GraphValue LMem graph candidate output ↔
        candidate.1 ∈ domain.1 ∧
          FOFormula.Satisfies LMem internalDefZFOutputFormula
            ![a, candidate, output] := by
    intro candidate output
    simpa only [params,
      internalDefZFReplacement_assignment] using
        hvalue candidate output
  have hrangeEq : range.1 = DefZF a.1 := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      let zL : LCarrier.{u} :=
        ⟨z, mem_L_of_mem hz range.2⟩
      rcases (hrangeVector zL).mp hz with
        ⟨candidate, hcandidate, hformula⟩
      have hcandidateContainer :=
        (mem_internalDefZFCandidateDomain_iff
          a candidate).mp hcandidate |>.1
      exact mem_DefZF_of_satisfies_internalDefZFOutputFormula
        a candidate zL hcandidateContainer hformula
    · intro hz
      rcases exists_internalDefZFCandidate_of_mem_DefZF
          a hz with
        ⟨candidate, output, hcandidate, hformula, houtput⟩
      rw [← houtput]
      exact (hrangeVector output).mpr
        ⟨candidate, hcandidate, hformula⟩
  refine ⟨{
    graph := graph
    range := range
    isFunctionGraph := by simpa only [domain] using hfunction
    mem_range_iff := by
      intro output
      simpa only [domain] using hrangeVector output
    graphValue_iff := by
      intro candidate output
      simpa only [domain] using hvalueVector candidate output
    range_eq_DefZF := hrangeEq
  }⟩

/-- A canonical internally represented copy of the original `DefZF a`. -/
noncomputable def internalDefZFData (a : LCarrier.{u}) :
    InternalDefZFData a :=
  Classical.choice (exists_internalDefZFData a)

/--
The genuine `LCarrier` whose underlying `ZFSet` is exactly `DefZF a`.
Its membership proof is obtained from Separation and Replacement above.
-/
noncomputable def DefZFLCarrier (a : LCarrier.{u}) :
    LCarrier.{u} :=
  (internalDefZFData a).range

@[simp]
theorem DefZFLCarrier_val (a : LCarrier.{u}) :
    (DefZFLCarrier a).1 = DefZF a.1 :=
  (internalDefZFData a).range_eq_DefZF

/-! ## The internal cardinal injection -/







end ContinuumFormula

end

end Constructible

end
end GCHSource_Work_CUGCH_InternalDefZFInjection


