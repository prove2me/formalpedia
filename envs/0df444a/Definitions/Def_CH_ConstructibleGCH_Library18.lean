-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library18
-- name    : CH_ConstructibleGCH_Library18
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T08:02:15.676103+00:00
-- url     : https://prove2.me/theorems/0ee41c5c-e7e1-4aa0-b89c-0d144e006ea4
-- title:
--   Definability enumeration and Skolem requests
-- statement:
--   This library supplies parameterized textbook E domains, the E recursion, positive finite-formula enumeration, and the witness requests used for Skolem closure. Its definitions connect finite syntactic descriptions with the constructible sets they describe.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEParameterizedDomain.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookERecursion.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEDefinability.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookPositiveFormulaEnumeration.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookESkolemClosure.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEInternalTasks.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookEConstructible.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library17
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookEParameterizedDomain -/
section GCHSource_Work_CUGCH_TextbookEParameterizedDomain
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The parameterized domain of the textbook enumeration recursion

The recursion defining `E(a,n,m)` has one fixed set parameter `a`, whereas
its domain `omega x omega` and its recursion relation do not depend on `a`.
This file inserts the parameter into the first-order contexts by a literal
renaming of the parameter-free formulas from `TextbookEDomain`.

The layouts are

* `(a,key)` for `textbookEDomainWithParamFormula`, and
* `(a,left,right)` for `textbookERelationWithParamFormula`.

In particular, coordinate zero is deliberately absent from both renaming
maps.  No property of `a` is added to either formula.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace TextbookEFormula

/-! ## The formulas and their exact renaming semantics -/

/-- Insert a dummy parameter before the sole domain variable. -/
def textbookEDomainWithParamRename : Fin 1 -> Fin 2 :=
  ![(1 : Fin 2)]

/-- Insert a dummy parameter before the two relation variables. -/
def textbookERelationWithParamRename : Fin 2 -> Fin 3 :=
  ![(1 : Fin 3), (2 : Fin 3)]

/-- The domain formula in the layout `(a,key)`.  The parameter `a` is
syntactically ignored. -/
def textbookEDomainWithParamFormula : FOFormula 2 :=
  FOFormula.rename textbookEDomainWithParamRename domainFormula

/-- The relation formula in the layout `(a,left,right)`.  The parameter `a`
is syntactically ignored. -/
def textbookERelationWithParamFormula : FOFormula 3 :=
  FOFormula.rename textbookERelationWithParamRename relationFormula

@[simp]
theorem textbookEDomainWithParamRename_apply
    (i : Fin 1) : textbookEDomainWithParamRename i = (1 : Fin 2) := by
  fin_cases i
  rfl

@[simp]
theorem textbookERelationWithParamRename_zero :
    textbookERelationWithParamRename (0 : Fin 2) = (1 : Fin 3) := by
  rfl

@[simp]
theorem textbookERelationWithParamRename_one :
    textbookERelationWithParamRename (1 : Fin 2) = (2 : Fin 3) := by
  rfl

/-- Ambient satisfaction of the parameterized domain formula is exactly
ambient satisfaction of the old formula at `key`. -/
@[simp]
theorem satisfies_textbookEDomainWithParamFormula
    (s : Tuple ZFSet.{u} 2) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookEDomainWithParamFormula s <->
      FOFormula.Satisfies Delta0Formula.ZFMem domainFormula ![s 1] := by
  rw [textbookEDomainWithParamFormula, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s (textbookEDomainWithParamRename i)) = ![s 1] := by
    funext i
    fin_cases i
    rfl
  rw [hassignment]

/-- Ambient satisfaction of the parameterized relation formula is exactly
ambient satisfaction of the old formula at `(left,right)`. -/
@[simp]
theorem satisfies_textbookERelationWithParamFormula
    (s : Tuple ZFSet.{u} 3) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        textbookERelationWithParamFormula s <->
      FOFormula.Satisfies Delta0Formula.ZFMem relationFormula
        ![s 1, s 2] := by
  rw [textbookERelationWithParamFormula, FOFormula.satisfies_rename]
  have hassignment :
      (fun i => s (textbookERelationWithParamRename i)) =
        ![s 1, s 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]

end TextbookEFormula

namespace Model

/-! ## Restricted semantics and absoluteness -/

 theorem satisfiesIn_rename_iff_TextbookEParameterizedDomain_gch
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rename formula) s <->
      SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

/-- Restricted satisfaction also forgets precisely the first coordinate. -/
@[simp]
theorem satisfiesIn_textbookEDomainWithParamFormula_rename
    (M : Set ZFSet.{u}) (s : Tuple ZFSet.{u} 2) :
    SatisfiesIn M TextbookEFormula.textbookEDomainWithParamFormula s <->
      SatisfiesIn M TextbookEFormula.domainFormula ![s 1] := by
  rw [TextbookEFormula.textbookEDomainWithParamFormula,
    satisfiesIn_rename_iff_TextbookEParameterizedDomain_gch]
  have hassignment :
      (fun i => s (TextbookEFormula.textbookEDomainWithParamRename i)) =
        ![s 1] := by
    funext i
    fin_cases i
    rfl
  rw [hassignment]

/-- Restricted satisfaction of the relation formula likewise forgets
precisely the first coordinate. -/
@[simp]
theorem satisfiesIn_textbookERelationWithParamFormula_rename
    (M : Set ZFSet.{u}) (s : Tuple ZFSet.{u} 3) :
    SatisfiesIn M TextbookEFormula.textbookERelationWithParamFormula s <->
      SatisfiesIn M TextbookEFormula.relationFormula ![s 1, s 2] := by
  rw [TextbookEFormula.textbookERelationWithParamFormula,
    satisfiesIn_rename_iff_TextbookEParameterizedDomain_gch]
  have hassignment :
      (fun i => s (TextbookEFormula.textbookERelationWithParamRename i)) =
        ![s 1, s 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]







end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEParameterizedDomain


/- Source module: Solutions.Work_CUGCH_TextbookERecursion -/
section GCHSource_Work_CUGCH_TextbookERecursion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The textbook simultaneous recursion defining `E`

This file constructs the function `E(a,n,m)` from Wang, *Axiomatic Set
Theory*, Section 6.4.  The recursion is performed on the actual set-coded
domain `omega x omega`, with keys ordered as `<m,n>` and with

`<i,k> R <m,n>` exactly when `i in m`.

Consequently the whole row with first coordinate `i` is available when the
value at first coordinate `m` is formed.  In particular, the projection
clause may use `E(a,n+1,i)`.  No external Lean graph is used as an internal
history witness; the object-language representation is supplied below by the
general internal textbook-recursion theorem.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## The ambient recursive solution -/

/-- The class solution of the textbook recursion, totalized by the empty set
away from the set-coded domain `omega x omega`. -/
noncomputable def textbookEByKey (a : ZFSet.{u}) : ZFSet.{u} -> ZFSet.{u} :=
  textbookGlobalRecursionFromLocalGraphs
    textbookERelation_isWellFoundedSetLikeOn (textbookEStep a)

/-- The constructed function satisfies the exact textbook class-recursion
equation on its declared domain. -/
theorem textbookEByKey_satisfies_classRecursion (a : ZFSet.{u}) :
    SatisfiesTextbookClassRecursion TextbookEDomain TextbookERelation
      textbookERelation_isWellFoundedSetLikeOn.2.2 (textbookEStep a)
      (textbookEByKey a) := by
  exact textbookGlobalRecursionFromLocalGraphs_satisfies_classRecursion
    textbookERelation_isWellFoundedSetLikeOn (textbookEStep a)

/-- The pointwise recursion equation on a genuine key. -/
theorem textbookEByKey_eq
    (a : ZFSet.{u}) {key : ZFSet.{u}} (hkey : key ∈ TextbookEDomain) :
    textbookEByKey a key =
      textbookEStep a key
        (predecessorRestrictionGraph
          (displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_isWellFoundedSetLikeOn.2.2 key)
          (textbookEByKey a)) := by
  exact textbookEByKey_satisfies_classRecursion a key hkey

/-- Outside `omega x omega`, the totalized recursive solution is empty. -/
@[simp]
theorem textbookEByKey_eq_empty_of_not_mem
    (a key : ZFSet.{u}) (hkey : key ∉ TextbookEDomain) :
    textbookEByKey a key = ∅ := by
  exact textbookGlobalRecursionFromLocalGraphs_eq_empty_of_not_mem
    textbookERelation_isWellFoundedSetLikeOn (textbookEStep a) hkey

/-- The textbook argument order is `(a,n,m)`, while the recursion key is
`<m,n>`. -/
noncomputable def textbookEZF
    (a n m : ZFSet.{u}) : ZFSet.{u} :=
  textbookEByKey a (ZFSet.pair m n)

/-! ## Access to earlier rows -/

 theorem natCode_mem_textbookEOmega (n : Nat) :
    (natCode n : ZFSet.{u}) ∈ textbookEOmegaZF := by
  exact (IndexedSequenceZF.mem_omega_iff_exists_natCode (natCode n)).mpr
    ⟨n, rfl⟩

 theorem textbookE_natKey_mem_domain (m n : Nat) :
    ZFSet.pair (natCode m : ZFSet.{u}) (natCode n) ∈ TextbookEDomain := by
  apply mem_textbookEDomain_iff.mpr
  exact ⟨natCode m, natCode_mem_textbookEOmega m,
    natCode n, natCode_mem_textbookEOmega n, rfl⟩

 theorem textbookE_earlierKey_mem_predecessors
    (m n i k : Nat) (hi : i < m) :
    ZFSet.pair (natCode i : ZFSet.{u}) (natCode k) ∈
      displayedPredecessors TextbookEDomain TextbookERelation
        textbookERelation_isWellFoundedSetLikeOn.2.2
        (ZFSet.pair (natCode m) (natCode n)) := by
  apply (displayedPredecessors_spec
    textbookERelation_isWellFoundedSetLikeOn.2.2
    (textbookE_natKey_mem_domain m n)
    (ZFSet.pair (natCode i) (natCode k))).mpr
  constructor
  · exact textbookE_natKey_mem_domain i k
  · rw [classRel_textbookERelation_iff]
    exact ⟨natCode i, natCode k, natCode m, natCode n,
      natCode_mem_textbookEOmega i, natCode_mem_textbookEOmega k,
      natCode_mem_textbookEOmega m, natCode_mem_textbookEOmega n,
      rfl, rfl, (natCode_mem_natCode_iff i m).mpr hi⟩

 theorem uniqueGraphLookupZF_predecessorRestrictionGraph
    (domain : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u})
    {key : ZFSet.{u}} (hkey : key ∈ domain) :
    uniqueGraphLookupZF (predecessorRestrictionGraph domain f) key = f key := by
  apply uniqueGraphLookupZF_eq_of_unique
  · exact pair_mem_predecessorRestrictionGraph f hkey
  · intro other hother
    rcases mem_predecessorRestrictionGraph_iff.mp hother with
      ⟨source, _hsource, hpair⟩
    have hcoordinates := ZFSet.pair_inj.mp hpair
    rw [hcoordinates.1] at hcoordinates
    exact hcoordinates.2.symm

 theorem textbookE_history_lookup
    (a : ZFSet.{u}) (m n i k : Nat) (hi : i < m) :
    uniqueGraphLookupZF
        (predecessorRestrictionGraph
          (displayedPredecessors TextbookEDomain TextbookERelation
            textbookERelation_isWellFoundedSetLikeOn.2.2
            (ZFSet.pair (natCode m) (natCode n)))
          (textbookEByKey a))
        (ZFSet.pair (natCode i) (natCode k)) =
      textbookEZF a (natCode k) (natCode i) := by
  rw [uniqueGraphLookupZF_predecessorRestrictionGraph _ _
    (textbookE_earlierKey_mem_predecessors m n i k hi)]
  rfl

/-! ## The five equations from Section 6.4 -/

@[simp]
theorem textbookEZF_code_zero
    (a : ZFSet.{u}) (n i j : Nat) (hi : i < n) (hj : j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 0)) =
      textbookDInCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 0) n)]
  exact textbookEStep_code_zero a _ n i j hi hj

@[simp]
theorem textbookEZF_code_one
    (a : ZFSet.{u}) (n i j : Nat) (hi : i < n) (hj : j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 1)) =
      textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 1) n)]
  exact textbookEStep_code_one a _ n i j hi hj

@[simp]
theorem textbookEZF_code_two
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 2)) =
      relativeDifferenceZF (ZFSet.funs (natCode n) a)
        (textbookEZF a (natCode n) (natCode i)) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 2) n),
    textbookEStep_code_two]
  exact congrArg (relativeDifferenceZF (ZFSet.funs (natCode n) a))
    (textbookE_history_lookup a (textbookECode i j 2) n i n
      (textbookECode_index_lt i j 2))

@[simp]
theorem textbookEZF_code_three
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 3)) =
      intersectionZF
        (textbookEZF a (natCode n) (natCode i))
        (textbookEZF a (natCode n) (natCode j)) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 3) n),
    textbookEStep_code_three]
  rw [textbookE_history_lookup a (textbookECode i j 3) n i n
      (textbookECode_index_lt i j 3),
    textbookE_history_lookup a (textbookECode i j 3) n j n]
  exact lt_of_lt_of_le
    (lt_of_lt_of_le j.lt_two_pow_self
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j)) (by
    simp only [textbookECode]
    have htwo : 0 < 2 ^ i := Nat.pow_pos (by decide)
    have hfive : 0 < 5 ^ 3 := Nat.pow_pos (by decide)
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.le_mul_of_pos_left (3 ^ j) (Nat.mul_pos htwo hfive))

@[simp]
theorem textbookEZF_code_four
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 4)) =
      textbookExistsProjCodeZF a (natCode n)
        (textbookEZF a (natCode (n + 1)) (natCode i)) := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 4) n),
    textbookEStep_code_four]
  exact congrArg (textbookExistsProjCodeZF a (natCode n))
    (textbookE_history_lookup a (textbookECode i j 4) n i (n + 1)
      (textbookECode_index_lt i j 4))

/-! The dummy field `j` in clauses two and four remains part of the code,
exactly as in the textbook, even though the resulting set does not depend on
that field. -/

@[simp]
theorem textbookEZF_code_zero_eq_empty_of_not_lt_left
    (a : ZFSet.{u}) (n i j : Nat) (hi : ¬ i < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 0)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 0) n)]
  exact textbookEStep_code_zero_eq_empty_of_not_lt_left a _ n i j hi

@[simp]
theorem textbookEZF_code_zero_eq_empty_of_not_lt_right
    (a : ZFSet.{u}) (n i j : Nat) (hj : ¬ j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 0)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 0) n)]
  exact textbookEStep_code_zero_eq_empty_of_not_lt_right a _ n i j hj

@[simp]
theorem textbookEZF_code_one_eq_empty_of_not_lt_left
    (a : ZFSet.{u}) (n i j : Nat) (hi : ¬ i < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 1)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 1) n)]
  exact textbookEStep_code_one_eq_empty_of_not_lt_left a _ n i j hi

@[simp]
theorem textbookEZF_code_one_eq_empty_of_not_lt_right
    (a : ZFSet.{u}) (n i j : Nat) (hj : ¬ j < n) :
    textbookEZF a (natCode n) (natCode (textbookECode i j 1)) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain (textbookECode i j 1) n)]
  exact textbookEStep_code_one_eq_empty_of_not_lt_right a _ n i j hj

/-- The final "otherwise" branch for a malformed natural-number code. -/
@[simp]
theorem textbookEZF_eq_empty_of_decode_none
    (a : ZFSet.{u}) (n m : Nat) (hm : textbookEDecode m = none) :
    textbookEZF a (natCode n) (natCode m) = ∅ := by
  rw [textbookEZF, textbookEByKey_eq a
    (textbookE_natKey_mem_domain m n)]
  simp [textbookEStep, hm]

/-! ## Pure membership-language graphs -/

namespace TextbookEFormula

/-- The graph of the recursive solution with layout `[a,key,output]`. -/
def textbookERecursionValueFormula : FOFormula 3 :=
  Model.recursionValueFormula textbookEDomainWithParamFormula
    textbookERelationWithParamFormula textbookEStepFormula

/-- Coordinate map selecting `[a,key,output]` from the existential context
`[a,n,m,output,key]`. -/
def textbookERecursionValueParameters : Fin 3 -> Fin 5 :=
  ![(0 : Fin 5), (4 : Fin 5), (3 : Fin 5)]

/-- The public graph of `E`, with layout `[a,n,m,output]`.

The quantified witness is the internal Kuratowski pair `<m,n>`, in the same
order as the ambient recursion key. -/
def textbookEZFFormula : FOFormula 4 :=
  .ex <| .conj
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last 4) (2 : Fin 5) (1 : Fin 5)).toFO
    (FOFormula.rename textbookERecursionValueParameters
      textbookERecursionValueFormula)

@[simp]
theorem textbookERecursionValueParameters_zero :
    textbookERecursionValueParameters (0 : Fin 3) = (0 : Fin 5) := by
  rfl

@[simp]
theorem textbookERecursionValueParameters_one :
    textbookERecursionValueParameters (1 : Fin 3) = (4 : Fin 5) := by
  rfl

@[simp]
theorem textbookERecursionValueParameters_two :
    textbookERecursionValueParameters (2 : Fin 3) = (3 : Fin 5) := by
  rfl

end TextbookEFormula

/-! ## The set-coded input domain -/



@[simp]
theorem pair_mem_textbookEDomain_iff
    (m n : ZFSet.{u}) :
    ZFSet.pair m n ∈ TextbookEDomain ↔
      m ∈ textbookEOmegaZF ∧ n ∈ textbookEOmegaZF := by
  constructor
  · intro hpair
    rcases mem_textbookEDomain_iff.mp hpair with
      ⟨m', hm', n', hn', hp⟩
    have hcoordinates := ZFSet.pair_inj.mp hp
    simpa only [hcoordinates.1, hcoordinates.2] using And.intro hm' hn'
  · rintro ⟨hm, hn⟩
    exact mem_textbookEDomain_iff.mpr ⟨m, hm, n, hn, rfl⟩



namespace Model

 theorem satisfiesIn_rename_iff_eRecursion
    (M : Set ZFSet.{u}) {n m : Nat} (formula : FOFormula n)
    (rename : Fin n -> Fin m) (s : Tuple ZFSet.{u} m) :
    SatisfiesIn M (FOFormula.rename rename formula) s ↔
      SatisfiesIn M formula (fun i => s (rename i)) := by
  induction formula generalizing m with
  | mem i j => rfl
  | eq i j => rfl
  | neg formula ih => exact not_congr (ih rename s)
  | conj left right ihLeft ihRight =>
      exact and_congr (ihLeft rename s) (ihRight rename s)
  | ex formula ih =>
      simp only [FOFormula.rename, SatisfiesIn, ih]
      constructor
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula
      · rintro ⟨value, hvalueM, hformula⟩
        refine ⟨value, hvalueM, ?_⟩
        simpa only [FOFormula.snoc_comp_liftRename] using hformula

@[simp]
theorem satisfiesIn_textbookERecursionValueFormula_rename
    (M : Set ZFSet.{u}) (s : Tuple ZFSet.{u} 5) :
    SatisfiesIn M
        (FOFormula.rename TextbookEFormula.textbookERecursionValueParameters
          TextbookEFormula.textbookERecursionValueFormula) s ↔
      SatisfiesIn M TextbookEFormula.textbookERecursionValueFormula
        ![s 0, s 4, s 3] := by
  rw [satisfiesIn_rename_iff_eRecursion]
  have hassignment :
      (fun i => s
        (TextbookEFormula.textbookERecursionValueParameters i)) =
        ![s 0, s 4, s 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hassignment]









end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookERecursion


/- Source module: Solutions.Work_CUGCH_TextbookEDefinability -/
section GCHSource_Work_CUGCH_TextbookEDefinability
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The textbook enumeration of definable relations

This file proves the two directions of Wang, *Axiomatic Set Theory*, Section
6.4, Proposition 2.  For fixed `a` and finite arity `n`, the recursively
constructed function `E(a,n,m)` enumerates exactly `Df(a,n)`:

`Df(a,n) = {E(a,n,m) | m in omega}`.

The proof follows the displayed five-clause definition.  Soundness is strong
induction on the numerical code, and completeness is induction on the finite
closure stages `D(k,a,n)`.  The resulting cardinal bound is an external
cardinal statement.  Internal model closure is treated separately below by
Replacement, rather than inferred from this external enumeration.
-/

section

open Set
open scoped Cardinal

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section



/-! ## Closure properties of `Df(a,n)` -/

theorem textbookDInZF_mem_textbookDfZF
    (a : ZFSet.{u}) {n i j : Nat} (hi : i < n) (hj : j < n) :
    textbookDInZF a n i j ∈ textbookDfZF a n := by
  apply textbookDStageZF_subset_DfZF a 0 n
  rw [textbookDStageZF_zero]
  exact mem_textbookDZeroZF_iff.mpr
    (Or.inl ⟨⟨i, hi⟩, ⟨j, hj⟩, rfl⟩)

theorem textbookDEqZF_mem_textbookDfZF
    (a : ZFSet.{u}) {n i j : Nat} (hi : i < n) (hj : j < n) :
    textbookDEqZF a n i j ∈ textbookDfZF a n := by
  apply textbookDStageZF_subset_DfZF a 0 n
  rw [textbookDStageZF_zero]
  exact mem_textbookDZeroZF_iff.mpr
    (Or.inr ⟨⟨i, hi⟩, ⟨j, hj⟩, rfl⟩)

 theorem textbookDInZF_self_eq_empty
    (a : ZFSet.{u}) {n i : Nat} (hi : i < n) :
    textbookDInZF a n i i = ∅ := by
  apply ZFSet.eq_empty _ |>.mpr
  intro graph hgraph
  rcases mem_textbookDInZF_iff.mp hgraph with
    ⟨hspace, _hi, _hi', x, y, hx, hy, hxy⟩
  have hfunc := mem_textbookTupleSpace_iff.mp hspace
  have hindex : (natCode i : ZFSet.{u}) ∈ natCode n :=
    (mem_natCode_iff_exists_fin (natCode i) n).mpr
      ⟨⟨i, hi⟩, rfl⟩
  rcases hfunc.2 (natCode i) hindex with ⟨value, hvalue, hunique⟩
  have hxvalue : x = value := hunique x hx
  have hyvalue : y = value := hunique y hy
  rw [hxvalue, hyvalue] at hxy
  exact ZFSet.mem_irrefl value hxy

/-- The default value used by malformed `E` codes really is a member of every
`Df(a,n)`.  At positive arity it is the false atomic relation `x_i in x_i`;
at arity zero it is obtained by the textbook's exceptional empty projection.
-/
theorem empty_mem_textbookDfZF (a : ZFSet.{u}) (n : Nat) :
    (∅ : ZFSet.{u}) ∈ textbookDfZF a n := by
  by_cases hn : n = 0
  · subst n
    have hfalse : textbookDInZF a 1 0 0 = (∅ : ZFSet.{u}) :=
      textbookDInZF_self_eq_empty a (by omega)
    have hfalseStage : (∅ : ZFSet.{u}) ∈ textbookDStageZF a 0 1 := by
      rw [textbookDStageZF_zero]
      rw [← hfalse]
      exact mem_textbookDZeroZF_iff.mpr
        (Or.inl ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩)
    apply textbookDStageZF_subset_DfZF a 1 0
    apply mem_textbookDStageZF_succ_iff.mpr
    exact Or.inr (Or.inr (Or.inr
      ⟨∅, hfalseStage, textbookExistsProjZF_zero a ∅⟩))
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hfalse := textbookDInZF_self_eq_empty a hnpos
    rw [← hfalse]
    exact textbookDInZF_mem_textbookDfZF a hnpos hnpos

theorem textbookDfZF_relativeDifference
    (a : ZFSet.{u}) {n : Nat} {r : ZFSet.{u}}
    (hr : r ∈ textbookDfZF a n) :
    relativeDifferenceZF (ZFSet.funs (natCode n) a) r ∈
      textbookDfZF a n := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨k, hk⟩
  apply textbookDStageZF_subset_DfZF a (k + 1) n
  apply mem_textbookDStageZF_succ_iff.mpr
  exact Or.inr (Or.inl ⟨r, hk, rfl⟩)

theorem textbookDfZF_intersection
    (a : ZFSet.{u}) {n : Nat} {r t : ZFSet.{u}}
    (hr : r ∈ textbookDfZF a n) (ht : t ∈ textbookDfZF a n) :
    intersectionZF r t ∈ textbookDfZF a n := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨kr, hkr⟩
  rcases mem_textbookDfZF_iff.mp ht with ⟨kt, hkt⟩
  let k := max kr kt
  have hrk : r ∈ textbookDStageZF a k n :=
    textbookDStageZF_mono a (Nat.le_max_left _ _) hkr
  have htk : t ∈ textbookDStageZF a k n :=
    textbookDStageZF_mono a (Nat.le_max_right _ _) hkt
  apply textbookDStageZF_subset_DfZF a (k + 1) n
  apply mem_textbookDStageZF_succ_iff.mpr
  exact Or.inr (Or.inr (Or.inl ⟨r, hrk, t, htk, rfl⟩))

theorem textbookDfZF_existsProjection
    (a : ZFSet.{u}) {n : Nat} {r : ZFSet.{u}}
    (hr : r ∈ textbookDfZF a (n + 1)) :
    textbookExistsProjZF a n r ∈ textbookDfZF a n := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨k, hk⟩
  apply textbookDStageZF_subset_DfZF a (k + 1) n
  apply mem_textbookDStageZF_succ_iff.mpr
  exact Or.inr (Or.inr (Or.inr ⟨r, hk, rfl⟩))

/-! ## Every value of `E` belongs to `Df` -/

/-- Soundness of the textbook enumeration.  The induction hypothesis is
available at every arity because the projection clause refers to row `n+1`.
-/
theorem textbookEZF_mem_textbookDfZF
    (a : ZFSet.{u}) (n m : Nat) :
    textbookEZF a (natCode n) (natCode m) ∈ textbookDfZF a n := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      cases hdecode : textbookEDecode m with
      | none =>
          rw [textbookEZF_eq_empty_of_decode_none a n m hdecode]
          exact empty_mem_textbookDfZF a n
      | some fields =>
          rcases fields with ⟨i, j, tag⟩
          have hfields :=
            (textbookEDecode_eq_some_iff m i j tag).mp hdecode
          rcases hfields with ⟨htag, hcode⟩
          subst m
          rcases (show tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨
              tag = 4 by omega) with htag | htag | htag | htag | htag <;>
            subst tag
          · by_cases hi : i < n
            · by_cases hj : j < n
              · rw [textbookEZF_code_zero a n i j hi hj,
                  textbookDInCodeZF_natCode]
                exact textbookDInZF_mem_textbookDfZF a hi hj
              · rw [textbookEZF_code_zero_eq_empty_of_not_lt_right
                    a n i j hj]
                exact empty_mem_textbookDfZF a n
            · rw [textbookEZF_code_zero_eq_empty_of_not_lt_left
                  a n i j hi]
              exact empty_mem_textbookDfZF a n
          · by_cases hi : i < n
            · by_cases hj : j < n
              · rw [textbookEZF_code_one a n i j hi hj,
                  textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_textbookDfZF a hi hj
              · rw [textbookEZF_code_one_eq_empty_of_not_lt_right
                    a n i j hj]
                exact empty_mem_textbookDfZF a n
            · rw [textbookEZF_code_one_eq_empty_of_not_lt_left
                  a n i j hi]
              exact empty_mem_textbookDfZF a n
          · rw [textbookEZF_code_two]
            exact textbookDfZF_relativeDifference a
              (ih i (textbookECode_index_lt i j 2) n)
          · rw [textbookEZF_code_three]
            exact textbookDfZF_intersection a
              (ih i (textbookECode_index_lt i j 3) n)
              (ih j (by
                exact lt_of_lt_of_le
                  (lt_of_lt_of_le j.lt_two_pow_self
                    (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j)) (by
                      simp only [textbookECode]
                      have htwo : 0 < 2 ^ i := Nat.pow_pos (by decide)
                      have hfive : 0 < 5 ^ 3 := Nat.pow_pos (by decide)
                      simpa only [Nat.mul_assoc, Nat.mul_comm,
                        Nat.mul_left_comm] using
                        Nat.le_mul_of_pos_left (3 ^ j)
                          (Nat.mul_pos htwo hfive))) n)
          · rw [textbookEZF_code_four, textbookExistsProjCodeZF_natCode]
            exact textbookDfZF_existsProjection a
              (ih i (textbookECode_index_lt i j 4) (n + 1))

/-! ## Every member of `Df` has an `E` code -/

 theorem exists_textbookECode_of_mem_DStage
    (a : ZFSet.{u}) :
    ∀ k n r, r ∈ textbookDStageZF a k n →
      ∃ m : Nat, textbookEZF a (natCode n) (natCode m) = r := by
  intro k
  induction k with
  | zero =>
      intro n r hr
      rw [textbookDStageZF_zero] at hr
      rcases mem_textbookDZeroZF_iff.mp hr with
        ⟨i, j, hir⟩ | ⟨i, j, hir⟩
      · refine ⟨textbookECode i.1 j.1 0, ?_⟩
        rw [textbookEZF_code_zero a n i.1 j.1 i.2 j.2,
          textbookDInCodeZF_natCode, hir]
      · refine ⟨textbookECode i.1 j.1 1, ?_⟩
        rw [textbookEZF_code_one a n i.1 j.1 i.2 j.2,
          textbookDEqCodeZF_natCode, hir]
  | succ k ih =>
      intro n r hr
      rcases mem_textbookDStageZF_succ_iff.mp hr with
        hr | ⟨t, ht, htr⟩ | ⟨t, ht, v, hv, htvr⟩ |
          ⟨t, ht, htr⟩
      · exact ih n r hr
      · rcases ih n t ht with ⟨i, hi⟩
        refine ⟨textbookECode i 0 2, ?_⟩
        rw [textbookEZF_code_two, hi]
        exact htr
      · rcases ih n t ht with ⟨i, hi⟩
        rcases ih n v hv with ⟨j, hj⟩
        refine ⟨textbookECode i j 3, ?_⟩
        rw [textbookEZF_code_three, hi, hj]
        exact htvr
      · rcases ih (n + 1) t ht with ⟨i, hi⟩
        refine ⟨textbookECode i 0 4, ?_⟩
        rw [textbookEZF_code_four, textbookExistsProjCodeZF_natCode, hi]
        exact htr

/-- Completeness of the textbook enumeration. -/
theorem exists_textbookEZF_eq_of_mem_textbookDfZF
    {a r : ZFSet.{u}} {n : Nat} (hr : r ∈ textbookDfZF a n) :
    ∃ m : Nat, textbookEZF a (natCode n) (natCode m) = r := by
  rcases mem_textbookDfZF_iff.mp hr with ⟨k, hk⟩
  exact exists_textbookECode_of_mem_DStage a k n r hk

/-- Exact elementwise form of the textbook identity
`Df(a,n) = {E(a,n,m) | m in omega}`. -/
theorem mem_textbookDfZF_iff_exists_textbookEZF
    {a r : ZFSet.{u}} {n : Nat} :
    r ∈ textbookDfZF a n ↔
      ∃ m : Nat, textbookEZF a (natCode n) (natCode m) = r := by
  constructor
  · exact exists_textbookEZF_eq_of_mem_textbookDfZF
  · rintro ⟨m, rfl⟩
    exact textbookEZF_mem_textbookDfZF a n m



/-! ## The fixed-arity cardinal bound -/





/-- The least textbook `E` code of a member of `Df(a,n)`. -/
noncomputable def firstTextbookECode (a : ZFSet.{u}) (n : Nat)
    (r : ZFCarrier (textbookDfZF a n)) : Nat := by
  classical
  exact Nat.find (exists_textbookEZF_eq_of_mem_textbookDfZF r.2)

@[simp]
theorem textbookEZF_firstTextbookECode
    (a : ZFSet.{u}) (n : Nat)
    (r : ZFCarrier (textbookDfZF a n)) :
    textbookEZF a (natCode n) (natCode (firstTextbookECode a n r)) = r.1 := by
  classical
  exact Nat.find_spec (exists_textbookEZF_eq_of_mem_textbookDfZF r.2)







/-! ## The internal Replacement range -/

namespace Model





end Model

/-! ## A pure membership-language graph for `Df` -/

namespace TextbookDfFormula

/-- Select `[a,n,omega,relation]` from the context
`[a,n,output,omega,relation]`. -/
def textbookDfRangeParameters : Fin 4 -> Fin 5 :=
  ![(0 : Fin 5), (1 : Fin 5), (3 : Fin 5), (4 : Fin 5)]

/-- Layout `[a,n,output,omega]`.  Every member of `output` is, and only is, a
value `E(a,n,m)` for some `m in omega`. -/
def textbookDfMembersFormula : FOFormula 4 :=
  FOFormula.all <| FOFormula.biimp
    (.mem (Fin.last 4) (2 : Fin 4).castSucc)
    (FOFormula.rename textbookDfRangeParameters
      (replacementRangeFormula TextbookEFormula.textbookEZFFormula))

/-- The public graph of the set-coded function `Df`, with layout
`[a,n,output]`.  The existential variable is the internally least inductive
set, and the explicit membership guard makes the graph false unless
`n in omega`. -/
def textbookDfZFFormula : FOFormula 3 :=
  .ex <| .conj
    (Model.standardOmegaAt (Fin.last 3))
    (.conj
      (.mem (1 : Fin 3).castSucc (Fin.last 3))
      textbookDfMembersFormula)

end TextbookDfFormula





namespace Model



















end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEDefinability


/- Source module: Solutions.Work_CUGCH_TextbookPositiveFormulaEnumeration -/
section GCHSource_Work_CUGCH_TextbookPositiveFormulaEnumeration
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Textbook enumeration of positive-arity formula relations

For a formula with `n + 1` free variables, this file recursively constructs
the actual relation set on the textbook tuple space `a^(n+1)`.  Atomic
formulas use `D_in` and `D_eq`; negation uses relative complement;
conjunction uses intersection; and existential quantification uses the
textbook projection operation.

The semantic correctness theorem is proved on the Kuratowski function graph
which represents each tuple.  The closure clauses then show that the relation
belongs to the genuine internal set `textbookDfZF a (n + 1)`, so completeness
of the textbook `E` enumeration supplies a natural-number code for it.

Only positive arities are asserted.  This is mathematically significant:
the textbook convention makes the zero-arity projection empty, whereas an
ordinary closed existential sentence can be true.  Skolem matrices have the
positive arity `n + 1`, so no needed witness relation is lost and the
zero-arity convention is not silently identified with sentence semantics.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-- The recursively generated textbook relation set.  At arity zero this
still follows the textbook's exceptional projection convention; semantic
correctness is therefore stated below only under `n != 0`. -/
noncomputable def textbookFormulaRelationZF
    (a : ZFSet.{u}) : {n : Nat} -> FOFormula n -> ZFSet.{u}
  | n, .mem i j => textbookDInZF a n i.1 j.1
  | n, .eq i j => textbookDEqZF a n i.1 j.1
  | n, .neg formula =>
      relativeDifferenceZF (textbookTupleSpace a n)
        (textbookFormulaRelationZF a formula)
  | _, .conj formula psi =>
      intersectionZF
        (textbookFormulaRelationZF a formula)
        (textbookFormulaRelationZF a psi)
  | n, .ex formula =>
      textbookExistsProjZF a n
        (textbookFormulaRelationZF a formula)

/-- The positive-arity specialization used by Skolem matrices. -/
noncomputable def textbookPositiveFormulaRelation
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) : ZFSet.{u} :=
  textbookFormulaRelationZF a formula

/-- On every represented tuple, the recursively constructed relation has
exactly the ordinary Tarskian semantics of the source formula. -/
theorem textbookTupleGraph_mem_textbookFormulaRelationZF_iff_of_ne_zero
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula n)
    (hn : n ≠ 0) (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ textbookFormulaRelationZF a formula ↔
      FOFormula.Satisfies (zfCarrierMem a) formula s := by
  induction formula with
  | mem i j =>
      simpa only [textbookFormulaRelationZF, FOFormula.Satisfies,
        zfCarrierMem] using
        (textbookTupleGraph_mem_DInZF_iff s i j)
  | eq i j =>
      simpa only [textbookFormulaRelationZF, FOFormula.Satisfies] using
        (textbookTupleGraph_mem_DEqZF_iff s i j)
  | neg formula ih =>
      simp only [textbookFormulaRelationZF,
        mem_relativeDifferenceZF_iff,
        textbookTupleGraph_mem_tupleSpace, true_and,
        FOFormula.Satisfies, ih hn]
  | conj formula psi ihFormula ihPsi =>
      simp only [textbookFormulaRelationZF,
        mem_intersectionZF_iff, FOFormula.Satisfies,
        ihFormula hn, ihPsi hn]
  | @ex m formula ih =>
      rw [textbookFormulaRelationZF,
        textbookTupleGraph_mem_existsProjZF_iff hn]
      apply exists_congr
      intro x
      exact ih (Nat.succ_ne_zero m) (snoc s x)

/-- Positive arity removes the exceptional zero-arity case. -/
@[simp]
theorem textbookTupleGraph_mem_textbookPositiveFormulaRelation_iff
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple (ZFCarrier a) (n + 1)) :
    textbookTupleGraph s ∈ textbookPositiveFormulaRelation a formula ↔
      FOFormula.Satisfies (zfCarrierMem a) formula s := by
  exact textbookTupleGraph_mem_textbookFormulaRelationZF_iff_of_ne_zero
    a formula (Nat.succ_ne_zero n) s

/-- Every positive-arity formula relation belongs to the textbook `Df` set
at the matching arity. -/
theorem textbookFormulaRelationZF_mem_textbookDfZF
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula n) :
    textbookFormulaRelationZF a formula ∈ textbookDfZF a n := by
  induction formula with
  | mem i j =>
      exact textbookDInZF_mem_textbookDfZF a i.2 j.2
  | eq i j =>
      exact textbookDEqZF_mem_textbookDfZF a i.2 j.2
  | neg formula ih =>
      simpa only [textbookFormulaRelationZF, textbookTupleSpace] using
        (textbookDfZF_relativeDifference a ih)
  | conj formula psi ihFormula ihPsi =>
      simpa only [textbookFormulaRelationZF] using
        (textbookDfZF_intersection a ihFormula ihPsi)
  | ex formula ih =>
      simpa only [textbookFormulaRelationZF] using
        (textbookDfZF_existsProjection a ih)

/-- Every positive-arity formula relation belongs to the textbook `Df` set
at the matching arity. -/
theorem textbookPositiveFormulaRelation_mem_textbookDfZF
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) :
    textbookPositiveFormulaRelation a formula ∈
      textbookDfZF a (n + 1) := by
  exact textbookFormulaRelationZF_mem_textbookDfZF a formula

/-- Completeness of the textbook `E` enumeration supplies a code for the
relation of every positive-arity formula. -/
theorem exists_textbookEZF_eq_textbookPositiveFormulaRelation
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) :
    ∃ code : Nat,
      textbookEZF a (natCode (n + 1)) (natCode code) =
        textbookPositiveFormulaRelation a formula :=
  exists_textbookEZF_eq_of_mem_textbookDfZF
    (textbookPositiveFormulaRelation_mem_textbookDfZF a formula)

/-- Semantic form of the preceding enumeration theorem: one textbook `E`
value recognizes exactly the satisfying represented tuples. -/
theorem exists_textbookECode_for_positiveFormula
    (a : ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1)) :
    ∃ code : Nat, ∀ s : Tuple (ZFCarrier a) (n + 1),
      textbookTupleGraph s ∈
          textbookEZF a (natCode (n + 1)) (natCode code) ↔
        FOFormula.Satisfies (zfCarrierMem a) formula s := by
  rcases exists_textbookEZF_eq_textbookPositiveFormulaRelation
      a formula with ⟨code, hcode⟩
  refine ⟨code, ?_⟩
  intro s
  rw [hcode]
  exact textbookTupleGraph_mem_textbookPositiveFormulaRelation_iff
    a formula s

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookPositiveFormulaEnumeration


/- Source module: Solutions.Work_CUGCH_TextbookESkolemClosure -/
section GCHSource_Work_CUGCH_TextbookESkolemClosure
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Full Tarski--Vaught closure through the textbook E enumeration

The textbook operation `E(U,n,m)` enumerates every positive-arity relation in
`Df(U,n)`.  `TextbookPositiveFormulaEnumeration` proves, without appealing to
an object-language truth predicate, that the relation of every formula with
at least one free coordinate occurs in this enumeration.

This file packages the corresponding full Tarski--Vaught criterion.  If a
subset of `U` contains witnesses for every relation `E(U,n+1,m)` and every
parameter tuple from the subset, then it is closed for every existential
subformula of every first-order formula.  Hence satisfaction is absolute for
all formulas, not merely for a finite fragment.

`ClosesUnderTextbookEWitnesses` is still an external semantic predicate.  No
claim is made here that a small subset satisfying it has already been
constructed inside `L`.  The remaining construction must internally
enumerate the pairs `(n,m)`, uniformly define the canonical witness step, and
collect its omega iteration by Replacement.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

section ZFC

/-- Closure under witnesses for every relation in the textbook `E`
enumeration.  A relation has arity `n + 1`; its final coordinate is the
candidate witness and the first `n` coordinates are parameters. -/
def ClosesUnderTextbookEWitnesses
    (small : Set ZFSet.{u}) (U : ZFSet.{u}) : Prop :=
  ∀ {n : Nat} (code : Nat) (params : Tuple (ZFCarrier U) n),
    (∀ i, (params i).1 ∈ small) ->
      (∃ x : ZFCarrier U,
        textbookTupleGraph (snoc params x) ∈
          textbookEZF U (natCode (n + 1)) (natCode code)) ->
      ∃ x : ZFCarrier U,
        x.1 ∈ small ∧
          textbookTupleGraph (snoc params x) ∈
            textbookEZF U (natCode (n + 1)) (natCode code)





end ZFC

end Constructible

end
end GCHSource_Work_CUGCH_TextbookESkolemClosure


/- Source module: Solutions.Work_CUGCH_TextbookEInternalTasks -/
section GCHSource_Work_CUGCH_TextbookEInternalTasks
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The internal task domain for textbook E witnesses

The witness instances used by `ClosesUnderTextbookEWitnesses` are indexed by
a relation code `m` and a positive arity `n + 1`.  This file represents those
indices by the actual constructible set

`omega x (omega \ {0})`.

The first coordinate is the `E` recursion code and the second coordinate is
the positive arity.  Thus a task is the same Kuratowski key
`<m,n+1>` that the recursion defining `E` uses.  The membership theorem below
proves both coverage and unique decoding; external natural numbers occur only
in that correctness statement, not as the purported internal task set.

The final theorem exactly rewrites `ClosesUnderTextbookEWitnesses` as closure
over members of this internal task domain.  It does not claim that the
corresponding witness operation has already been represented by one internal
function graph or collected through omega by Replacement.  In particular,
constructibility of the uniformly varying values
`textbookEZF U (natCode (n + 1)) (natCode m)` remains a separate obligation.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

namespace Model

/-! ## The actual constructible task set -/

/-- The standard internal omega, packaged as an actual member of `L`. -/
def textbookEOmegaLCarrier : LCarrier.{u} :=
  ⟨textbookEOmegaZF, omega_mem_L⟩

/-- The singleton containing the von Neumann zero, packaged in `L`. -/
def textbookEZeroSingletonLCarrier : LCarrier.{u} :=
  pairLCarrier emptyLCarrier emptyLCarrier

/-- The positive standard naturals `omega \ {0}`, constructed by the
rudimentary difference operation inside `L`. -/
def textbookEPositiveOmegaLCarrier : LCarrier.{u} :=
  ⟨Godel.F1 textbookEOmegaLCarrier.1 textbookEZeroSingletonLCarrier.1,
    by
      simpa [Godel.op] using
        (Godel.op_mem_L (i := (1 : Fin 9))
          textbookEOmegaLCarrier.2 textbookEZeroSingletonLCarrier.2)⟩

/-- Internal witness tasks.  The first coordinate is an `E` code and the
second coordinate is its positive arity. -/
def textbookEWitnessTaskDomain : LCarrier.{u} :=
  prodLCarrier textbookEOmegaLCarrier textbookEPositiveOmegaLCarrier

@[simp]
theorem textbookEWitnessTaskDomain_val :
    (textbookEWitnessTaskDomain : LCarrier.{u}).1 =
      ZFSet.prod textbookEOmegaZF textbookEPositiveOmegaLCarrier.1 :=
  rfl

theorem mem_textbookEPositiveOmegaLCarrier_iff (x : ZFSet.{u}) :
    x ∈ (textbookEPositiveOmegaLCarrier : LCarrier.{u}).1 ↔
      ∃ n : Nat, x = natCode (n + 1) := by
  rw [textbookEPositiveOmegaLCarrier, Godel.mem_F1_iff]
  constructor
  · rintro ⟨hxOmega, hxZero⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hxOmega with
      ⟨n, rfl⟩
    cases n with
    | zero =>
        exfalso
        apply hxZero
        let zeroCode : LCarrier.{u} :=
          ⟨natCode 0, natCode_mem_L 0⟩
        change zeroCode.1 ∈ textbookEZeroSingletonLCarrier.1
        rw [textbookEZeroSingletonLCarrier,
          mem_pairLCarrier_iff]
        apply Or.inl
        apply Subtype.ext
        simp only [zeroCode, emptyLCarrier, natCode, Nat.cast_zero,
          Ordinal.toZFSet_zero]
    | succ n =>
        exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    constructor
    · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (n + 1))).mpr ⟨n + 1, rfl⟩
    · let succCode : LCarrier.{u} :=
        ⟨natCode (n + 1), natCode_mem_L (n + 1)⟩
      change succCode.1 ∉ textbookEZeroSingletonLCarrier.1
      intro hmem
      rcases (mem_pairLCarrier_iff emptyLCarrier emptyLCarrier
          succCode).mp (by
            simpa only [textbookEZeroSingletonLCarrier] using hmem) with
        heq | heq
      · have hcode : (natCode (n + 1) : ZFSet.{u}) = natCode 0 := by
          calc
            natCode (n + 1) = ∅ := congrArg Subtype.val heq
            _ = natCode 0 := by
              simp only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero]
        have : n + 1 = 0 := natCode_injective hcode
        omega
      · have hcode : (natCode (n + 1) : ZFSet.{u}) = natCode 0 := by
          calc
            natCode (n + 1) = ∅ := congrArg Subtype.val heq
            _ = natCode 0 := by
              simp only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero]
        have : n + 1 = 0 := natCode_injective hcode
        omega

/-- Exact decoding of every member of the internal task domain. -/
theorem mem_textbookEWitnessTaskDomain_iff (task : ZFSet.{u}) :
    task ∈ (textbookEWitnessTaskDomain : LCarrier.{u}).1 ↔
      ∃ code arity : Nat,
        task = ZFSet.pair (natCode code) (natCode (arity + 1)) := by
  rw [textbookEWitnessTaskDomain_val, ZFSet.mem_prod]
  constructor
  · rintro ⟨codeZF, hcode, arityZF, harity, rfl⟩
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode codeZF).mp hcode with
      ⟨code, rfl⟩
    rcases (mem_textbookEPositiveOmegaLCarrier_iff arityZF).mp harity with
      ⟨arity, rfl⟩
    exact ⟨code, arity, rfl⟩
  · rintro ⟨code, arity, rfl⟩
    exact ⟨natCode code,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode code)).mpr ⟨code, rfl⟩,
      natCode (arity + 1),
      (mem_textbookEPositiveOmegaLCarrier_iff
        (natCode (arity + 1))).mpr ⟨arity, rfl⟩,
      rfl⟩





/-! ## Exact reduction of the external closure predicate -/







end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEInternalTasks


/- Source module: Solutions.Work_CUGCH_TextbookEConstructible -/
section GCHSource_Work_CUGCH_TextbookEConstructible
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Constructibility of the textbook E values

This file proves directly that the standard-natural-number values of the
textbook recursion `E(a,n,m)` are constructible whenever `a` is.  The proof
does not place `L` inside a transitive set model of ZF.

The main preliminary step is closure under finite function spaces.  Every
finite function graph with values in a constructible set is itself
constructible.  The whole finite function space is then obtained by one
bounded definition over a constructible level containing all those graphs.
The atomic relations and existential projection are handled by the same
bounded-section argument.  Finally, strong induction on the numerical `E`
code follows the five clauses from the textbook definition.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

noncomputable section

/-! ## A bounded-definition closure lemma for `L` -/

/-- A set all of whose members are constructible is constructible when one
fixed bounded formula defines it from finitely many constructible
parameters. -/
 theorem mem_L_of_delta0_definition
    {z : ZFSet.{u}} {n : Nat}
    (params : Tuple ZFSet.{u} n) (hparams : ∀ i, params i ∈ L)
    (formula : Delta0Formula (n + 1))
    (correct : ∀ q : ZFSet.{u},
      Delta0Formula.Satisfies Delta0Formula.ZFMem formula
          (snoc params q) ↔ q ∈ z)
    (hmembers : ∀ q ∈ z, q ∈ L) :
    z ∈ L := by
  rcases exists_LStage_for_tuple params hparams with
    ⟨parameterStage, hparameterStage⟩
  rcases exists_LStage_for_members hmembers with
    ⟨memberStage, hmemberStage⟩
  let stage : Ordinal.{u} := max parameterStage memberStage
  let stageParams : Tuple (ZFCarrier (LStageZF stage)) n :=
    fun i =>
      ⟨params i,
        LStageZF_mono (le_max_left parameterStage memberStage)
          (hparameterStage i)⟩
  let certificate : Delta0Section (LStageZF stage) z :=
    { arity := n
      params := stageParams
      formula := formula
      correct := by
        intro q
        have hvalues : Delta0Formula.val stageParams = params := by
          funext i
          rfl
        simpa only [hvalues] using correct q.1 }
  refine ⟨Order.succ stage, ?_⟩
  rw [LStageZF_succ]
  apply certificate.mem_DefZF (LStageZF_isTransitive stage)
  intro q hq
  exact LStageZF_mono (le_max_right parameterStage memberStage)
    (hmemberStage q hq)

/-! ## Finite tuple spaces preserve constructibility -/

/-- Adjoining one constructible element to a constructible set preserves
constructibility. -/
theorem textbookInsert_mem_L {x a : ZFSet.{u}}
    (hx : x ∈ L) (ha : a ∈ L) : insert x a ∈ L := by
  rw [ZFSet.insert_eq]
  exact union_mem_L (singleton_mem_L hx) ha

/-- The graph of a finite tuple of members of a constructible set belongs to
`L`. -/
theorem textbookTupleGraph_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) {n : Nat}
    (tuple : Tuple (ZFCarrier a) n) :
    textbookTupleGraph tuple ∈ L := by
  induction n with
  | zero =>
      have hempty : textbookTupleGraph tuple = (∅ : ZFSet.{u}) := by
        apply ZFSet.eq_empty _ |>.mpr
        intro q hq
        rcases (mem_textbookTupleGraph_iff tuple).mp hq with ⟨i, _⟩
        exact Fin.elim0 i
      rw [hempty]
      exact empty_mem_L
  | succ n ih =>
      let initial : Tuple (ZFCarrier a) n :=
        fun i => tuple i.castSucc
      let finalEntry : ZFCarrier a := tuple (Fin.last n)
      have htuple : tuple = snoc initial finalEntry := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [finalEntry]
        · simp [initial]
      rw [htuple, textbookTupleGraph_snoc]
      apply textbookInsert_mem_L
      · exact orderedPair_mem_L (natCode_mem_L n)
          (mem_L_of_mem finalEntry.2 ha)
      · exact ih initial

/-- The actual set of all functions from a standard finite ordinal to a
constructible set is constructible. -/
theorem textbookTupleSpace_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n : Nat) :
    textbookTupleSpace a n ∈ L := by
  let params : Tuple ZFSet.{u} 2 := ![natCode n, a]
  apply mem_L_of_delta0_definition params (by
      intro i
      fin_cases i
      · exact natCode_mem_L n
      · exact ha)
    (TextbookDefFormula.isFunctionDeltaAt
      (2 : Fin 3) (0 : Fin 3) (1 : Fin 3))
  · intro graph
    rw [TextbookDefFormula.satisfies_isFunctionDeltaAt]
    exact mem_textbookTupleSpace_iff.symm
  · intro graph hgraph
    rcases exists_textbookTupleGraph_eq_of_isFunc
        (mem_textbookTupleSpace_iff.mp hgraph) with
      ⟨tuple, rfl⟩
    exact textbookTupleGraph_mem_L ha tuple

/-! ## The four set operations occurring in the E clauses -/

/-- The atomic membership relation on a finite tuple space is constructible. -/
theorem textbookDInZF_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n i j : Nat) :
    textbookDInZF a n i j ∈ L := by
  let params : Tuple ZFSet.{u} 4 :=
    ![a, natCode n, natCode i, natCode j]
  have hspace : textbookTupleSpace a n ∈ L :=
    textbookTupleSpace_mem_L ha n
  apply mem_L_of_delta0_definition params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_L n
      · exact natCode_mem_L i
      · exact natCode_mem_L j)
    TextbookDefFormula.dInMemberDelta
  · intro graph
    change
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          TextbookDefFormula.dInMemberDelta
          ![a, natCode n, natCode i, natCode j, graph] ↔ _
    rw [TextbookDefFormula.satisfies_dInMemberDelta]
    rw [← textbookDInCodeZF_natCode]
    rw [mem_textbookDInCodeZF_iff]
    constructor
    · intro h
      exact ⟨⟨n, rfl⟩, h⟩
    · rintro ⟨_, h⟩
      exact h
  · intro graph hgraph
    exact mem_L_of_mem (textbookDInZF_subset_tupleSpace a n i j hgraph)
      hspace

/-- The atomic equality relation on a finite tuple space is constructible. -/
theorem textbookDEqZF_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n i j : Nat) :
    textbookDEqZF a n i j ∈ L := by
  let params : Tuple ZFSet.{u} 4 :=
    ![a, natCode n, natCode i, natCode j]
  have hspace : textbookTupleSpace a n ∈ L :=
    textbookTupleSpace_mem_L ha n
  apply mem_L_of_delta0_definition params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_L n
      · exact natCode_mem_L i
      · exact natCode_mem_L j)
    TextbookDefFormula.dEqMemberDelta
  · intro graph
    change
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          TextbookDefFormula.dEqMemberDelta
          ![a, natCode n, natCode i, natCode j, graph] ↔ _
    rw [TextbookDefFormula.satisfies_dEqMemberDelta]
    rw [← textbookDEqCodeZF_natCode]
    rw [mem_textbookDEqCodeZF_iff]
    constructor
    · intro h
      exact ⟨⟨n, rfl⟩, h⟩
    · rintro ⟨_, h⟩
      exact h
  · intro graph hgraph
    exact mem_L_of_mem (textbookDEqZF_subset_tupleSpace a n i j hgraph)
      hspace

/-- Relative difference of constructible sets is constructible. -/
theorem relativeDifferenceZF_mem_L
    {space removed : ZFSet.{u}}
    (hspace : space ∈ L) (hremoved : removed ∈ L) :
    relativeDifferenceZF space removed ∈ L := by
  simpa [relativeDifferenceZF, Godel.op, Godel.F1] using
    (Godel.op_mem_L (i := (1 : Fin 9)) hspace hremoved)

/-- Intersection of constructible sets is constructible. -/
theorem intersectionZF_mem_L
    {left right : ZFSet.{u}} (hleft : left ∈ L) (hright : right ∈ L) :
    intersectionZF left right ∈ L := by
  have hleftRight : relativeDifferenceZF left right ∈ L :=
    relativeDifferenceZF_mem_L hleft hright
  have hresult :
      relativeDifferenceZF left (relativeDifferenceZF left right) ∈ L :=
    relativeDifferenceZF_mem_L hleft hleftRight
  have heq :
      relativeDifferenceZF left (relativeDifferenceZF left right) =
        intersectionZF left right := by
    apply ZFSet.ext
    intro x
    simp only [mem_relativeDifferenceZF_iff, mem_intersectionZF_iff]
    tauto
  rwa [heq] at hresult

/-- The textbook existential projection of a constructible relation is
constructible. -/
theorem textbookExistsProjZF_mem_L
    {a relation : ZFSet.{u}} (ha : a ∈ L) (hrelation : relation ∈ L)
    (n : Nat) : textbookExistsProjZF a n relation ∈ L := by
  let params : Tuple ZFSet.{u} 3 := ![a, natCode n, relation]
  have hspace : textbookTupleSpace a n ∈ L :=
    textbookTupleSpace_mem_L ha n
  apply mem_L_of_delta0_definition params (by
      intro k
      fin_cases k
      · exact ha
      · exact natCode_mem_L n
      · exact hrelation)
    TextbookDefFormula.existsProjMemberDelta
  · intro graph
    change
      Delta0Formula.Satisfies Delta0Formula.ZFMem
          TextbookDefFormula.existsProjMemberDelta
          ![a, natCode n, relation, graph] ↔ _
    rw [TextbookDefFormula.satisfies_existsProjMemberDelta]
    rw [← textbookExistsProjCodeZF_natCode]
    rw [mem_textbookExistsProjCodeZF_iff]
    constructor
    · intro h
      exact ⟨⟨n, rfl⟩, h⟩
    · rintro ⟨_, h⟩
      exact h
  · intro graph hgraph
    exact mem_L_of_mem
      (textbookExistsProjZF_subset_tupleSpace a n relation hgraph) hspace

/-! ## Strong induction through the five E clauses -/

/-- Every standard-code value of the textbook enumeration is constructible
when its set parameter is constructible. -/
theorem textbookEZF_natCode_mem_L
    {a : ZFSet.{u}} (ha : a ∈ L) (n m : Nat) :
    textbookEZF a (natCode n) (natCode m) ∈ L := by
  induction m using Nat.strong_induction_on generalizing n with
  | h m ih =>
      cases hdecode : textbookEDecode m with
      | none =>
          rw [textbookEZF_eq_empty_of_decode_none a n m hdecode]
          exact empty_mem_L
      | some fields =>
          rcases fields with ⟨i, j, tag⟩
          have hdecoded :=
            (textbookEDecode_eq_some_iff m i j tag).mp hdecode
          rcases hdecoded with ⟨htag, hm⟩
          subst m
          have hi : i < textbookECode i j tag :=
            textbookECode_index_lt i j tag
          have htagCases :
              tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 := by
            omega
          rcases htagCases with rfl | rfl | rfl | rfl | rfl
          · by_cases hin : i < n
            · by_cases hjn : j < n
              · rw [textbookEZF_code_zero a n i j hin hjn,
                  textbookDInCodeZF_natCode]
                exact textbookDInZF_mem_L ha n i j
              · rw [textbookEZF_code_zero_eq_empty_of_not_lt_right
                  a n i j hjn]
                exact empty_mem_L
            · rw [textbookEZF_code_zero_eq_empty_of_not_lt_left
                a n i j hin]
              exact empty_mem_L
          · by_cases hin : i < n
            · by_cases hjn : j < n
              · rw [textbookEZF_code_one a n i j hin hjn,
                  textbookDEqCodeZF_natCode]
                exact textbookDEqZF_mem_L ha n i j
              · rw [textbookEZF_code_one_eq_empty_of_not_lt_right
                  a n i j hjn]
                exact empty_mem_L
            · rw [textbookEZF_code_one_eq_empty_of_not_lt_left
                a n i j hin]
              exact empty_mem_L
          · rw [textbookEZF_code_two]
            exact relativeDifferenceZF_mem_L
              (textbookTupleSpace_mem_L ha n) (ih i hi n)
          · have hj : j < textbookECode i j 3 := by
              apply lt_of_lt_of_le
                (lt_of_lt_of_le j.lt_two_pow_self
                  (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j))
              simp only [textbookECode]
              have htwo : 0 < 2 ^ i := Nat.pow_pos (by decide)
              have hfive : 0 < 5 ^ 3 := Nat.pow_pos (by decide)
              simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
                Nat.le_mul_of_pos_left (3 ^ j) (Nat.mul_pos htwo hfive)
            rw [textbookEZF_code_three]
            exact intersectionZF_mem_L (ih i hi n) (ih j hj n)
          · rw [textbookEZF_code_four,
              textbookExistsProjCodeZF_natCode]
            exact textbookExistsProjZF_mem_L ha (ih i hi (n + 1)) n

namespace Model

/-- A standard-code `E` value, packaged as an actual member of `L`. -/
def textbookEZFLCarrier
    (U : LCarrier.{u}) (n m : Nat) : LCarrier.{u} :=
  ⟨textbookEZF U.1 (natCode n) (natCode m),
    textbookEZF_natCode_mem_L U.2 n m⟩

@[simp]
theorem textbookEZFLCarrier_val
    (U : LCarrier.{u}) (n m : Nat) :
    (textbookEZFLCarrier U n m).1 =
      textbookEZF U.1 (natCode n) (natCode m) :=
  rfl

end Model

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookEConstructible


