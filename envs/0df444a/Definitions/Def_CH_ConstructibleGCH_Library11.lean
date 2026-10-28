-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library11
-- name    : CH_ConstructibleGCH_Library11
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:35:54.724859+00:00
-- url     : https://prove2.me/theorems/c801c707-5e4a-4674-b34d-749af2c4e07c
-- title:
--   Natural-number literals, addition and E codes
-- statement:
--   Natural-number codes are represented by finite ordinals. This library provides the interfaces for literals, addition and decoding of the arithmetic codes used by the textbook E operations.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookECodeArithmetic.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookECodeDecode.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookNaturalLiterals.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookDefinabilityCode.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookNaturalAddition.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library10
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookECodeArithmetic -/
section GCHSource_Work_CUGCH_TextbookECodeArithmetic
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Arithmetic facts for the textbook enumeration code

Wang, *Axiomatic Set Theory*, Section 6.4 enumerates the five constructors
used to generate definable relations by natural numbers of the form

`2 ^ i * 3 ^ j * 5 ^ tag`.

This file records only the metatheoretic arithmetic facts about that code.
It does not claim that exponentiation, multiplication, or decoding has
already been represented by a first-order formula inside a ZF model.  Those
internal graph formulas and their absoluteness are separate obligations.
-/

section

namespace Constructible

/-- The exact prime-power code used in the five clauses defining `E`. -/
def textbookECode (i j tag : Nat) : Nat :=
  2 ^ i * 3 ^ j * 5 ^ tag





@[simp]
theorem textbookECode_factorization_two (i j tag : Nat) :
    (textbookECode i j tag).factorization 2 = i := by
  simp [textbookECode, Nat.factorization_mul, Nat.prime_two,
    Nat.prime_three, Nat.prime_five]

@[simp]
theorem textbookECode_factorization_three (i j tag : Nat) :
    (textbookECode i j tag).factorization 3 = j := by
  simp [textbookECode, Nat.factorization_mul, Nat.prime_two,
    Nat.prime_three, Nat.prime_five]

@[simp]
theorem textbookECode_factorization_five (i j tag : Nat) :
    (textbookECode i j tag).factorization 5 = tag := by
  simp [textbookECode, Nat.factorization_mul, Nat.prime_two,
    Nat.prime_three, Nat.prime_five]

/-- Unique factorization makes all three fields of the textbook code unique. -/
theorem textbookECode_injective_fields
    {i j tag i' j' tag' : Nat}
    (h : textbookECode i j tag = textbookECode i' j' tag') :
    i = i' /\ j = j' /\ tag = tag' := by
  constructor
  . simpa only [textbookECode_factorization_two] using
      congrArg (fun n : Nat => n.factorization 2) h
  constructor
  . simpa only [textbookECode_factorization_three] using
      congrArg (fun n : Nat => n.factorization 3) h
  . simpa only [textbookECode_factorization_five] using
      congrArg (fun n : Nat => n.factorization 5) h

/-- The recursive reference `i` in every constructor clause is earlier than
the code of that clause.  This is the numerical decrease used by the
well-founded recursion defining `E`. -/
theorem textbookECode_index_lt (i j tag : Nat) :
    i < textbookECode i j tag := by
  have hthree : 0 < 3 ^ j := Nat.pow_pos (by decide)
  have hfive : 0 < 5 ^ tag := Nat.pow_pos (by decide)
  apply lt_of_lt_of_le i.lt_two_pow_self
  simp only [textbookECode]
  simpa only [Nat.mul_assoc] using
    Nat.le_mul_of_pos_right (2 ^ i) (Nat.mul_pos hthree hfive)

end Constructible

end
end GCHSource_Work_CUGCH_TextbookECodeArithmetic


/- Source module: Solutions.Work_CUGCH_TextbookECodeDecode -/
section GCHSource_Work_CUGCH_TextbookECodeDecode
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Metatheoretic decoding of the textbook enumeration code

Wang, *Axiomatic Set Theory*, Section 6.4 uses the five tags `0, ..., 4`
in codes of the form `2 ^ i * 3 ^ j * 5 ^ tag`.  This file supplies a
checked decoder for those natural-number codes.  It first reads the three
prime exponents and then re-encodes them; the latter check rejects zero and
numbers having any additional prime factor.

This is only an auxiliary operation on Lean's metatheoretic type `Nat`.
It is not an internal operation of a ZF model and is never used as though
its graph were automatically available to Separation or Replacement.  The
corresponding object-language graph formula and its absoluteness are proved
separately in `TextbookECodeFormula`.
-/

section

namespace Constructible

/-- Decode an accepted textbook constructor code into its two indices and
one of the five tags.  The re-encoding test is essential: factorization at
`2`, `3`, and `5` alone cannot detect other prime factors. -/
def textbookEDecode (m : Nat) : Option (Nat × Nat × Nat) :=
  let i := m.factorization 2
  let j := m.factorization 3
  let tag := m.factorization 5
  if tag < 5 ∧ m = textbookECode i j tag then
    some (i, j, tag)
  else
    none

/-- The decoder accepts exactly the five tagged textbook codes. -/
theorem textbookEDecode_eq_some_iff (m i j tag : Nat) :
    textbookEDecode m = some (i, j, tag) ↔
      tag < 5 ∧ m = textbookECode i j tag := by
  simp only [textbookEDecode]
  split_ifs with h
  · rcases h with ⟨htag, hcode⟩
    constructor
    · intro hsome
      simp only [Option.some.injEq, Prod.mk.injEq] at hsome
      rcases hsome with ⟨hi, hj, htag'⟩
      subst i
      subst j
      subst tag
      exact ⟨htag, hcode⟩
    · rintro ⟨_, hcode'⟩
      have hfields := textbookECode_injective_fields
        (hcode.symm.trans hcode')
      rcases hfields with ⟨hi, hj, htag'⟩
      simp only [hi, hj, htag']
  · constructor
    · intro hnone
      cases hnone
    · rintro ⟨htag, hcode⟩
      apply (h ?_).elim
      constructor
      · rw [hcode, textbookECode_factorization_five]
        exact htag
      · rw [hcode]
        simp only [textbookECode_factorization_two,
          textbookECode_factorization_three, textbookECode_factorization_five]

/-- Every valid textbook code decodes to the fields from which it was made. -/
@[simp]
theorem textbookEDecode_textbookECode (i j tag : Nat) (htag : tag < 5) :
    textbookEDecode (textbookECode i j tag) = some (i, j, tag) := by
  rw [textbookEDecode_eq_some_iff]
  exact ⟨htag, rfl⟩

@[simp]
theorem textbookEDecode_code_zero (i j : Nat) :
    textbookEDecode (textbookECode i j 0) = some (i, j, 0) := by
  exact textbookEDecode_textbookECode i j 0 (by decide)

@[simp]
theorem textbookEDecode_code_one (i j : Nat) :
    textbookEDecode (textbookECode i j 1) = some (i, j, 1) := by
  exact textbookEDecode_textbookECode i j 1 (by decide)

@[simp]
theorem textbookEDecode_code_two (i j : Nat) :
    textbookEDecode (textbookECode i j 2) = some (i, j, 2) := by
  exact textbookEDecode_textbookECode i j 2 (by decide)

@[simp]
theorem textbookEDecode_code_three (i j : Nat) :
    textbookEDecode (textbookECode i j 3) = some (i, j, 3) := by
  exact textbookEDecode_textbookECode i j 3 (by decide)

@[simp]
theorem textbookEDecode_code_four (i j : Nat) :
    textbookEDecode (textbookECode i j 4) = some (i, j, 4) := by
  exact textbookEDecode_textbookECode i j 4 (by decide)



end Constructible

end
end GCHSource_Work_CUGCH_TextbookECodeDecode


/- Source module: Solutions.Work_CUGCH_TextbookNaturalLiterals -/
section GCHSource_Work_CUGCH_TextbookNaturalLiterals
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Bounded formulas for standard finite ordinals

This file provides the natural-number literals needed by the textbook
enumeration of definable relations.  The literal for zero says that its
designated coordinate has no members.  Recursively, the literal for `k + 1`
chooses, bounded by that coordinate, a predecessor satisfying the literal for
`k` and asserts that the coordinate is its von Neumann successor.

Consequently every quantifier is bounded.  These formulas do not define
addition or multiplication, and their semantics refers to the standard
von Neumann codes `natCode k`.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

namespace Delta0Formula

/-- `emptyDeltaAt i` says that coordinate `i` has no members. -/
def emptyDeltaAt {n : Nat} (i : Fin n) : Delta0Formula n :=
  .boundedAll i (.neg (.eq (Fin.last n) (Fin.last n)))

/-- Ambient semantics of the bounded empty-set formula. -/
@[simp]
theorem satisfies_emptyDeltaAt {n : Nat} (i : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (emptyDeltaAt i) s <->
      s i = (∅ : ZFSet.{u}) := by
  simp only [emptyDeltaAt, satisfies_boundedAll, Satisfies,
    snoc_last]
  constructor
  · intro h
    apply ZFSet.eq_empty _ |>.mpr
    intro x hx
    exact h x hx True.intro
  · intro hzero x hx _htrue
    rw [hzero] at hx
    exact ZFSet.notMem_empty x hx

/--
The bounded formula saying that coordinate `i` is the standard von Neumann
ordinal `k`.  In the successor clause the predecessor witness is bounded by
the proposed successor itself.
-/
def natLiteralDeltaAt : (k : Nat) -> {n : Nat} ->
    Fin n -> Delta0Formula n
  | 0, _, i => emptyDeltaAt i
  | k + 1, n, i =>
      .boundedEx i
        (.conj
          (natLiteralDeltaAt k (Fin.last n))
          (successorAt i.castSucc (Fin.last n)))

/-- Ambient semantics of a bounded standard-natural-number literal. -/
@[simp]
theorem satisfies_natLiteralDeltaAt (k : Nat) {n : Nat} (i : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (natLiteralDeltaAt k i) s <->
      s i = (natCode k : ZFSet.{u}) := by
  induction k generalizing n with
  | zero =>
      rw [natLiteralDeltaAt, satisfies_emptyDeltaAt]
      simp only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero]
  | succ k ih =>
      simp only [natLiteralDeltaAt, Satisfies, ih,
        satisfies_successorAt, snoc_last, snoc_castSucc]
      constructor
      · rintro ⟨x, _hx, rfl, hsuccessor⟩
        exact hsuccessor.trans (natCode_succ_eq_insert k).symm
      · intro hsuccessor
        refine ⟨(natCode k : ZFSet.{u}), ?_, rfl, ?_⟩
        · rw [hsuccessor, natCode_succ_eq_insert]
          exact ZFSet.mem_insert_iff.mpr (Or.inl rfl)
        · exact hsuccessor.trans (natCode_succ_eq_insert k)

/-- Ambient first-order semantics after forgetting boundedness annotations. -/
@[simp]
theorem satisfies_natLiteralDeltaAt_toFO (k : Nat) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies ZFMem (natLiteralDeltaAt k i).toFO s <->
      s i = (natCode k : ZFSet.{u}) := by
  rw [satisfies_toFO, satisfies_natLiteralDeltaAt]

end Delta0Formula

namespace Model

noncomputable section

/-- Every standard natural-number code belongs to a transitive ZF model. -/
theorem natCode_mem_of_isTransitiveZFModel {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (k : Nat) :
    (natCode k : ZFSet.{u}) ∈ M := by
  simpa only [natCode] using
    natOrdinal_mem_of_isTransitiveZFModel hM k

/--
Restricted satisfaction over any transitive set has exactly the same
standard-literal semantics, provided every free coordinate lies in the set.
-/
theorem satisfiesIn_natLiteralDeltaAt_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) (k : Nat)
    {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (Delta0Formula.natLiteralDeltaAt k i).toFO s <->
      s i = (natCode k : ZFSet.{u}) := by
  rw [satisfiesIn_delta0_iff hM
      (Delta0Formula.natLiteralDeltaAt k i) s hs,
    Delta0Formula.satisfies_natLiteralDeltaAt_toFO]

end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookNaturalLiterals


/- Source module: Solutions.Work_CUGCH_TextbookDefinabilityCode -/
section GCHSource_Work_CUGCH_TextbookDefinabilityCode
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Set-coded indices for the textbook definability operations

The core definitions in `TextbookDefinability` use Lean natural numbers for
their finite arities and indices.  The textbook absoluteness argument also
needs ambient, meta-level total functions whose arguments are sets.  This
file supplies that intermediate, set-coded interface.  It does not yet supply
internal function graphs, first-order definitions, or absoluteness proofs.

Each arity, coordinate-index, or stage argument is decoded only when it is a
member of the standard von Neumann `omega`; the set and relation arguments
remain arbitrary.  Operations return the empty set when a coded argument is
invalid.  On standard codes the definitions reduce exactly to the
`Nat`-indexed core; no internal formula or absoluteness claim is made here.
-/

section

universe u

namespace Constructible

open FiniteSequenceZF

/-! ## Decoding standard natural-number sets -/

/-- Decode a member of the ambient standard von Neumann `omega`, and reject
every other set.  The chosen witness is unique by injectivity of `natCode`.
This meta-level decoder must not be used as an internal definition in a
nontransitive model; later absoluteness arguments explicitly prove that a
transitive ZF model's internally defined omega is this ambient omega. -/
noncomputable def textbookNatDecode (x : ZFSet.{u}) : Option Nat :=
  by
    classical
    exact if hx : x ∈ Ordinal.omega0.toZFSet then
      some (Classical.choose
        (IndexedSequenceZF.mem_omega_iff_exists_natCode x |>.mp hx))
    else
      none

theorem textbookNatDecode_eq_some_iff {x : ZFSet.{u}} {n : Nat} :
    textbookNatDecode x = some n ↔ x = natCode n := by
  unfold textbookNatDecode
  split_ifs with hx
  · let k := Classical.choose
      (IndexedSequenceZF.mem_omega_iff_exists_natCode x |>.mp hx)
    have hk : x = natCode k :=
      Classical.choose_spec
        (IndexedSequenceZF.mem_omega_iff_exists_natCode x |>.mp hx)
    constructor
    · intro h
      have hkn : k = n := Option.some.inj h
      simpa only [hkn] using hk
    · intro hxn
      apply congrArg some
      apply natCode_injective
      rw [← hk, hxn]
  · constructor
    · intro h
      cases h
    · intro hxn
      exfalso
      apply hx
      rw [hxn]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode n)).mpr ⟨n, rfl⟩

@[simp]
theorem textbookNatDecode_natCode (n : Nat) :
    textbookNatDecode (natCode n : ZFSet.{u}) = some n :=
  textbookNatDecode_eq_some_iff.mpr rfl

theorem textbookNatDecode_eq_none_iff {x : ZFSet.{u}} :
    textbookNatDecode x = none ↔ x ∉ Ordinal.omega0.toZFSet := by
  constructor
  · intro hdecode hx
    rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hx with
      ⟨n, rfl⟩
    simp at hdecode
  · intro hx
    simp only [textbookNatDecode]
    exact dif_neg hx



/-! ## Total set-coded operations -/

/-- The finite power `a^n`, totalized to the empty set off `omega`. -/
noncomputable def textbookTupleSpaceCodeZF
    (a n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookTupleSpace a n'
  | none => ∅

/-- The set-coded version of `D_in(a,n,i,j)`. -/
noncomputable def textbookDInCodeZF
    (a n i j : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n, textbookNatDecode i, textbookNatDecode j with
  | some n', some i', some j' => textbookDInZF a n' i' j'
  | _, _, _ => ∅

/-- The set-coded version of `D_eq(a,n,i,j)`. -/
noncomputable def textbookDEqCodeZF
    (a n i j : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n, textbookNatDecode i, textbookNatDecode j with
  | some n', some i', some j' => textbookDEqZF a n' i' j'
  | _, _, _ => ∅

/-- The set-coded existential projection. -/
noncomputable def textbookExistsProjCodeZF
    (a n r : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookExistsProjZF a n' r
  | none => ∅

/-- The set-coded atomic stage `D(0,a,n)`. -/
noncomputable def textbookDZeroCodeZF
    (a n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookDZeroZF a n'
  | none => ∅

/-- The set-coded finite stage `D(k,a,n)`. -/
noncomputable def textbookDStageCodeZF
    (a k n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode k, textbookNatDecode n with
  | some k', some n' => textbookDStageZF a k' n'
  | _, _ => ∅

/-- The set-coded union `Df(a,n)` of all finite stages. -/
noncomputable def textbookDfCodeZF
    (a n : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode n with
  | some n' => textbookDfZF a n'
  | none => ∅

@[simp]
theorem textbookTupleSpaceCodeZF_natCode (a : ZFSet.{u}) (n : Nat) :
    textbookTupleSpaceCodeZF a (natCode n) = textbookTupleSpace a n := by
  simp [textbookTupleSpaceCodeZF]

@[simp]
theorem textbookDInCodeZF_natCode
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDInCodeZF a (natCode n) (natCode i) (natCode j) =
      textbookDInZF a n i j := by
  simp [textbookDInCodeZF]

@[simp]
theorem textbookDEqCodeZF_natCode
    (a : ZFSet.{u}) (n i j : Nat) :
    textbookDEqCodeZF a (natCode n) (natCode i) (natCode j) =
      textbookDEqZF a n i j := by
  simp [textbookDEqCodeZF]

@[simp]
theorem textbookExistsProjCodeZF_natCode
    (a r : ZFSet.{u}) (n : Nat) :
    textbookExistsProjCodeZF a (natCode n) r =
      textbookExistsProjZF a n r := by
  simp [textbookExistsProjCodeZF]

@[simp]
theorem textbookDZeroCodeZF_natCode (a : ZFSet.{u}) (n : Nat) :
    textbookDZeroCodeZF a (natCode n) = textbookDZeroZF a n := by
  simp [textbookDZeroCodeZF]

@[simp]
theorem textbookDStageCodeZF_natCode
    (a : ZFSet.{u}) (k n : Nat) :
    textbookDStageCodeZF a (natCode k) (natCode n) =
      textbookDStageZF a k n := by
  simp [textbookDStageCodeZF]

@[simp]
theorem textbookDfCodeZF_natCode (a : ZFSet.{u}) (n : Nat) :
    textbookDfCodeZF a (natCode n) = textbookDfZF a n := by
  simp [textbookDfCodeZF]

@[simp]
theorem textbookTupleSpaceCodeZF_eq_empty_of_not_mem_omega
    {a n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookTupleSpaceCodeZF a n = ∅ := by
  simp [textbookTupleSpaceCodeZF,
    textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDInCodeZF_eq_empty_of_arity_not_mem_omega
    {a n i j : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDInCodeZF a n i j = ∅ := by
  simp [textbookDInCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDInCodeZF_eq_empty_of_left_not_mem_omega
    {a n i j : ZFSet.{u}} (hi : i ∉ Ordinal.omega0.toZFSet) :
    textbookDInCodeZF a n i j = ∅ := by
  simp [textbookDInCodeZF, textbookNatDecode_eq_none_iff.mpr hi]

@[simp]
theorem textbookDInCodeZF_eq_empty_of_right_not_mem_omega
    {a n i j : ZFSet.{u}} (hj : j ∉ Ordinal.omega0.toZFSet) :
    textbookDInCodeZF a n i j = ∅ := by
  simp [textbookDInCodeZF, textbookNatDecode_eq_none_iff.mpr hj]

@[simp]
theorem textbookDEqCodeZF_eq_empty_of_arity_not_mem_omega
    {a n i j : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDEqCodeZF a n i j = ∅ := by
  simp [textbookDEqCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDEqCodeZF_eq_empty_of_left_not_mem_omega
    {a n i j : ZFSet.{u}} (hi : i ∉ Ordinal.omega0.toZFSet) :
    textbookDEqCodeZF a n i j = ∅ := by
  simp [textbookDEqCodeZF, textbookNatDecode_eq_none_iff.mpr hi]

@[simp]
theorem textbookDEqCodeZF_eq_empty_of_right_not_mem_omega
    {a n i j : ZFSet.{u}} (hj : j ∉ Ordinal.omega0.toZFSet) :
    textbookDEqCodeZF a n i j = ∅ := by
  simp [textbookDEqCodeZF, textbookNatDecode_eq_none_iff.mpr hj]

@[simp]
theorem textbookExistsProjCodeZF_eq_empty_of_not_mem_omega
    {a n r : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookExistsProjCodeZF a n r = ∅ := by
  simp [textbookExistsProjCodeZF,
    textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDZeroCodeZF_eq_empty_of_not_mem_omega
    {a n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDZeroCodeZF a n = ∅ := by
  simp [textbookDZeroCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDStageCodeZF_eq_empty_of_stage_not_mem_omega
    {a k n : ZFSet.{u}} (hk : k ∉ Ordinal.omega0.toZFSet) :
    textbookDStageCodeZF a k n = ∅ := by
  simp [textbookDStageCodeZF, textbookNatDecode_eq_none_iff.mpr hk]

@[simp]
theorem textbookDStageCodeZF_eq_empty_of_arity_not_mem_omega
    {a k n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDStageCodeZF a k n = ∅ := by
  simp [textbookDStageCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

@[simp]
theorem textbookDfCodeZF_eq_empty_of_not_mem_omega
    {a n : ZFSet.{u}} (hn : n ∉ Ordinal.omega0.toZFSet) :
    textbookDfCodeZF a n = ∅ := by
  simp [textbookDfCodeZF, textbookNatDecode_eq_none_iff.mpr hn]

end Constructible

end
end GCHSource_Work_CUGCH_TextbookDefinabilityCode


/- Source module: Solutions.Work_CUGCH_TextbookNaturalAddition -/
section GCHSource_Work_CUGCH_TextbookNaturalAddition
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# The set-theoretic graph of addition on the standard natural numbers

This file defines addition without adding an arithmetic symbol to the
language of set theory.  The formula says that a finite function graph starts
at `x`, is closed under von Neumann successor along the indices below `y`,
and has value `z` at `y`.  Its free-variable layout is `[omega, x, y, z]`.

The use of Lean's `Nat.add` below is confined to the canonical witness and to
the metatheoretic statement of the semantics.  The defining formula itself
uses only equality and membership.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace TextbookNatFormula

/-! ## The bounded finite-recursion body -/

/--
The transition clause for a graph with layout
`[omega, x, y, z, ySucc, graph]`.

For every `k ∈ y`, it chooses `kSucc = k ∪ {k}` and graph values at `k`
and `kSucc`, and requires the latter value to be the successor of the former.
-/
def natAddTransitionDeltaAt {n : Nat}
    (omega y ySucc graph : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedAll y
    (Delta0Formula.boundedEx ySucc.castSucc
      (.conj
        (Delta0Formula.successorAt
          (Fin.last (n + 1)) (Fin.last n).castSucc)
        (Delta0Formula.boundedEx omega.castSucc.castSucc
          (.conj
            (TextbookDefFormula.graphValueDeltaAt
              graph.castSucc.castSucc.castSucc
              (Fin.last n).castSucc.castSucc
              (Fin.last (n + 2)))
            (Delta0Formula.boundedEx omega.castSucc.castSucc.castSucc
              (.conj
                (TextbookDefFormula.graphValueDeltaAt
                  graph.castSucc.castSucc.castSucc.castSucc
                  (Fin.last (n + 1)).castSucc.castSucc
                  (Fin.last (n + 3)))
                (Delta0Formula.successorAt
                  (Fin.last (n + 3))
                  (Fin.last (n + 2)).castSucc)))))))

/-- Fixed layout `[omega, x, y, z, ySucc, graph]`. -/
def natAddTransitionDelta : Delta0Formula 6 :=
  natAddTransitionDeltaAt
    (0 : Fin 6) (2 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/--
The complete bounded condition on `[omega, x, y, z, ySucc, graph]`:
`graph : ySucc → omega`, its zero value is `x`, its `y` value is `z`, and
successive indices have successive values.
-/
def natAddGraphDeltaAt {n : Nat}
    (omega x y z ySucc graph : Fin n) : Delta0Formula n :=
  .conj
    (TextbookDefFormula.isFunctionDeltaAt
      graph ySucc omega)
    (.conj
      (Delta0Formula.boundedEx ySucc
        (.conj
          (Delta0Formula.emptyDeltaAt (Fin.last n))
          (TextbookDefFormula.graphValueDeltaAt
            graph.castSucc (Fin.last n) x.castSucc)))
      (.conj
        (TextbookDefFormula.graphValueDeltaAt
          graph y z)
        (natAddTransitionDeltaAt omega y ySucc graph)))

/-- Fixed layout `[omega, x, y, z, ySucc, graph]`. -/
def natAddGraphDelta : Delta0Formula 6 :=
  natAddGraphDeltaAt
    (0 : Fin 6) (1 : Fin 6) (2 : Fin 6)
    (3 : Fin 6) (4 : Fin 6) (5 : Fin 6)

/--
Pure membership-language formula for natural-number addition.  The free
layout is `[omega, x, y, z]`.  The first conjunct identifies `omega` as the
least inductive set, so this is not merely addition relative to an arbitrary
set called `omega`.
-/
def natAddFormula : FOFormula 4 :=
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
              (.ex natAddGraphDelta.toFO))))))

/-! ## Ambient semantics of the bounded body -/

@[simp]
theorem satisfies_natAddTransitionDeltaAt {n : Nat}
    (omega y ySucc graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (natAddTransitionDeltaAt omega y ySucc graph) s <->
      forall k, k ∈ s y ->
        insert k k ∈ s ySucc /\
          exists value, value ∈ s omega /\
            ZFSet.pair k value ∈ s graph /\
            insert value value ∈ s omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ s graph := by
  simp [natAddTransitionDeltaAt]

@[simp]
theorem satisfies_natAddTransitionDelta
    (omega x y z ySucc graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natAddTransitionDelta
        ![omega, x, y, z, ySucc, graph] <->
      forall k, k ∈ y ->
        insert k k ∈ ySucc /\
          exists value, value ∈ omega /\
            ZFSet.pair k value ∈ graph /\
            insert value value ∈ omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ graph := by
  simp [natAddTransitionDelta]

@[simp]
theorem satisfies_natAddGraphDeltaAt {n : Nat}
    (omega x y z ySucc graph : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (natAddGraphDeltaAt omega x y z ySucc graph) s <->
      ZFSet.IsFunc (s ySucc) (s omega) (s graph) /\
      ((∅ : ZFSet.{u}) ∈ s ySucc /\ ZFSet.pair ∅ (s x) ∈ s graph) /\
      ZFSet.pair (s y) (s z) ∈ s graph /\
      (forall k, k ∈ s y ->
        insert k k ∈ s ySucc /\
          exists value, value ∈ s omega /\
            ZFSet.pair k value ∈ s graph /\
            insert value value ∈ s omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ s graph) := by
  simp [natAddGraphDeltaAt]

@[simp]
theorem satisfies_natAddGraphDelta
    (omega x y z ySucc graph : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
        ![omega, x, y, z, ySucc, graph] <->
      ZFSet.IsFunc ySucc omega graph /\
      ((∅ : ZFSet.{u}) ∈ ySucc /\ ZFSet.pair ∅ x ∈ graph) /\
      ZFSet.pair y z ∈ graph /\
      (forall k, k ∈ y ->
        insert k k ∈ ySucc /\
          exists value, value ∈ omega /\
            ZFSet.pair k value ∈ graph /\
            insert value value ∈ omega /\
            ZFSet.pair (insert k k) (insert value value) ∈ graph) := by
  simp [natAddGraphDelta]

/-! ## Ambient semantics of the standard-omega guard -/

@[simp]
theorem satisfies_transitiveZFEmptyAt_ambient {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.transitiveZFEmptyAt i) s <->
      s i = (∅ : ZFSet.{u}) := by
  simp only [Model.transitiveZFEmptyAt, FOFormula.satisfies_all,
    FOFormula.Satisfies, snoc_last, snoc_castSucc]
  constructor
  · intro h
    exact ZFSet.eq_empty _ |>.mpr (fun x hx => h x hx)
  · intro hempty x hx
    rw [hempty] at hx
    exact ZFSet.notMem_empty x hx

@[simp]
theorem satisfies_transitiveZFSuccessorAt_ambient {n : Nat}
    (successor index : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.transitiveZFSuccessorAt successor index) s <->
      s successor = insert (s index) (s index) := by
  simp only [Model.transitiveZFSuccessorAt, FOFormula.Satisfies,
    FOFormula.satisfies_all, FOFormula.satisfies_imp,
    FOFormula.satisfies_disj, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hindex, hforward, hbackward⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      rcases hforward z hz with hzIndex | hzEq
      · exact Or.inr hzIndex
      · exact Or.inl hzEq
    · rintro (rfl | hz)
      · exact hindex
      · exact hbackward z hz
  · intro hsuccessor
    rw [hsuccessor]
    refine ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl), ?_, ?_⟩
    · intro z hz
      rcases ZFSet.mem_insert_iff.mp hz with hzEq | hzIndex
      · exact Or.inr hzEq
      · exact Or.inl hzIndex
    · intro z hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr hz)

@[simp]
theorem satisfies_transitiveZFInductiveAt_ambient {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.transitiveZFInductiveAt i) s <->
      (∅ : ZFSet.{u}) ∈ s i /\
        forall x, x ∈ s i -> insert x x ∈ s i := by
  simp [Model.transitiveZFInductiveAt]

theorem ambient_inductive_contains_natCode
    {w : ZFSet.{u}}
    (hw : (∅ : ZFSet.{u}) ∈ w /\
      forall x, x ∈ w -> insert x x ∈ w) :
    forall n : Nat, (natCode n : ZFSet.{u}) ∈ w := by
  intro n
  induction n with
  | zero =>
      simpa only [natCode, Nat.cast_zero, Ordinal.toZFSet_zero] using hw.1
  | succ n ih =>
      rw [natCode_succ_eq_insert]
      exact hw.2 (natCode n) ih

@[simp]
theorem satisfies_standardOmegaAt_ambient_iff {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (Model.standardOmegaAt i) s <->
      s i = Ordinal.omega0.toZFSet := by
  rw [Model.standardOmegaAt]
  simp only [FOFormula.Satisfies, FOFormula.satisfies_all,
    FOFormula.satisfies_imp, FOFormula.satisfies_boundedAll,
    satisfies_transitiveZFInductiveAt_ambient,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hinductive, hminimal⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      exact hminimal Ordinal.omega0.toZFSet
        (by
          constructor
          · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode ∅).mpr
              ⟨0, by simp [natCode]⟩
          · intro x hx
            rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hx with
              ⟨k, rfl⟩
            rw [← natCode_succ_eq_insert]
            exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
              (natCode (k + 1))).mpr ⟨k + 1, rfl⟩) z hz
    · intro hz
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode z).mp hz with
        ⟨k, rfl⟩
      exact ambient_inductive_contains_natCode hinductive k
  · intro homega
    rw [homega]
    constructor
    · constructor
      · exact (IndexedSequenceZF.mem_omega_iff_exists_natCode ∅).mpr
          ⟨0, by simp [natCode]⟩
      · intro x hx
        rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode x).mp hx with
          ⟨k, rfl⟩
        rw [← natCode_succ_eq_insert]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (k + 1))).mpr ⟨k + 1, rfl⟩
    · intro w hw z hz
      rcases (IndexedSequenceZF.mem_omega_iff_exists_natCode z).mp hz with
        ⟨k, rfl⟩
      exact ambient_inductive_contains_natCode hw k

/-! ## Canonical finite graphs -/

/-- The canonical tuple `k ↦ natCode (a + k)` of length `b + 1`. -/
noncomputable def natAddCanonicalTuple (a b : Nat) :
    Tuple (ZFCarrier (Ordinal.omega0.toZFSet : ZFSet.{u})) (b + 1) :=
  fun i =>
    ⟨natCode (a + i.1),
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a + i.1))).mpr ⟨a + i.1, rfl⟩⟩

/-- The Kuratowski graph of the canonical addition recursion. -/
noncomputable def natAddCanonicalGraph (a b : Nat) : ZFSet.{u} :=
  textbookTupleGraph (natAddCanonicalTuple a b)

theorem natAddCanonicalGraph_isFunc (a b : Nat) :
    ZFSet.IsFunc (natCode (b + 1)) Ordinal.omega0.toZFSet
      (natAddCanonicalGraph a b) := by
  exact textbookTupleGraph_isFunc (natAddCanonicalTuple a b)



@[simp]
theorem natAddCanonicalGraph_value (a b : Nat) (i : Fin (b + 1)) :
    ZFSet.pair (natCode i.1) (natCode (a + i.1)) ∈
      natAddCanonicalGraph a b := by
  exact textbookTupleGraph_value
    (natAddCanonicalTuple a b) i

theorem natAddCanonicalGraph_satisfies (a b : Nat) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
      ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
        natCode (a + b), natCode (b + 1), natAddCanonicalGraph a b] := by
  rw [satisfies_natAddGraphDelta]
  refine ⟨natAddCanonicalGraph_isFunc a b, ?_, ?_, ?_⟩
  · constructor
    · apply (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (∅ : ZFSet.{u}) (b + 1)).mpr
      exact ⟨0, Nat.zero_lt_succ b, by simp [natCode]⟩
    · simpa [natCode] using
        (natAddCanonicalGraph_value a b ⟨0, Nat.zero_lt_succ b⟩)
  · simpa using
      (natAddCanonicalGraph_value a b ⟨b, Nat.lt_succ_self b⟩)
  · intro k hk
    rcases (IndexedSequenceZF.mem_natCode_iff_exists_lt k b).mp hk with
      ⟨j, hj, rfl⟩
    constructor
    · rw [← natCode_succ_eq_insert]
      exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
        (natCode (j + 1)) (b + 1)).mpr
          ⟨j + 1, Nat.succ_lt_succ hj, rfl⟩
    · refine ⟨natCode (a + j),
        (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (a + j))).mpr ⟨a + j, rfl⟩, ?_, ?_, ?_⟩
      · exact natAddCanonicalGraph_value a b ⟨j, hj.trans (Nat.lt_succ_self b)⟩
      · rw [← natCode_succ_eq_insert]
        exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
          (natCode (a + j + 1))).mpr ⟨a + j + 1, rfl⟩
      · rw [← natCode_succ_eq_insert, ← natCode_succ_eq_insert]
        simpa [Nat.add_assoc] using natAddCanonicalGraph_value a b
          ⟨j + 1, Nat.succ_lt_succ hj⟩

/-! ## Uniqueness of the finite recursion -/

theorem natAddGraphDelta_output_unique
    (a b : Nat) (z ySucc graph : ZFSet.{u})
    (hySucc : ySucc = natCode (b + 1))
    (hgraph :
      Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b,
          z, ySucc, graph]) :
    z = natCode (a + b) := by
  rw [satisfies_natAddGraphDelta] at hgraph
  rcases hgraph with ⟨hfunc, hzero, hyValue, hstep⟩
  have hvalues : forall j : Nat, j <= b ->
      ZFSet.pair (natCode j) (natCode (a + j)) ∈ graph := by
    intro j hj
    induction j with
    | zero =>
        simpa [natCode] using hzero.2
    | succ j ih =>
        have hjb : j < b := Nat.lt_of_succ_le hj
        have hjDomain : (natCode j : ZFSet.{u}) ∈ ySucc := by
          rw [hySucc]
          exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
            (natCode j) (b + 1)).mpr
              ⟨j, hjb.trans (Nat.lt_succ_self b), rfl⟩
        rcases hfunc.2 (natCode j) hjDomain with
          ⟨output, _houtput, hunique⟩
        rcases hstep (natCode j)
            ((IndexedSequenceZF.mem_natCode_iff_exists_lt
              (natCode j) b).mpr ⟨j, hjb, rfl⟩) with
          ⟨_hnextDomain, value, _hvalueOmega, hvalue,
            _hnextOmega, hnext⟩
        have hprevious := ih (Nat.le_of_lt hjb)
        have hvalueEq : value = natCode (a + j) :=
          (hunique value hvalue).trans
            (hunique (natCode (a + j)) hprevious).symm
        rw [hvalueEq, ← natCode_succ_eq_insert,
          ← natCode_succ_eq_insert] at hnext
        simpa [Nat.add_assoc] using hnext
  have hbDomain : (natCode b : ZFSet.{u}) ∈ ySucc := by
    rw [hySucc]
    exact (IndexedSequenceZF.mem_natCode_iff_exists_lt
      (natCode b) (b + 1)).mpr ⟨b, Nat.lt_succ_self b, rfl⟩
  rcases hfunc.2 (natCode b) hbDomain with
    ⟨output, _houtput, hunique⟩
  exact (hunique z hyValue).trans
    (hunique (natCode (a + b)) (hvalues b le_rfl)).symm

@[simp]
theorem satisfies_natAddFormula_ambient
    (omega x y z : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
        ![omega, x, y, z] <->
      omega = Ordinal.omega0.toZFSet /\
      x ∈ omega /\ y ∈ omega /\ z ∈ omega /\
      exists ySucc, ySucc = insert y y /\
        exists graph,
          Delta0Formula.Satisfies Delta0Formula.ZFMem natAddGraphDelta
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
          FOFormula.Satisfies Delta0Formula.ZFMem natAddGraphDelta.toFO
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
    rw [Delta0Formula.satisfies_toFO, hassign] at hgraphFormula
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
      rw [Delta0Formula.satisfies_toFO, hassign]
      exact hgraph

@[simp]
theorem satisfies_natAddFormula_natCode_iff
    (a b : Nat) (z : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem natAddFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] <->
      z = natCode (a + b) := by
  rw [satisfies_natAddFormula_ambient]
  constructor
  · rintro ⟨_homega, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySucc, graph, hgraph⟩
    apply natAddGraphDelta_output_unique a b z ySucc graph
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
        (natCode (a + b))).mpr ⟨a + b, rfl⟩,
      natCode (b + 1), ?_, natAddCanonicalGraph a b, ?_⟩
    · exact (natCode_succ_eq_insert b)
    · exact natAddCanonicalGraph_satisfies a b

/-! ## Restricted semantics in transitive ZF models -/

theorem satisfiesIn_natAddFormula_natCode_iff
    {M : ZFSet.{u}} (hM : Model.IsTransitiveZFModel M)
    (a b : Nat) {z : ZFSet.{u}} (hzM : z ∈ M) :
    Model.SatisfiesIn (M : Set ZFSet.{u}) natAddFormula
        ![(Ordinal.omega0.toZFSet : ZFSet.{u}), natCode a, natCode b, z] <->
      z = natCode (a + b) := by
  let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
  let s : Tuple ZFSet.{u} 4 := ![omega, natCode a, natCode b, z]
  have homegaM : omega ∈ M :=
    Model.omega_toZFSet_mem_of_isTransitiveZFModel hM
  have haM : (natCode a : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM a
  have hbM : (natCode b : ZFSet.{u}) ∈ M :=
    Model.natCode_mem_of_isTransitiveZFModel hM b
  have hsM : forall i, s i ∈ M := by
    intro i
    fin_cases i
    · exact homegaM
    · exact haM
    · exact hbM
    · exact hzM
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
          Model.SatisfiesIn (M : Set ZFSet.{u}) natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph)) <-> _)
  constructor
  · rintro ⟨homegaFormula, _haOmega, _hbOmega, _hzOmega,
      ySucc, hySuccM, hySuccFormula, graph, hgraphM, hgraphFormula⟩
    have _homega : s (0 : Fin 4) = Ordinal.omega0.toZFSet :=
      (Model.satisfiesIn_standardOmegaAt_iff hM
        (0 : Fin 4) s hsM).mp homegaFormula
    have hsuccAssign : snoc s ySucc =
        ![omega, natCode a, natCode b, z, ySucc] := by
      funext i
      fin_cases i <;> rfl
    have hsuccAssignM : forall i, snoc s ySucc i ∈ M := by
      rw [hsuccAssign]
      intro i
      fin_cases i
      · exact homegaM
      · exact haM
      · exact hbM
      · exact hzM
      · exact hySuccM
    have hySuccAmbient :=
      (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s ySucc) hsuccAssignM).mp hySuccFormula
    rw [Delta0Formula.satisfies_toFO,
      Delta0Formula.satisfies_successorAt] at hySuccAmbient
    have hySucc : ySucc = natCode (b + 1) := by
      have hraw : ySucc = insert (natCode b) (natCode b) := by
        rw [hsuccAssign] at hySuccAmbient
        simpa using hySuccAmbient
      exact hraw.trans (natCode_succ_eq_insert b).symm
    have hassign : snoc (snoc s ySucc) graph =
        ![omega, natCode a, natCode b, z, ySucc, graph] := by
      funext i
      fin_cases i <;> rfl
    have hgraphAssignM : forall i,
        snoc (snoc s ySucc) graph i ∈ M := by
      rw [hassign]
      intro i
      fin_cases i
      · exact homegaM
      · exact haM
      · exact hbM
      · exact hzM
      · exact hySuccM
      · exact hgraphM
    have hgraphAbsolute :
        Model.SatisfiesIn (M : Set ZFSet.{u}) natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph) <->
          FOFormula.Satisfies Delta0Formula.ZFMem natAddGraphDelta.toFO
            (snoc (snoc s ySucc) graph) :=
      Model.satisfiesIn_delta0_iff hM.1 natAddGraphDelta
        (snoc (snoc s ySucc) graph) hgraphAssignM
    have hgraphAmbient := hgraphAbsolute.mp hgraphFormula
    rw [Delta0Formula.satisfies_toFO] at hgraphAmbient
    rw [hassign] at hgraphAmbient
    have hresult := natAddGraphDelta_output_unique
      a b z ySucc graph hySucc hgraphAmbient
    exact hresult
  · intro hz
    have hzEq : z = (natCode (a + b) : ZFSet.{u}) := hz
    have hySuccM : (natCode (b + 1) : ZFSet.{u}) ∈ M :=
      Model.natCode_mem_of_isTransitiveZFModel hM (b + 1)
    have hcanonicalFunc := natAddCanonicalGraph_isFunc a b
    have hgraphM : natAddCanonicalGraph a b ∈ M :=
      Model.finiteIsFunc_mem_of_isTransitiveZFModel
        hM homegaM hcanonicalFunc
    refine ⟨(Model.satisfiesIn_standardOmegaAt_iff hM
      (0 : Fin 4) s hsM).mpr rfl,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode a)).mpr ⟨a, rfl⟩,
      (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode b)).mpr ⟨b, rfl⟩, ?_,
      natCode (b + 1), hySuccM, ?_,
      natAddCanonicalGraph a b, hgraphM, ?_⟩
    · rw [hzEq]
      exact (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (natCode (a + b))).mpr ⟨a + b, rfl⟩
    · have hsuccAssign : snoc s (natCode (b + 1)) =
          ![omega, natCode a, natCode b, z, natCode (b + 1)] := by
        funext i
        fin_cases i <;> rfl
      have hsuccAssignM : forall i,
          snoc s (natCode (b + 1)) i ∈ M := by
        rw [hsuccAssign]
        intro i
        fin_cases i
        · exact homegaM
        · exact haM
        · exact hbM
        · exact hzM
        · exact hySuccM
      apply (Model.satisfiesIn_delta0_iff hM.1
        (Delta0Formula.successorAt
          (Fin.last 4) (2 : Fin 4).castSucc)
        (snoc s (natCode (b + 1))) hsuccAssignM).mpr
      rw [Delta0Formula.satisfies_toFO,
        Delta0Formula.satisfies_successorAt]
      rw [hsuccAssign]
      simpa using
        (natCode_succ_eq_insert b)
    · have hassign :
          snoc (snoc s (natCode (b + 1)))
              (natAddCanonicalGraph a b) =
            ![omega, natCode a, natCode b, z,
              natCode (b + 1), natAddCanonicalGraph a b] := by
        funext i
        fin_cases i <;> rfl
      have hgraphAssignM : forall i,
          snoc (snoc s (natCode (b + 1)))
            (natAddCanonicalGraph a b) i ∈ M := by
        rw [hassign]
        intro i
        fin_cases i
        · exact homegaM
        · exact haM
        · exact hbM
        · exact hzM
        · exact hySuccM
        · exact hgraphM
      apply (Model.satisfiesIn_delta0_iff hM.1 natAddGraphDelta
        (snoc (snoc s (natCode (b + 1)))
          (natAddCanonicalGraph a b)) hgraphAssignM).mpr
      rw [Delta0Formula.satisfies_toFO]
      rw [hassign, hzEq]
      exact natAddCanonicalGraph_satisfies a b

/-! ## Standard function-absoluteness packaging -/

/-- Total ambient operation on arbitrary set codes.  Invalid inputs are sent
to the empty set; the graph formula is restricted to standard codes by its
domain predicate. -/
noncomputable def natAddCodeZF (x y : ZFSet.{u}) : ZFSet.{u} :=
  match textbookNatDecode x, textbookNatDecode y with
  | some a, some b => natCode (a + b)
  | _, _ => ∅

@[simp]
theorem natAddCodeZF_natCode (a b : Nat) :
    natAddCodeZF (natCode a : ZFSet.{u}) (natCode b) =
      natCode (a + b) := by
  simp [natAddCodeZF]







end TextbookNatFormula

end Constructible

end
end GCHSource_Work_CUGCH_TextbookNaturalAddition


