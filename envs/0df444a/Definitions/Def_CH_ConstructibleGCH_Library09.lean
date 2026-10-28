-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library09
-- name    : CH_ConstructibleGCH_Library09
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:29:12.732694+00:00
-- url     : https://prove2.me/theorems/18e38814-a316-4dfb-b89e-f388846d835f
-- title:
--   Finite tuples and well-founded predecessor closure
-- statement:
--   Finite tuples and their tuple spaces have set codes whose interpretation is absolute in the relevant transitive models. This library supplies their constructor interfaces and the well-founded predecessor relations used by the textbook E recursion.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookFiniteTupleAbsolute.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookTupleSpaceAbsolute.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookSetWellFounded.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookPredecessorClosure.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TextbookClassWellFounded.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library08
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_TextbookFiniteTupleAbsolute -/
section GCHSource_Work_CUGCH_TextbookFiniteTupleAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Finite tuple spaces inside transitive ZF models

The bounded predicate `IsFunc(n,a,f)` is absolute to a transitive model, but
that observation alone does not identify the model's function space with the
ambient `a^n`: one must also prove that every ambient function graph with
finite domain belongs to the model.  This file supplies that missing closure
argument before constructing the whole finite function space internally.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

/-! ## Every finite function graph is a tuple graph -/

theorem exists_textbookTupleGraph_eq_of_isFunc
    {a f : ZFSet.{u}} {n : Nat}
    (hf : ZFSet.IsFunc (natCode n) a f) :
    ∃ s : Tuple (ZFCarrier a) n, textbookTupleGraph s = f := by
  classical
  have hindex : ∀ i : Fin n, (natCode i.1 : ZFSet.{u}) ∈ natCode n := by
    intro i
    exact (mem_natCode_iff_exists_fin _ _).mpr ⟨i, rfl⟩
  choose value hpair hunique using fun i : Fin n => hf.2 (natCode i.1) (hindex i)
  have hvalue : ∀ i : Fin n, value i ∈ a := by
    intro i
    exact (ZFSet.pair_mem_prod.mp (hf.1 (hpair i))).2
  let s : Tuple (ZFCarrier a) n := fun i => ⟨value i, hvalue i⟩
  refine ⟨s, ?_⟩
  apply ZFSet.ext
  intro q
  constructor
  · intro hq
    rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, hi⟩
    rw [← hi]
    exact hpair i
  · intro hq
    rcases ZFSet.mem_prod.mp (hf.1 hq) with
      ⟨index, hindexMem, output, _houtput, hqPair⟩
    rcases (mem_natCode_iff_exists_fin index n).mp hindexMem with ⟨i, rfl⟩
    have houtputValue : output = value i := hunique i output (by
      change ZFSet.pair (natCode i.1) output ∈ f
      rw [← hqPair]
      exact hq)
    apply (mem_textbookTupleGraph_iff s).mpr
    refine ⟨i, ?_⟩
    change ZFSet.pair (natCode i.1) (value i) = q
    rw [← houtputValue, ← hqPair]

namespace Model

noncomputable section

/-- A transitive ZF model is closed under adjoining one member to a set. -/
theorem textbookInsert_mem_of_isTransitiveZFModel
    {M x a : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hx : x ∈ M) (ha : a ∈ M) : insert x a ∈ M := by
  have hsingleton : ({x} : ZFSet.{u}) ∈ M :=
    singleton_mem_of_isTransitiveZFModel hM hx
  have hpair : ({{x}, a} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hsingleton ha
  have hunion := sUnion_mem_of_isTransitiveZFModel hM hpair
  change ZFSet.sUnion ({{x}, a} : ZFSet.{u}) ∈ M at hunion
  rw [ZFSet.sUnion_pair] at hunion
  rw [ZFSet.insert_eq]
  exact hunion

/-- The canonical graph of a finite tuple of members of `a` belongs to `M`. -/
theorem textbookTupleGraph_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    {n : Nat} (s : Tuple (ZFCarrier a) n) :
    textbookTupleGraph s ∈ M := by
  induction n with
  | zero =>
      have hempty : textbookTupleGraph s = (∅ : ZFSet.{u}) := by
        apply ZFSet.eq_empty _ |>.mpr
        intro q hq
        rcases (mem_textbookTupleGraph_iff s).mp hq with ⟨i, _⟩
        exact Fin.elim0 i
      rw [hempty]
      exact empty_mem_of_isTransitiveZFModel hM
  | succ n ih =>
      let initial : Tuple (ZFCarrier a) n := fun i => s i.castSucc
      let finalEntry : ZFCarrier a := s (Fin.last n)
      have hs : s = snoc initial finalEntry := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [finalEntry]
        · simp [initial]
      rw [hs, textbookTupleGraph_snoc]
      apply textbookInsert_mem_of_isTransitiveZFModel hM
      · apply kuratowskiPair_mem_of_isTransitiveZFModel hM
        · exact natOrdinal_mem_of_isTransitiveZFModel hM n
        · exact hM.1.mem_trans finalEntry.2 ha
      · exact ih initial

/-- Every ambient function graph from a standard finite ordinal into `a`
belongs to a transitive ZF model containing `a`. -/
theorem finiteIsFunc_mem_of_isTransitiveZFModel
    {M a f : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    {n : Nat} (hf : ZFSet.IsFunc (natCode n) a f) : f ∈ M := by
  rcases exists_textbookTupleGraph_eq_of_isFunc hf with ⟨s, rfl⟩
  exact textbookTupleGraph_mem_of_isTransitiveZFModel hM ha s

/-! ## A reusable Delta-zero absoluteness bridge -/

/-- Raw restricted satisfaction of a bounded formula agrees with its ambient
semantics when all parameters belong to a transitive carrier. -/
theorem satisfiesIn_delta0_iff
    {M : ZFSet.{u}} (hM : M.IsTransitive) {n : Nat}
    (phi : Delta0Formula n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) phi.toFO s ↔
      FOFormula.Satisfies Delta0Formula.ZFMem phi.toFO s := by
  let sM : Tuple (ZFCarrier M) n := fun i => ⟨s i, hs i⟩
  have hval : (fun i => (sM i).1) = s := by
    funext i
    rfl
  have hdeltaVal : Delta0Formula.val sM = s := by
    funext i
    rfl
  calc
    SatisfiesIn (M : Set ZFSet.{u}) phi.toFO s ↔
        FOFormula.Satisfies (zfCarrierMem M) phi.toFO sM := by
      have hbridge :=
        (Model.satisfies_subtype_iff_satisfiesIn
          (M : Set ZFSet.{u}) phi.toFO sM).symm
      rw [hval] at hbridge
      exact hbridge
    _ ↔ FOFormula.Satisfies Delta0Formula.ZFMem phi.toFO s := by
      have habsolute :=
        Delta0Formula.satisfies_toFO_absolute hM phi sM
      rw [hdeltaVal] at habsolute
      exact habsolute

/-! ## Internal power-set witnesses -/

/-- The Power Set axiom inside `M`, stated without identifying its witness
with the ambient powerset.  It contains exactly the subsets of `x` that are
themselves members of `M`. -/
theorem exists_internalPowerSet
    {M x : ZFSet.{u}} (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    ∃ power : ZFCarrier M,
      ∀ y : ZFCarrier M, y.1 ∈ power.1 ↔ y.1 ⊆ x := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  let xM : ZFCarrier M := ⟨x, hx⟩
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .powerSet xM with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  intro y
  have hpowerY := hpower y
  change y.1 ∈ power.1 ↔
    ∀ z : ZFCarrier M, z.1 ∈ y.1 → z.1 ∈ x at hpowerY
  constructor
  · intro hyPower z hzy
    have hzM : z ∈ M := hM.1.mem_trans hzy y.2
    exact (hpowerY.mp hyPower) ⟨z, hzM⟩ hzy
  · intro hySubset
    apply hpowerY.mpr
    intro z hzy
    exact hySubset hzy

end

end Model

namespace TextbookDefFormula

/-! ## A bounded formula for Cartesian-product membership -/

/-- `candidate` is a Kuratowski pair with first coordinate in `left` and
second coordinate in `right`. -/
def productMemberDeltaAt {n : Nat}
    (candidate left right : Fin n) : Delta0Formula n :=
  Delta0Formula.boundedEx left
    (Delta0Formula.boundedEx right.castSucc
      (Delta0Formula.kuratowskiPairEqAt
        candidate.castSucc.castSucc
        (Fin.last n).castSucc
        (Fin.last (n + 1))))

@[simp]
theorem satisfies_productMemberDeltaAt {n : Nat}
    (candidate left right : Fin n) (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (productMemberDeltaAt candidate left right) s ↔
      s candidate ∈ ZFSet.prod (s left) (s right) := by
  simp only [productMemberDeltaAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc, ZFSet.mem_prod]

/-- Layout `[left, right, candidate]`. -/
def productMemberDelta : Delta0Formula 3 :=
  productMemberDeltaAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

def productMemberFormula : FOFormula 3 :=
  productMemberDelta.toFO

@[simp]
theorem satisfies_productMemberFormula
    (left right candidate : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem productMemberFormula
        ![left, right, candidate] ↔
      candidate ∈ ZFSet.prod left right := by
  simp [productMemberFormula, productMemberDelta]

/-- Layout `[domain, codomain, graph]`. -/
def isFunctionDelta : Delta0Formula 3 :=
  isFunctionDeltaAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)

def isFunctionFormula : FOFormula 3 :=
  isFunctionDelta.toFO

@[simp]
theorem satisfies_isFunctionFormula
    (domain codomain graph : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem isFunctionFormula
        ![domain, codomain, graph] ↔
      ZFSet.IsFunc domain codomain graph := by
  simp [isFunctionFormula, isFunctionDelta]

end TextbookDefFormula

namespace Model

noncomputable section

/-! ## Cartesian products in transitive ZF models -/

/-- Binary union closure, derived from Pairing and Union inside the model. -/
theorem textbookUnion_mem_of_isTransitiveZFModel
    {M x y : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hx : x ∈ M) (hy : y ∈ M) : x ∪ y ∈ M := by
  have hpair : ({x, y} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hx hy
  simpa only [ZFSet.sUnion_pair] using
    sUnion_mem_of_isTransitiveZFModel hM hpair

theorem satisfiesIn_productMemberFormula_iff
    {M left right candidate : ZFSet.{u}}
    (hM : M.IsTransitive) (hleft : left ∈ M)
    (hright : right ∈ M) (hcandidate : candidate ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.productMemberFormula
        ![left, right, candidate] ↔
      candidate ∈ ZFSet.prod left right := by
  have hs : ∀ i : Fin 3, ![left, right, candidate] i ∈ M := by
    intro i
    fin_cases i
    · exact hleft
    · exact hright
    · exact hcandidate
  rw [TextbookDefFormula.productMemberFormula,
    satisfiesIn_delta0_iff hM TextbookDefFormula.productMemberDelta
      ![left, right, candidate] hs]
  simpa only [TextbookDefFormula.productMemberFormula] using
    (TextbookDefFormula.satisfies_productMemberFormula
      left right candidate)

/-- A transitive ZF model is closed under the ambient Cartesian product.
The proof uses two internal power-set witnesses only as a bounding set for
Separation; it never asserts that either witness is an ambient powerset. -/
theorem prod_mem_of_isTransitiveZFModel
    {M left right : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    (hleft : left ∈ M) (hright : right ∈ M) :
    ZFSet.prod left right ∈ M := by
  let union : ZFSet.{u} := left ∪ right
  have hunion : union ∈ M :=
    textbookUnion_mem_of_isTransitiveZFModel hM hleft hright
  rcases exists_internalPowerSet hM hunion with ⟨powerOne, hpowerOne⟩
  rcases exists_internalPowerSet hM powerOne.2 with
    ⟨powerTwo, hpowerTwo⟩
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨left, hleft⟩, ⟨right, hright⟩]
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.productMemberFormula params powerTwo
  have hassign : ∀ q : ZFSet.{u},
      snoc (zfCarrierTupleVal params) q = ![left, right, q] := by
    intro q
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (powerTwo.1.sep fun q =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.productMemberFormula
          (snoc (zfCarrierTupleVal params) q)) =
        ZFSet.prod left right := by
    apply ZFSet.ext
    intro q
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hqPowerTwo, hqFormula⟩
      have hqM : q ∈ M :=
        hM.1.mem_trans hqPowerTwo powerTwo.2
      apply (satisfiesIn_productMemberFormula_iff
        hM.1 hleft hright hqM).mp
      rwa [← hassign q]
    · intro hqProd
      rcases ZFSet.mem_prod.mp hqProd with
        ⟨x, hxLeft, y, hyRight, hqPair⟩
      have hxM : x ∈ M := hM.1.mem_trans hxLeft hleft
      have hyM : y ∈ M := hM.1.mem_trans hyRight hright
      have hqM : q ∈ M := by
        rw [hqPair]
        exact kuratowskiPair_mem_of_isTransitiveZFModel hM hxM hyM
      have hsingletonM : ({x} : ZFSet.{u}) ∈ M :=
        singleton_mem_of_isTransitiveZFModel hM hxM
      have hunorderedM : ({x, y} : ZFSet.{u}) ∈ M :=
        unorderedPair_mem_of_isTransitiveZFModel hM hxM hyM
      have hsingletonSubset : ({x} : ZFSet.{u}) ⊆ union := by
        intro z hz
        have hzx : z = x := by simpa using hz
        subst z
        exact ZFSet.mem_union.mpr (Or.inl hxLeft)
      have hunorderedSubset : ({x, y} : ZFSet.{u}) ⊆ union := by
        intro z hz
        rcases ZFSet.mem_pair.mp hz with rfl | rfl
        · exact ZFSet.mem_union.mpr (Or.inl hxLeft)
        · exact ZFSet.mem_union.mpr (Or.inr hyRight)
      have hsingletonPowerOne : ({x} : ZFSet.{u}) ∈ powerOne.1 :=
        (hpowerOne ⟨{x}, hsingletonM⟩).mpr hsingletonSubset
      have hunorderedPowerOne : ({x, y} : ZFSet.{u}) ∈ powerOne.1 :=
        (hpowerOne ⟨{x, y}, hunorderedM⟩).mpr hunorderedSubset
      have hqSubsetPowerOne : q ⊆ powerOne.1 := by
        intro z hz
        rw [hqPair, ZFSet.pair] at hz
        rcases ZFSet.mem_pair.mp hz with hzx | hzu
        · simpa only [hzx] using hsingletonPowerOne
        · simpa only [hzu] using hunorderedPowerOne
      have hqPowerTwo : q ∈ powerTwo.1 :=
        (hpowerTwo ⟨q, hqM⟩).mpr hqSubsetPowerOne
      refine ⟨hqPowerTwo, ?_⟩
      rw [hassign q]
      exact (satisfiesIn_productMemberFormula_iff
        hM.1 hleft hright hqM).mpr hqProd
  rw [hsepEq] at hsep
  exact hsep

/-! ## Finite function spaces in transitive ZF models -/

theorem satisfiesIn_isFunctionFormula_iff
    {M domain codomain graph : ZFSet.{u}}
    (hM : M.IsTransitive) (hdomain : domain ∈ M)
    (hcodomain : codomain ∈ M) (hgraph : graph ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.isFunctionFormula
        ![domain, codomain, graph] ↔
      ZFSet.IsFunc domain codomain graph := by
  have hs : ∀ i : Fin 3, ![domain, codomain, graph] i ∈ M := by
    intro i
    fin_cases i
    · exact hdomain
    · exact hcodomain
    · exact hgraph
  rw [TextbookDefFormula.isFunctionFormula,
    satisfiesIn_delta0_iff hM TextbookDefFormula.isFunctionDelta
      ![domain, codomain, graph] hs]
  simpa only [TextbookDefFormula.isFunctionFormula] using
    (TextbookDefFormula.satisfies_isFunctionFormula
      domain codomain graph)

/-- The full ambient finite function space `a^n` belongs to every transitive
ZF model containing `a`.  The reverse inclusion in the final Separation
identity is precisely where finite-graph closure is used. -/
theorem textbookTupleSpace_mem_of_isTransitiveZFModel
    {M a : ZFSet.{u}} (hM : IsTransitiveZFModel M) (ha : a ∈ M)
    (n : Nat) : textbookTupleSpace a n ∈ M := by
  have hnM : (natCode n : ZFSet.{u}) ∈ M :=
    natOrdinal_mem_of_isTransitiveZFModel hM n
  have hprodM : ZFSet.prod (natCode n) a ∈ M :=
    prod_mem_of_isTransitiveZFModel hM hnM ha
  rcases exists_internalPowerSet hM hprodM with ⟨power, hpower⟩
  let params : Tuple (ZFCarrier M) 2 :=
    ![⟨natCode n, hnM⟩, ⟨a, ha⟩]
  have hsep := satisfiesIn_sep_mem_of_isTransitiveZFModel hM
    TextbookDefFormula.isFunctionFormula params power
  have hassign : ∀ graph : ZFSet.{u},
      snoc (zfCarrierTupleVal params) graph = ![natCode n, a, graph] := by
    intro graph
    funext i
    fin_cases i <;> rfl
  have hsepEq :
      (power.1.sep fun graph =>
        SatisfiesIn (M : Set ZFSet.{u})
          TextbookDefFormula.isFunctionFormula
          (snoc (zfCarrierTupleVal params) graph)) =
        textbookTupleSpace a n := by
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_sep, mem_textbookTupleSpace_iff]
    constructor
    · rintro ⟨hgraphPower, hgraphFormula⟩
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphPower power.2
      apply (satisfiesIn_isFunctionFormula_iff
        hM.1 hnM ha hgraphM).mp
      rwa [← hassign graph]
    · intro hgraphFunc
      have hgraphM : graph ∈ M :=
        finiteIsFunc_mem_of_isTransitiveZFModel hM ha hgraphFunc
      have hgraphPower : graph ∈ power.1 :=
        (hpower ⟨graph, hgraphM⟩).mpr hgraphFunc.1
      refine ⟨hgraphPower, ?_⟩
      rw [hassign graph]
      exact (satisfiesIn_isFunctionFormula_iff
        hM.1 hnM ha hgraphM).mpr hgraphFunc
  rw [hsepEq] at hsep
  exact hsep

end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookFiniteTupleAbsolute


/- Source module: Solutions.Work_CUGCH_TextbookTupleSpaceAbsolute -/
section GCHSource_Work_CUGCH_TextbookTupleSpaceAbsolute
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Absoluteness of finite function spaces

The formula for an unrestricted function space is not absolute to a
transitive model: the model may omit subsets of an infinite Cartesian
product.  This file therefore restricts the first input to a standard finite
ordinal.  The restriction is part of the graph formula, as required by
`Model.FunctionAbsoluteTo`; the formula is false away from its stated domain.

The guard says that the first input belongs to the internally least inductive
set.  In a transitive ZF model that set is the ambient von Neumann `omega`.
The function-space conjunct itself is exactly
`TextbookDefFormula.functionSpaceGraph`.
-/

section

open Set

universe u

namespace Constructible

open FiniteSequenceZF

namespace Model

noncomputable section

/-! ## Restricted-semantics helpers -/

 theorem satisfiesIn_all_iff_TextbookTupleSpaceAbsolute_gch
    (M : Set ZFSet.{u}) {n : Nat} (formula : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.all formula) s <->
      forall x : ZFSet.{u}, x ∈ M ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp [FOFormula.all, SatisfiesIn]

 theorem satisfiesIn_imp_iff_TextbookTupleSpaceAbsolute_gch
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.imp left right) s <->
      (SatisfiesIn M left s -> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.imp, FOFormula.disj, SatisfiesIn]
  tauto

 theorem satisfiesIn_biimp_iff_TextbookTupleSpaceAbsolute_gch
    (M : Set ZFSet.{u}) {n : Nat} (left right : FOFormula n)
    (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.biimp left right) s <->
      (SatisfiesIn M left s <-> SatisfiesIn M right s) := by
  classical
  simp only [FOFormula.biimp, SatisfiesIn, satisfiesIn_imp_iff_TextbookTupleSpaceAbsolute_gch]
  tauto

 theorem satisfiesIn_boundedAll_iff_TextbookTupleSpaceAbsolute_gch
    (M : Set ZFSet.{u}) {n : Nat} (set : Fin n)
    (formula : FOFormula (n + 1)) (s : Tuple ZFSet.{u} n) :
    SatisfiesIn M (FOFormula.boundedAll set formula) s <->
      forall x : ZFSet.{u}, x ∈ M -> x ∈ s set ->
        SatisfiesIn M formula (snoc s x) := by
  classical
  simp only [FOFormula.boundedAll, FOFormula.boundedEx, SatisfiesIn]
  constructor
  · intro h x hxM hxSet
    by_contra hx
    exact h ⟨x, hxM, by simpa using hxSet, hx⟩
  · intro h hex
    rcases hex with ⟨x, hxM, hxSet, hx⟩
    exact hx (h x hxM (by simpa using hxSet))

/-! ## A formula that denotes the standard omega -/

/-- `s i` is the internally least inductive set.  The inductiveness predicate
is the one whose exact semantics over arbitrary transitive ZF models was
proved in `TransitiveZFOmega`. -/
def standardOmegaAt {n : Nat} (i : Fin n) : FOFormula n :=
  .conj
    (transitiveZFInductiveAt i)
    (FOFormula.all
      (FOFormula.imp
        (transitiveZFInductiveAt (Fin.last n))
        (FOFormula.boundedAll i.castSucc
          (.mem (Fin.last (n + 1)) (Fin.last n).castSucc))))

/-- In every transitive ZF model, `standardOmegaAt` denotes exactly the
ambient von Neumann `omega`. -/
theorem satisfiesIn_standardOmegaAt_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) {n : Nat}
    (i : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall j, s j ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) (standardOmegaAt i) s <->
      s i = Ordinal.omega0.toZFSet := by
  rw [standardOmegaAt]
  simp only [SatisfiesIn, satisfiesIn_all_iff_TextbookTupleSpaceAbsolute_gch, satisfiesIn_imp_iff_TextbookTupleSpaceAbsolute_gch,
    satisfiesIn_boundedAll_iff_TextbookTupleSpaceAbsolute_gch, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hinductiveFormula, hminimalFormula⟩
    have hinductive : ZFInductiveSetIn M (s i) :=
      (satisfiesIn_transitiveZFInductiveAt_iff hM.1
        (empty_mem_of_isTransitiveZFModel hM)
        (fun x hx => successor_mem_of_isTransitiveZFModel hM hx)
        i s hs).mp hinductiveFormula
    have hminimal : forall w : ZFSet.{u}, w ∈ M ->
        ZFInductiveSetIn M w -> s i ⊆ w := by
      intro w hwM hwInductive x hx
      have hwFormula :
          SatisfiesIn (M : Set ZFSet.{u})
            (transitiveZFInductiveAt (Fin.last n)) (snoc s w) := by
        apply (satisfiesIn_transitiveZFInductiveAt_iff hM.1
          (empty_mem_of_isTransitiveZFModel hM)
          (fun z hz => successor_mem_of_isTransitiveZFModel hM hz)
          (Fin.last n) (snoc s w) (by
            intro j
            refine Fin.lastCases ?_ (fun k => ?_) j
            · simpa using hwM
            · simpa using hs k)).mpr
        simpa only [snoc_last] using hwInductive
      exact hminimalFormula w hwM hwFormula x
        (hM.1.mem_trans hx (hs i)) hx
    let omegaM : ZFCarrier M := ⟨s i, hs i⟩
    exact zfCarrier_leastInductiveSet_eq_omega
      hM omegaM hinductive hminimal
  · intro homega
    have homegaM : Ordinal.omega0.toZFSet ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    have hnM : forall k : Nat, (k : Ordinal.{u}).toZFSet ∈ M :=
      natOrdinal_mem_of_isTransitiveZFModel hM
    constructor
    · apply (satisfiesIn_transitiveZFInductiveAt_iff hM.1
        (empty_mem_of_isTransitiveZFModel hM)
        (fun x hx => successor_mem_of_isTransitiveZFModel hM hx)
        i s hs).mpr
      simpa only [homega] using omegaToZFSet_isInductiveSetIn M
    · intro w hwM hwFormula x hxM hxOmega
      have hwInductive : ZFInductiveSetIn M w := by
        simpa only [snoc_last] using
          (satisfiesIn_transitiveZFInductiveAt_iff hM.1
            (empty_mem_of_isTransitiveZFModel hM)
            (fun z hz => successor_mem_of_isTransitiveZFModel hM hz)
            (Fin.last n) (snoc s w) (by
              intro j
              refine Fin.lastCases ?_ (fun k => ?_) j
              · simpa using hwM
              · simpa using hs k)).mp hwFormula
      rw [homega] at hxOmega
      rcases Ordinal.mem_toZFSet_iff.mp hxOmega with ⟨alpha, halpha, rfl⟩
      rcases Ordinal.lt_omega0.mp halpha with ⟨k, rfl⟩
      exact natOrdinal_mem_of_ZFInductiveSetIn hwInductive hnM k

/-! ## The finite-domain guard -/

/-- Coordinate `domain` belongs to the internally defined standard omega. -/
def standardFiniteDomainAt {n : Nat} (domain : Fin n) : FOFormula n :=
  .ex (.conj
    (standardOmegaAt (Fin.last n))
    (.mem domain.castSucc (Fin.last n)))

/-- Exact restricted semantics of the finite-domain guard. -/
theorem satisfiesIn_standardFiniteDomainAt_iff
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M) {n : Nat}
    (domain : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : forall i, s i ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u})
        (standardFiniteDomainAt domain) s <->
      exists k : Nat, s domain = natCode k := by
  simp only [standardFiniteDomainAt, SatisfiesIn,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨omega, homegaM, homegaFormula, hdomainOmega⟩
    have homega : omega = Ordinal.omega0.toZFSet :=
      by
        simpa only [snoc_last] using
          (satisfiesIn_standardOmegaAt_iff hM (Fin.last n)
            (snoc s omega) (by
              intro i
              refine Fin.lastCases ?_ (fun j => ?_) i
              · simpa using homegaM
              · simpa using hs j)).mp homegaFormula
    rw [homega] at hdomainOmega
    exact IndexedSequenceZF.mem_omega_iff_exists_natCode (s domain)
      |>.mp hdomainOmega
  · rintro ⟨k, hdomain⟩
    let omega : ZFSet.{u} := Ordinal.omega0.toZFSet
    have homegaM : omega ∈ M :=
      omega_toZFSet_mem_of_isTransitiveZFModel hM
    refine ⟨omega, homegaM, ?_, ?_⟩
    · apply (satisfiesIn_standardOmegaAt_iff hM
        (Fin.last n) (snoc s omega) (by
          intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using homegaM
          · simpa using hs j)).mpr
      simp only [snoc_last, omega]
    · apply (IndexedSequenceZF.mem_omega_iff_exists_natCode
        (s domain)).mpr
      exact ⟨k, hdomain⟩

/-! ## Guarded function-space graph -/



/-- Layout `[domain, codomain, space]`.  The first conjunct makes the graph
false off `FiniteFunctionSpaceTupleDomain`; the second conjunct is the
unmodified general function-space formula. -/
def finiteFunctionSpaceGraph : FOFormula 3 :=
  .conj
    (standardFiniteDomainAt (0 : Fin 3))
    TextbookDefFormula.functionSpaceGraph

/-- On a standard finite domain, the unrestricted function-space formula has
the expected semantics inside every transitive ZF model. -/
theorem satisfiesIn_functionSpaceGraph_iff_of_standardFinite
    {M domain codomain space : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hdomain : domain ∈ M) (hcodomain : codomain ∈ M)
    (hspace : space ∈ M)
    (hfinite : exists n : Nat, domain = natCode n) :
    SatisfiesIn (M : Set ZFSet.{u})
        TextbookDefFormula.functionSpaceGraph
        ![domain, codomain, space] <->
      space = ZFSet.funs domain codomain := by
  rcases hfinite with ⟨n, rfl⟩
  rw [TextbookDefFormula.functionSpaceGraph,
    TextbookDefFormula.functionSpaceAt, satisfiesIn_all_iff_TextbookTupleSpaceAbsolute_gch]
  simp only [satisfiesIn_biimp_iff_TextbookTupleSpaceAbsolute_gch, SatisfiesIn,
    TextbookDefFormula.isFunctionAt, snoc_last, snoc_castSucc]
  have hfunction (graph : ZFSet.{u}) (hgraphM : graph ∈ M) :
      SatisfiesIn (M : Set ZFSet.{u})
          (TextbookDefFormula.isFunctionDeltaAt
            (Fin.last 3) (0 : Fin 3).castSucc (1 : Fin 3).castSucc).toFO
          (snoc ![natCode n, codomain, space] graph) <->
        ZFSet.IsFunc (natCode n) codomain graph := by
    have hassign :
        snoc ![natCode n, codomain, space] graph =
          ![natCode n, codomain, space, graph] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    have hs : forall i,
        ![natCode n, codomain, space, graph] i ∈ M := by
      intro i
      fin_cases i
      · exact hdomain
      · exact hcodomain
      · exact hspace
      · exact hgraphM
    have habsolute := satisfiesIn_delta0_iff hM.1
      (TextbookDefFormula.isFunctionDeltaAt
        (Fin.last 3) (0 : Fin 3).castSucc (1 : Fin 3).castSucc)
      ![natCode n, codomain, space, graph] hs
    rw [Delta0Formula.satisfies_toFO,
      TextbookDefFormula.satisfies_isFunctionDeltaAt] at habsolute
    have hdomainValue :
        ![natCode n, codomain, space, graph] ((0 : Fin 3).castSucc) =
          natCode n := rfl
    have hcodomainValue :
        ![natCode n, codomain, space, graph] ((1 : Fin 3).castSucc) =
          codomain := rfl
    have hgraphValue :
        ![natCode n, codomain, space, graph] (Fin.last 3) = graph := rfl
    rw [hdomainValue, hcodomainValue, hgraphValue] at habsolute
    exact habsolute
  constructor
  · intro h
    apply ZFSet.ext
    intro graph
    rw [ZFSet.mem_funs]
    constructor
    · intro hgraphSpace
      have hgraphM : graph ∈ M :=
        hM.1.mem_trans hgraphSpace hspace
      exact (hfunction graph hgraphM).mp
        ((h graph hgraphM).mp hgraphSpace)
    · intro hgraphFunc
      have hgraphM : graph ∈ M :=
        finiteIsFunc_mem_of_isTransitiveZFModel
          hM hcodomain hgraphFunc
      exact (h graph hgraphM).mpr
        ((hfunction graph hgraphM).mpr hgraphFunc)
  · intro hspaceEq graph hgraphM
    constructor
    · intro hgraphSpace
      apply (hfunction graph hgraphM).mpr
      apply ZFSet.mem_funs.mp
      rwa [← hspaceEq]
    · intro hgraphFormula
      change graph ∈ space
      rw [hspaceEq, ZFSet.mem_funs]
      exact (hfunction graph hgraphM).mp hgraphFormula

/-- Exact restricted semantics of the guarded graph. -/
theorem satisfiesIn_finiteFunctionSpaceGraph_iff
    {M domain codomain space : ZFSet.{u}}
    (hM : IsTransitiveZFModel M)
    (hdomain : domain ∈ M) (hcodomain : codomain ∈ M)
    (hspace : space ∈ M) :
    SatisfiesIn (M : Set ZFSet.{u}) finiteFunctionSpaceGraph
        ![domain, codomain, space] <->
      (exists n : Nat, domain = natCode n) ∧
        space = ZFSet.funs domain codomain := by
  rw [finiteFunctionSpaceGraph]
  simp only [SatisfiesIn]
  rw [satisfiesIn_standardFiniteDomainAt_iff hM
    (0 : Fin 3) ![domain, codomain, space] (by
      intro i
      fin_cases i
      · exact hdomain
      · exact hcodomain
      · exact hspace)]
  constructor
  · rintro ⟨hfinite, hspaceFormula⟩
    exact ⟨hfinite,
      (satisfiesIn_functionSpaceGraph_iff_of_standardFinite
        hM hdomain hcodomain hspace hfinite).mp hspaceFormula⟩
  · rintro ⟨hfinite, hspaceEq⟩
    exact ⟨hfinite,
      (satisfiesIn_functionSpaceGraph_iff_of_standardFinite
        hM hdomain hcodomain hspace hfinite).mpr hspaceEq⟩



end

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TextbookTupleSpaceAbsolute


/- Source module: Solutions.Work_CUGCH_TextbookSetWellFounded -/
section GCHSource_Work_CUGCH_TextbookSetWellFounded
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Textbook set-well-founded and set-like class relations

This file formalizes the definitions used in Sections 6.1 and 6.2 of Wang
Fangting, *Axiomatic Set Theory*.

A class relation is well-founded on `A` when every nonempty **set** contained
in `A` has a minimal member.  This is deliberately not defined as Lean's
`WellFounded` on the whole external type: for a proper-class domain that would
quantify over arbitrary external subclasses and would be stronger than the
textbook definition.

Set-likeness is a separate condition saying that every predecessor class is
represented by an actual `ZFSet`.  The bad-point theorem below is the exact
minimal-counterexample argument used in the recursion absoluteness proof.
Its bad set is an ambient set; it is not asserted to belong to a model.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## Standard class-relation definitions -/

/-- Evaluation of a binary class relation represented as two-coordinate
tuples.  The coordinate order is `(left,right)`. -/
def ClassRel (R : Set (Tuple ZFSet.{u} 2))
    (left right : ZFSet.{u}) : Prop :=
  ![left, right] ∈ R

/-- Every pair in `R` has both coordinates in `A`, i.e. `R` is a relation on
`A`. -/
def IsRelationOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall s, s ∈ R -> Model.TupleIn A s

/-- The left endpoint of a pair in a relation on `A` lies in `A`. -/
theorem IsRelationOn.left_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsRelationOn A R) {left right : ZFSet.{u}}
    (h : ClassRel R left right) : left ∈ A := by
  have htuple := hR ![left, right] h
  have hleft := htuple (0 : Fin 2)
  change left ∈ A at hleft
  exact hleft

/-- The right endpoint of a pair in a relation on `A` lies in `A`. -/
theorem IsRelationOn.right_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsRelationOn A R) {left right : ZFSet.{u}}
    (h : ClassRel R left right) : right ∈ A := by
  have htuple := hR ![left, right] h
  have hright := htuple (1 : Fin 2)
  change right ∈ A at hright
  exact hright

/-- Every nonempty actual set contained in `A` has an `R`-minimal member.
This is the textbook class-relation notion of well-foundedness. -/
def HasSetMinimaOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall z : ZFSet.{u},
    (forall x, x ∈ z -> x ∈ A) ->
    (exists x, x ∈ z) ->
    exists u, u ∈ z ∧ forall v, v ∈ z -> Not (ClassRel R v u)

/-- Every predecessor class of a point of `A` is represented by an actual
set.  This is the textbook notion of a set-like relation. -/
def HasSetPredecessorsOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall x, x ∈ A ->
    exists predecessors : ZFSet.{u}, forall y,
      y ∈ predecessors <-> y ∈ A ∧ ClassRel R y x

/-- A well-founded set-like relation in the exact textbook sense. -/
def IsWellFoundedSetLikeOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  IsRelationOn A R ∧ HasSetMinimaOn A R ∧ HasSetPredecessorsOn A R

/-- `predecessors` represents the full predecessor set of `x` in `A`. -/
def IsPredecessorSet (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2))
    (x predecessors : ZFSet.{u}) : Prop :=
  forall y, y ∈ predecessors <-> y ∈ A ∧ ClassRel R y x

/-- Textbook condition (III): every ambient predecessor of an argument from
`M` is again in `M`.  This condition remains separate from set-likeness. -/
def PredecessorsClosedIn (M A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall x, x ∈ M -> forall y, y ∈ A -> ClassRel R y x -> y ∈ M

/-- The actual ambient set representing the external class intersection
`A ∩ M`.  It is not asserted to be an element of `M`. -/
def modelIntersectionZF (M : ZFSet.{u})
    (A : Set ZFSet.{u}) : ZFSet.{u} :=
  M.sep fun x => x ∈ A

@[simp]
theorem mem_modelIntersectionZF_iff
    {M : ZFSet.{u}} {A : Set ZFSet.{u}} {x : ZFSet.{u}} :
    x ∈ modelIntersectionZF M A <-> x ∈ M ∧ x ∈ A := by
  exact ZFSet.mem_sep

/-! ## Comparison with Lean well-foundedness on an actual set -/

/-- On an actual set-sized domain, and only there, the textbook set-minimum
condition is equivalent to Lean well-foundedness of the subtype relation. -/
theorem hasSetMinimaOn_iff_wellFounded_zfCarrier
    (domain : ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2)) :
    HasSetMinimaOn (domain : Set ZFSet.{u}) R <->
      WellFounded fun y x : ZFCarrier domain => ClassRel R y.1 x.1 := by
  constructor
  · intro hmin
    apply WellFounded.wellFounded_iff_has_min.mpr
    intro s hs
    let represented : ZFSet.{u} := domain.sep fun x =>
      exists hx : x ∈ domain,
        (⟨x, hx⟩ : ZFCarrier domain) ∈ s
    have hrepresentedSubset : forall x, x ∈ represented -> x ∈ domain := by
      intro x hx
      exact (ZFSet.mem_sep.mp hx).1
    have hrepresentedNonempty : exists x, x ∈ represented := by
      rcases hs with ⟨x, hx⟩
      refine ⟨x.1, ZFSet.mem_sep.mpr ⟨x.2, ?_⟩⟩
      exact ⟨x.2, by simpa only [Subtype.coe_eta] using hx⟩
    rcases hmin represented hrepresentedSubset hrepresentedNonempty with
      ⟨m, hmRepresented, hmMinimal⟩
    have hmDomain : m ∈ domain := (ZFSet.mem_sep.mp hmRepresented).1
    let mD : ZFCarrier domain := ⟨m, hmDomain⟩
    have hmS : mD ∈ s := by
      rcases (ZFSet.mem_sep.mp hmRepresented).2 with ⟨hm', hm'S⟩
      have heq : (⟨m, hm'⟩ : ZFCarrier domain) = mD := Subtype.ext rfl
      simpa only [heq] using hm'S
    refine ⟨mD, hmS, ?_⟩
    intro x hxS hxRel
    have hxRepresented : x.1 ∈ represented := by
      refine ZFSet.mem_sep.mpr ⟨x.2, x.2, ?_⟩
      simpa only [Subtype.coe_eta] using hxS
    exact hmMinimal x.1 hxRepresented hxRel
  · intro hwf z hzSubset hzNonempty
    let s : Set (ZFCarrier domain) := {x | x.1 ∈ z}
    have hsNonempty : s.Nonempty := by
      rcases hzNonempty with ⟨x, hx⟩
      have hxDomain : x ∈ domain := hzSubset x hx
      exact ⟨⟨x, hxDomain⟩, hx⟩
    rcases hwf.has_min s hsNonempty with ⟨m, hmS, hmMinimal⟩
    refine ⟨m.1, hmS, ?_⟩
    intro x hx
    have hxDomain : x ∈ domain := hzSubset x hx
    let xD : ZFCarrier domain := ⟨x, hxDomain⟩
    exact hmMinimal xD hx

/-! ## The textbook bad-point argument -/

/-- If local agreement follows from agreement at all predecessors, then two
functions agree on any set-sized predecessor-closed domain.  The proof takes
an `R`-minimal member of the ambient set of bad points. -/
theorem agreeOn_of_hasSetMinimaOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hmin : HasSetMinimaOn A R)
    {domain : ZFSet.{u}}
    (hdom : forall x, x ∈ domain -> x ∈ A)
    (hclosed : forall ⦃x⦄, x ∈ domain ->
      forall ⦃y⦄, ClassRel R y x -> y ∈ domain)
    {F H : ZFSet.{u} -> ZFSet.{u}}
    (hlocal : forall x, x ∈ domain ->
      (forall y, ClassRel R y x -> F y = H y) ->
      F x = H x) :
    forall x, x ∈ domain -> F x = H x := by
  intro x hx
  by_contra hxBad
  let bad : ZFSet.{u} := domain.sep fun z => Not (F z = H z)
  have hbadSubset : forall z, z ∈ bad -> z ∈ A := by
    intro z hz
    exact hdom z (ZFSet.mem_sep.mp hz).1
  have hbadNonempty : exists z, z ∈ bad := by
    exact ⟨x, ZFSet.mem_sep.mpr ⟨hx, hxBad⟩⟩
  rcases hmin bad hbadSubset hbadNonempty with ⟨u, huBad, huMinimal⟩
  have huDomain : u ∈ domain := (ZFSet.mem_sep.mp huBad).1
  have huNe : Not (F u = H u) := (ZFSet.mem_sep.mp huBad).2
  have hpredAgree : forall y, ClassRel R y u -> F y = H y := by
    intro y hyu
    have hyDomain : y ∈ domain := hclosed huDomain hyu
    by_contra hyBad
    have hyInBad : y ∈ bad :=
      ZFSet.mem_sep.mpr ⟨hyDomain, hyBad⟩
    exact huMinimal y hyInBad hyu
  exact huNe (hlocal u huDomain hpredAgree)

/-- Two solutions of the same recursive equation agree on a set-sized
predecessor-closed domain.  Unlike the auxiliary theorem based on Lean's
global `WellFounded`, this proof uses exactly the textbook set-minimum
hypothesis and the displayed predecessor sets. -/
theorem recursionSolutions_agreeOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hmin : HasSetMinimaOn A R)
    {domain : ZFSet.{u}}
    (hdom : forall x, x ∈ domain -> x ∈ A)
    (hclosed : forall ⦃x⦄, x ∈ domain ->
      forall ⦃y⦄, ClassRel R y x -> y ∈ domain)
    {predecessors : ZFSet.{u} -> ZFSet.{u}}
    (hpredecessors : forall x, x ∈ domain ->
      IsPredecessorSet A R x (predecessors x))
    {step : ZFSet.{u} -> ZFSet.{u} -> ZFSet.{u}}
    {F H : ZFSet.{u} -> ZFSet.{u}}
    (hF : forall x, x ∈ domain ->
      F x = step x (predecessorRestrictionGraph (predecessors x) F))
    (hH : forall x, x ∈ domain ->
      H x = step x (predecessorRestrictionGraph (predecessors x) H)) :
    forall x, x ∈ domain -> F x = H x := by
  apply agreeOn_of_hasSetMinimaOn hmin hdom hclosed
  intro x hx hpredAgree
  rw [hF x hx, hH x hx]
  apply congrArg (step x)
  apply predecessorRestrictionGraph_congr
  intro y hy
  have hyRel : ClassRel R y x :=
    (hpredecessors x hx y).mp hy |>.2
  exact hpredAgree y hyRel



end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookSetWellFounded


/- Source module: Solutions.Work_CUGCH_TextbookPredecessorClosure -/
section GCHSource_Work_CUGCH_TextbookPredecessorClosure
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Textbook predecessor closure for set-like class relations

This file formalizes Definition 3 and Propositions 1--2 of Section 6.1 in
Wang Fangting, *Axiomatic Set Theory*.

For a set-like class relation `R` on `A`, `displayedPredecessors A R hsetLike x`
is the displayed set

`{y in A | ClassRel R y x}`.

Starting with this set as `p_0(x)`, the next layer is the union of the
displayed predecessor sets of all members of the current layer.  The closure
is the union of all finite layers.  Both unions below are actual `ZFSet`s;
neither is merely an external `Set ZFSet`.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## Displayed predecessor sets -/

/-- A chosen actual set displaying the predecessors of `x` in `A`.

Outside `A` its value is defined to be empty.  All mathematical uses below
are at points of `A`, where `HasSetPredecessorsOn` gives the exact membership
description. -/
noncomputable def displayedPredecessors
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) : ZFSet.{u} :=
  by
    classical
    exact if hx : x ∈ A then Classical.choose (hsetLike x hx) else ∅

/-- The chosen set has exactly the predecessor members asserted by
set-likeness. -/
theorem displayedPredecessors_spec
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    IsPredecessorSet A R x (displayedPredecessors A R hsetLike x) := by
  unfold displayedPredecessors
  rw [dif_pos hx]
  exact Classical.choose_spec (hsetLike x hx)

/-- A displayed predecessor set is extensionally unique.  Thus the ambient
`Classical.choose` in `displayedPredecessors` does not add an object-level
choice principle: it selects the unique set whose existence is already part
of set-likeness. -/
theorem isPredecessorSet_unique
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    {x predecessors₁ predecessors₂ : ZFSet.{u}}
    (h₁ : IsPredecessorSet A R x predecessors₁)
    (h₂ : IsPredecessorSet A R x predecessors₂) :
    predecessors₁ = predecessors₂ := by
  apply ZFSet.ext
  intro y
  exact (h₁ y).trans (h₂ y).symm

/-- Any set with the required predecessor semantics is the chosen displayed
predecessor set. -/
theorem eq_displayedPredecessors_of_isPredecessorSet
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x predecessors : ZFSet.{u}}
    (hx : x ∈ A) (hpredecessors : IsPredecessorSet A R x predecessors) :
    predecessors = displayedPredecessors A R hsetLike x :=
  isPredecessorSet_unique hpredecessors
    (displayedPredecessors_spec hsetLike hx)



/-- Every member of a displayed predecessor set is in the relation's
domain. -/
theorem displayedPredecessors_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    (displayedPredecessors A R hsetLike x : Set ZFSet.{u}) ⊆ A := by
  intro y hy
  exact (displayedPredecessors_spec hsetLike hx y).mp hy |>.1

/-! ## The finite predecessor layers and their union -/

/-- The textbook finite predecessor layers:

* `p_0(x)` is the displayed predecessor set of `x`;
* `p_(n+1)(x)` is the union of the predecessor sets of members of `p_n(x)`.

The indexed union ranges over the actual members of `p_n(x)`, so every layer
is an actual `ZFSet`. -/
noncomputable def predecessorLayer
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) :
    Nat → ZFSet.{u}
  | 0 => displayedPredecessors A R hsetLike x
  | n + 1 => ZFSet.iUnion fun y : ZFCarrier (predecessorLayer A R hsetLike x n) =>
      displayedPredecessors A R hsetLike y.1

@[simp]
theorem predecessorLayer_zero
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) :
    predecessorLayer A R hsetLike x 0 =
      displayedPredecessors A R hsetLike x := rfl

@[simp]
theorem predecessorLayer_succ
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) (n : Nat) :
    predecessorLayer A R hsetLike x (n + 1) =
      ZFSet.iUnion fun y : ZFCarrier (predecessorLayer A R hsetLike x n) =>
        displayedPredecessors A R hsetLike y.1 := rfl

/-- Every finite predecessor layer remains inside `A`. -/
theorem predecessorLayer_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    ∀ n, (predecessorLayer A R hsetLike x n : Set ZFSet.{u}) ⊆ A := by
  intro n
  induction n with
  | zero =>
      exact displayedPredecessors_subset hsetLike hx
  | succ n ih =>
      intro z hz
      change z ∈ predecessorLayer A R hsetLike x (n + 1) at hz
      rw [predecessorLayer_succ] at hz
      rcases ZFSet.mem_iUnion.mp hz with ⟨y, hzy⟩
      have hyA : y.1 ∈ A := ih y.2
      exact (displayedPredecessors_spec hsetLike hyA z).mp hzy |>.1

/-- Exact membership semantics of a successor predecessor layer. -/
theorem mem_predecessorLayer_succ_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x z : ZFSet.{u}}
    (hx : x ∈ A) (n : Nat) :
    z ∈ predecessorLayer A R hsetLike x (n + 1) ↔
      ∃ y, y ∈ predecessorLayer A R hsetLike x n ∧
        z ∈ A ∧ ClassRel R z y := by
  rw [predecessorLayer_succ, ZFSet.mem_iUnion]
  constructor
  · rintro ⟨y, hzy⟩
    have hyA : y.1 ∈ A := predecessorLayer_subset hsetLike hx n y.2
    exact ⟨y.1, y.2, (displayedPredecessors_spec hsetLike hyA z).mp hzy⟩
  · rintro ⟨y, hyLayer, hzA, hzy⟩
    let yLayer : ZFCarrier (predecessorLayer A R hsetLike x n) :=
      ⟨y, hyLayer⟩
    refine ⟨yLayer, ?_⟩
    exact (displayedPredecessors_spec hsetLike
      (predecessorLayer_subset hsetLike hx n hyLayer) z).mpr ⟨hzA, hzy⟩

/-- `cl(A,x,R)`: the actual set obtained by taking the union of all finite
predecessor layers.  `ZFSet.iUnion` is the set-sized union indexed by `Nat`,
the external index type corresponding to `n in omega` in the displayed
textbook construction. -/
noncomputable def predecessorClosure
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion (predecessorLayer A R hsetLike x)

@[simp]
theorem mem_predecessorClosure_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    {hsetLike : HasSetPredecessorsOn A R} {x z : ZFSet.{u}} :
    z ∈ predecessorClosure A R hsetLike x ↔
      ∃ n, z ∈ predecessorLayer A R hsetLike x n := by
  simp [predecessorClosure]

/-- The predecessor closure of a point of `A` is still a subset of `A`. -/
theorem predecessorClosure_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    (predecessorClosure A R hsetLike x : Set ZFSet.{u}) ⊆ A := by
  intro z hz
  rcases mem_predecessorClosure_iff.mp hz with ⟨n, hzn⟩
  exact predecessorLayer_subset hsetLike hx n hzn

/-! ## Textbook Propositions 1 and 2 -/

/-- Textbook Proposition 1: if `y` belongs to `cl(A,x,R)`, then the displayed
predecessor set of `y` is contained in the same closure. -/
theorem displayedPredecessors_subset_predecessorClosure_of_mem
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x y : ZFSet.{u}}
    (hx : x ∈ A) (hy : y ∈ predecessorClosure A R hsetLike x) :
    displayedPredecessors A R hsetLike y ⊆
      predecessorClosure A R hsetLike x := by
  intro z hz
  rcases mem_predecessorClosure_iff.mp hy with ⟨n, hyn⟩
  apply mem_predecessorClosure_iff.mpr
  refine ⟨n + 1, ?_⟩
  apply (mem_predecessorLayer_succ_iff hsetLike hx n).mpr
  have hyA : y ∈ A := predecessorLayer_subset hsetLike hx n hyn
  exact ⟨y, hyn, (displayedPredecessors_spec hsetLike hyA z).mp hz⟩

/-- Relation form of Proposition 1: the closure is downward closed under
`R`.  `IsRelationOn` supplies the fact that the lower endpoint is in `A`. -/
theorem predecessorClosure_downward_closed
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R) {x y z : ZFSet.{u}}
    (hx : x ∈ A) (hy : y ∈ predecessorClosure A R hsetLike x)
    (hzy : ClassRel R z y) :
    z ∈ predecessorClosure A R hsetLike x := by
  have hyA : y ∈ A := predecessorClosure_subset hsetLike hx hy
  have hzPred : z ∈ displayedPredecessors A R hsetLike y :=
    (displayedPredecessors_spec hsetLike hyA z).mpr
      ⟨hrelation.left_mem hzy, hzy⟩
  exact displayedPredecessors_subset_predecessorClosure_of_mem
    hsetLike hx hy hzPred

/-- Textbook Proposition 2: an immediate predecessor has the smaller
predecessor closure. -/
theorem predecessorClosure_subset_of_rel
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R) {x y : ZFSet.{u}}
    (hyx : ClassRel R y x) :
    predecessorClosure A R hsetLike y ⊆
      predecessorClosure A R hsetLike x := by
  have hxA : x ∈ A := hrelation.right_mem hyx
  have hyA : y ∈ A := hrelation.left_mem hyx
  have hyLayerZero : y ∈ predecessorLayer A R hsetLike x 0 := by
    rw [predecessorLayer_zero]
    exact (displayedPredecessors_spec hsetLike hxA y).mpr ⟨hyA, hyx⟩
  have hyClosure : y ∈ predecessorClosure A R hsetLike x :=
    mem_predecessorClosure_iff.mpr ⟨0, hyLayerZero⟩
  have hlevels : ∀ n,
      predecessorLayer A R hsetLike y n ⊆
        predecessorClosure A R hsetLike x := by
    intro n
    induction n with
    | zero =>
        rw [predecessorLayer_zero]
        exact displayedPredecessors_subset_predecessorClosure_of_mem
          hsetLike hxA hyClosure
    | succ n ih =>
        intro z hz
        rcases (mem_predecessorLayer_succ_iff hsetLike hyA n).mp hz with
          ⟨s, hsn, hzA, hzs⟩
        have hsClosure : s ∈ predecessorClosure A R hsetLike x := ih hsn
        have hsA : s ∈ A := predecessorLayer_subset hsetLike hyA n hsn
        have hzPred : z ∈ displayedPredecessors A R hsetLike s :=
          (displayedPredecessors_spec hsetLike hsA z).mpr ⟨hzA, hzs⟩
        exact displayedPredecessors_subset_predecessorClosure_of_mem
          hsetLike hxA hsClosure hzPred
  intro z hz
  rcases mem_predecessorClosure_iff.mp hz with ⟨n, hzn⟩
  exact hlevels n hzn

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookPredecessorClosure


/- Source module: Solutions.Work_CUGCH_TextbookClassWellFounded -/
section GCHSource_Work_CUGCH_TextbookClassWellFounded
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Class minima from textbook set-well-foundedness

This file proves Theorem 1 of Section 6.1 in Wang Fangting,
*Axiomatic Set Theory*.  The definition of a well-founded class relation only
assumes minima for nonempty actual sets.  Set-likeness makes the finite
predecessor closure of a point an actual `ZFSet`; intersecting that closure
with an arbitrary nonempty external subclass then upgrades the conclusion to
all subclasses.

The file also records the textbook local recursion domain

`d_x = {x} union cl(A,x,R)`.
-/

section

open Set

universe u

namespace Constructible

noncomputable section

/-! ## The general class-minimum theorem -/

/-- Every nonempty external subclass of `A` has an `R`-minimal member.  This
is the conclusion of the textbook's general induction theorem, not the
definition of `HasSetMinimaOn`. -/
def HasClassMinimaOn (A : Set ZFSet.{u})
    (R : Set (Tuple ZFSet.{u} 2)) : Prop :=
  forall X : Set ZFSet.{u}, X ⊆ A -> X.Nonempty ->
    exists x, x ∈ X ∧ forall y, y ∈ X -> Not (ClassRel R y x)

/-- Textbook Section 6.1, Theorem 1.  The only set to which
`HasSetMinimaOn` is applied is `X intersect cl(A,x,R)`, represented by
Separation from the actual predecessor closure. -/
theorem hasClassMinimaOn_of_isWellFoundedSetLikeOn
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R) :
    HasClassMinimaOn A R := by
  rcases hR with ⟨hrelation, hsetMinima, hsetLike⟩
  intro X hXA hXnonempty
  rcases hXnonempty with ⟨x, hxX⟩
  have hxA : x ∈ A := hXA hxX
  by_cases hhasPredecessor : exists y, y ∈ X ∧ ClassRel R y x
  · let boundedBad : ZFSet.{u} :=
      (predecessorClosure A R hsetLike x).sep fun y => y ∈ X
    have hboundedSubset : forall y, y ∈ boundedBad -> y ∈ A := by
      intro y hy
      exact predecessorClosure_subset hsetLike hxA
        (ZFSet.mem_sep.mp hy).1
    have hboundedNonempty : exists y, y ∈ boundedBad := by
      rcases hhasPredecessor with ⟨y, hyX, hyx⟩
      have hyA : y ∈ A := hXA hyX
      have hyLayerZero :
          y ∈ predecessorLayer A R hsetLike x 0 := by
        rw [predecessorLayer_zero]
        exact (displayedPredecessors_spec hsetLike hxA y).mpr
          ⟨hyA, hyx⟩
      have hyClosure :
          y ∈ predecessorClosure A R hsetLike x :=
        mem_predecessorClosure_iff.mpr ⟨0, hyLayerZero⟩
      exact ⟨y, ZFSet.mem_sep.mpr ⟨hyClosure, hyX⟩⟩
    rcases hsetMinima boundedBad hboundedSubset hboundedNonempty with
      ⟨u, huBounded, huMinimal⟩
    have huClosure : u ∈ predecessorClosure A R hsetLike x :=
      (ZFSet.mem_sep.mp huBounded).1
    have huX : u ∈ X := (ZFSet.mem_sep.mp huBounded).2
    refine ⟨u, huX, ?_⟩
    intro v hvX hvu
    have hvClosure : v ∈ predecessorClosure A R hsetLike x :=
      predecessorClosure_downward_closed hrelation hsetLike hxA
        huClosure hvu
    exact huMinimal v (ZFSet.mem_sep.mpr ⟨hvClosure, hvX⟩) hvu
  · exact ⟨x, hxX, fun y hyX hyx => hhasPredecessor ⟨y, hyX, hyx⟩⟩

/-- After the textbook class-minimum theorem has been proved, its relation on
the Lean subtype of `A` is genuinely well-founded.  This is a derived bridge,
not a strengthening silently inserted into the definition. -/
theorem wellFounded_classRel_zfSubtype
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hR : IsWellFoundedSetLikeOn A R) :
    WellFounded (fun y x : {z : ZFSet.{u} // z ∈ A} =>
      ClassRel R y.1 x.1) := by
  apply WellFounded.wellFounded_iff_has_min.mpr
  intro s hs
  let X : Set ZFSet.{u} := Subtype.val '' s
  have hXA : X ⊆ A := by
    rintro z ⟨zA, _hzS, rfl⟩
    exact zA.2
  have hXnonempty : X.Nonempty := by
    rcases hs with ⟨zA, hzS⟩
    exact ⟨zA.1, ⟨zA, hzS, rfl⟩⟩
  rcases hasClassMinimaOn_of_isWellFoundedSetLikeOn hR X hXA
      hXnonempty with ⟨z, hzX, hzMinimal⟩
  rcases hzX with ⟨zA, hzS, rfl⟩
  refine ⟨zA, hzS, ?_⟩
  intro yA hyS hyz
  exact hzMinimal yA.1 ⟨yA, hyS, rfl⟩ hyz

/-! ## The local domain used in the recursion proof -/

/-- The textbook local recursion domain `d_x = {x} union cl(A,x,R)`. -/
noncomputable def localRecursionDomain
    (A : Set ZFSet.{u}) (R : Set (Tuple ZFSet.{u} 2))
    (hsetLike : HasSetPredecessorsOn A R) (x : ZFSet.{u}) : ZFSet.{u} :=
  ({x} : ZFSet.{u}) ∪ predecessorClosure A R hsetLike x

@[simp]
theorem mem_localRecursionDomain_iff
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    {hsetLike : HasSetPredecessorsOn A R} {x y : ZFSet.{u}} :
    y ∈ localRecursionDomain A R hsetLike x ↔
      y = x ∨ y ∈ predecessorClosure A R hsetLike x := by
  simp [localRecursionDomain]

/-- The local domain is contained in `A` whenever its top point is in `A`. -/
theorem localRecursionDomain_subset
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hsetLike : HasSetPredecessorsOn A R) {x : ZFSet.{u}}
    (hx : x ∈ A) :
    (localRecursionDomain A R hsetLike x : Set ZFSet.{u}) ⊆ A := by
  intro y hy
  rcases mem_localRecursionDomain_iff.mp hy with rfl | hyClosure
  · exact hx
  · exact predecessorClosure_subset hsetLike hx hyClosure

/-- Every predecessor of a point in `d_x` again belongs to `d_x`. -/
theorem localRecursionDomain_predecessorClosed
    {A : Set ZFSet.{u}} {R : Set (Tuple ZFSet.{u} 2)}
    (hrelation : IsRelationOn A R)
    (hsetLike : HasSetPredecessorsOn A R) {x y z : ZFSet.{u}}
    (hx : x ∈ A)
    (hy : y ∈ localRecursionDomain A R hsetLike x)
    (hzy : ClassRel R z y) :
    z ∈ localRecursionDomain A R hsetLike x := by
  apply mem_localRecursionDomain_iff.mpr
  right
  rcases mem_localRecursionDomain_iff.mp hy with hyEq | hyClosure
  · subst y
    have hzA : z ∈ A := hrelation.left_mem hzy
    have hzLayerZero : z ∈ predecessorLayer A R hsetLike x 0 := by
      rw [predecessorLayer_zero]
      exact (displayedPredecessors_spec hsetLike hx z).mpr ⟨hzA, hzy⟩
    exact mem_predecessorClosure_iff.mpr ⟨0, hzLayerZero⟩
  · exact predecessorClosure_downward_closed hrelation hsetLike hx
      hyClosure hzy

end

end Constructible

end
end GCHSource_Work_CUGCH_TextbookClassWellFounded


