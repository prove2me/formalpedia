-- Prove2me | Definitions.Def_CH_ConstructibleGCH_Library07
-- name    : CH_ConstructibleGCH_Library07
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T07:24:30.661401+00:00
-- url     : https://prove2.me/theorems/73529290-1cff-464d-9fbe-0420d81811bb
-- title:
--   Transitive-model Separation and Replacement graphs
-- statement:
--   This library supplies the first-order scheme interfaces for transitive models of ZF, including definable Separation sets and Replacement function graphs. It also supplies restriction graphs, indexed unions and canonical selectors for increasing constructible stages.
--
--   The original constructible-universe formalization is by **Zike Liu**, copyright 2026, Apache-2.0; see the [pinned source](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53). This Prove2Me adaptation preserves the original copyright notices.
--
--   This module includes supporting proofs required by its definitions and constructor data.
--
--   Mathematical references: Andrew Marks, [*Set Theory*, Lemma 21.3 and Corollary 21.4, printed pp. 90–91](https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf); Kurt Gödel, [“The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis,” PNAS 24 (1938), 556–557](https://doi.org/10.1073/pnas.24.12.556); and Gödel’s 1940 Princeton monograph, *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory* ([publisher note](https://assets.press.princeton.edu/about_pup/PUP100/book/1hGodel.pdf)). The upstream textbook E/Df construction cites Wang Fangting, *Axiomatic Set Theory*, §§6.3–6.8.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Zike Liu, constructible-universe formalization, Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53. Source modules: https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/RestrictionGraph.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/Absoluteness.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TransitiveZFModel.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/FormulaSchemeBridge.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TransitiveZFClosure.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TransitiveZFSeparation.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/TransitiveZFFunctionGraph.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/ReplacementFunctionGraphLCarrier.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalCardinalUnion.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/InternalStageCardinalUnion.lean#L1; https://github.com/05-02-07/lean-constructible-universe/blob/7f5a7d03d63d9769172f17350bbe8303996e5b53/ConstructibleUniverse/SetTheory/ZFC/Constructible/CanonicalLimitStageSelector.lean#L1

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

import Definitions.Def_CH_ConstructibleGCH_Library06
/-
Prove2Me adaptation of the constructible-universe formalization by Zike Liu,
Apache-2.0, commit 7f5a7d03d63d9769172f17350bbe8303996e5b53.
Original copyright notices are preserved below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-/

set_option Elab.async false
set_option maxHeartbeats 1000000

/- Source module: Solutions.Work_CUGCH_RestrictionGraph -/
section GCHSource_Work_CUGCH_RestrictionGraph
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Set-sized restriction graphs

This file contains the representation-neutral facts about the actual
Kuratowski graph of an external function restricted to an actual `ZFSet`.
It makes no assertion that the graph belongs to a particular model; that
additional fact must be obtained from that model's Replacement scheme.
-/

section

universe u

namespace Constructible

noncomputable section

/-- The actual Kuratowski graph of `f` restricted to the members of
`domain`. -/
noncomputable def predecessorRestrictionGraph
    (domain : ZFSet.{u}) (f : ZFSet.{u} -> ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun x : {x : ZFSet.{u} // x ∈ domain} =>
    ZFSet.pair x.1 (f x.1)

/-- Membership in the restriction graph has the expected semantics. -/
@[simp]
theorem mem_predecessorRestrictionGraph_iff
    {domain p : ZFSet.{u}} {f : ZFSet.{u} -> ZFSet.{u}} :
    p ∈ predecessorRestrictionGraph domain f <->
      exists x : ZFSet.{u}, x ∈ domain ∧
        ZFSet.pair x (f x) = p := by
  rw [predecessorRestrictionGraph, ZFSet.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.1, x.2, hx⟩
  · rintro ⟨x, hx, hp⟩
    exact ⟨⟨x, hx⟩, hp⟩

/-- Every domain member contributes its ordered pair. -/
theorem pair_mem_predecessorRestrictionGraph
    {domain x : ZFSet.{u}} (f : ZFSet.{u} -> ZFSet.{u})
    (hx : x ∈ domain) :
    ZFSet.pair x (f x) ∈ predecessorRestrictionGraph domain f := by
  exact mem_predecessorRestrictionGraph_iff.mpr ⟨x, hx, rfl⟩

/-- Pointwise agreement on the domain gives equality of the actual graphs. -/
theorem predecessorRestrictionGraph_congr
    {domain : ZFSet.{u}} {f g : ZFSet.{u} -> ZFSet.{u}}
    (hfg : forall x : ZFSet.{u}, x ∈ domain -> f x = g x) :
    predecessorRestrictionGraph domain f =
      predecessorRestrictionGraph domain g := by
  apply ZFSet.ext
  intro p
  simp only [mem_predecessorRestrictionGraph_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [hfg x hx]⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [hfg x hx]⟩



end

end Constructible

end
end GCHSource_Work_CUGCH_RestrictionGraph


/- Source module: Solutions.Work_CUGCH_Absoluteness -/
section GCHSource_Work_CUGCH_Absoluteness
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Restriction semantics for absoluteness

This file isolates the semantic core of the textbook definition of
absoluteness.  If `M` is an external class of sets, an `n`-ary relation is
absolute to `M` when the relation interpreted by its defining formula in
`M` is exactly the ambient relation restricted to tuples from `M`.

The corresponding definition for a function has two parts: its values on
arguments from `M` must lie in `M`, and its graph formula must have the
expected truth value in `M`.  The closure condition is stated explicitly;
correctness of a graph formula for candidate outputs already in `M` does not
by itself imply that the actual function value belongs to `M`.

No transitivity or set-theoretic axioms are needed for these semantic
equivalences.  Those hypotheses enter later, when closure and preservation
of recursive definitions are proved.
-/

section

open Set

universe u

namespace Constructible

namespace Model

/-! ## Relations and classes -/

/-- Every coordinate of `s` belongs to the external carrier `M`. -/
def TupleIn (M : Set ZFSet.{u}) {n : Nat}
    (s : Tuple ZFSet.{u} n) : Prop :=
  forall i, s i ∈ M

@[simp]
theorem tupleIn_snoc_iff {M : Set ZFSet.{u}} {n : Nat}
    {s : Tuple ZFSet.{u} n} {x : ZFSet.{u}} :
    TupleIn M (snoc s x) ↔ TupleIn M s ∧ x ∈ M := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      simpa using h i.castSucc
    · simpa using h (Fin.last n)
  · rintro ⟨hs, hx⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using hs j

















/-! ## Functions -/









end Model

end Constructible

end
end GCHSource_Work_CUGCH_Absoluteness


/- Source module: Solutions.Work_CUGCH_TransitiveZFModel -/
section GCHSource_Work_CUGCH_TransitiveZFModel
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Transitive set models of ZF

This file packages the standard set-model hypotheses used in the textbook
development of absoluteness.  The carrier `M` is a genuine `ZFSet`.
`ZFCarrier M` is the Lean subtype of its members, equipped with ambient
membership, while `(M : Set ZFSet)` is only the corresponding external
membership predicate.

The model predicate contains exactly two mathematical assumptions:
transitivity of `M` and satisfaction of the full first-order theory ZF by
the inherited membership structure.  In particular, no Choice axiom,
recursive closure, or absoluteness conclusion is built into the definition.

The remaining results are representation bridges.  They identify the
intrinsically scoped `FOFormula` semantics, Mathlib bounded-formula
semantics, and raw-domain `SatisfiesIn` semantics on the same carrier.  These
bridges require neither transitivity nor the ZF model hypothesis.
-/

section

universe u

namespace Constructible

namespace Model

/-! ## The standard transitive-set-model predicate -/

/--
The internal set `M`, with membership inherited from ambient `ZFSet`, models
the full first-order theory ZF.

The structure instance is local to this proposition.  This avoids installing
a competing global structure on the reducible subtype `ZFCarrier M`.
-/
def ZFSetModelsZF (M : ZFSet.{u}) : Prop :=
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF

/-- A standard transitive set model of ZF, stated without hidden closure. -/
def IsTransitiveZFModel (M : ZFSet.{u}) : Prop :=
  M.IsTransitive ∧ ZFSetModelsZF M

/-! ## Formula-semantics bridges -/

/--
Satisfaction on the subtype of members of an internal `ZFSet` agrees with
raw satisfaction whose quantifiers are restricted to that set.
-/
@[simp]
theorem satisfies_zfCarrier_iff_satisfiesIn (M : ZFSet.{u}) {n : Nat}
    (phi : FOFormula n) (s : Tuple (ZFCarrier M) n) :
    FOFormula.Satisfies (zfCarrierMem M) phi s ↔
      SatisfiesIn (M : Set ZFSet.{u}) phi (fun i => (s i).1) := by
  change
    FOFormula.Satisfies (fun x y : ZFCarrier M => x.1 ∈ y.1) phi s ↔
      SatisfiesIn (M : Set ZFSet.{u}) phi (fun i => (s i).1)
  exact satisfies_subtype_iff_satisfiesIn
    (M : Set ZFSet.{u}) phi s

/--
Forward syntax bridge: translating an `FOFormula` to Mathlib's bounded
formula syntax and realizing it on `ZFCarrier M` is the same as restricted
raw satisfaction in `M`.
-/
@[simp]
theorem realizes_toBoundedFormula_zfCarrier_iff_satisfiesIn
    (M : ZFSet.{u}) {n : Nat} (phi : FOFormula n)
    (s : Tuple (ZFCarrier M) n) :
    realizes (zfCarrierMem M) (toBoundedFormula phi) s ↔
      SatisfiesIn (M : Set ZFSet.{u}) phi (fun i => (s i).1) := by
  exact (realizes_toBoundedFormula (zfCarrierMem M) phi s).trans
    (satisfies_zfCarrier_iff_satisfiesIn M phi s)

/--
Reverse syntax bridge: every Mathlib bounded formula in the function-free
membership language has the same restricted semantics as its normalization
to `FOFormula`.
-/
@[simp]
theorem realizes_zfCarrier_iff_satisfiesIn_fromBoundedFormula
    (M : ZFSet.{u}) {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty n)
    (s : Tuple (ZFCarrier M) n) :
    realizes (zfCarrierMem M) phi s ↔
      SatisfiesIn (M : Set ZFSet.{u}) (fromBoundedFormula phi)
        (fun i => (s i).1) := by
  exact (realize_fromBoundedFormula (zfCarrierMem M) phi s).trans
    (satisfies_zfCarrier_iff_satisfiesIn M
      (fromBoundedFormula phi) s)

end Model

end Constructible

end
end GCHSource_Work_CUGCH_TransitiveZFModel


/- Source module: Solutions.Work_CUGCH_FormulaSchemeBridge -/
section GCHSource_Work_CUGCH_FormulaSchemeBridge
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Formula bridge for the ZF axiom schemes

The construction syntax `FOFormula n` treats its `n` variables as one scoped
tuple.  The Separation and Replacement schemes in `Theory.ZF` instead use
Mathlib formulas whose variables are free variables indexed by `Fin n`.
This file moves the same variables between those two presentations and proves
that realization is unchanged.

This is only a syntax/semantics theorem.  It does not assert that an ambient
separation or replacement result belongs to a particular model.
-/

section

universe u

namespace Constructible.Model

/-- Turn the scoped variables of an `FOFormula` into Mathlib free variables,
as required by the formulas indexing the ZF axiom schemes. -/
def toSchemeFormula {n : Nat} (phi : FOFormula n) :
    FirstOrder.Language.setTheory.Formula (Fin n) :=
  (toBoundedFormula phi).toFormula.relabel
    (Sum.elim Empty.elim id)

/-- Moving all scoped variables to free-variable positions preserves the
independent `FOFormula` satisfaction semantics. -/
@[simp]
theorem realize_toSchemeFormula {A : Type u} (E : A -> A -> Prop)
    {n : Nat} (phi : FOFormula n) (s : Tuple A n) :
    letI : FirstOrder.Language.setTheory.Structure A :=
      FirstOrder.Language.setTheoryStructure E
    (toSchemeFormula phi).Realize s <->
      FOFormula.Satisfies E phi s := by
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  rw [toSchemeFormula, FirstOrder.Language.Formula.realize_relabel,
    FirstOrder.Language.BoundedFormula.realize_toFormula]
  have hfree :
      (s ∘ Sum.elim Empty.elim id) ∘ Sum.inl =
        (Empty.elim : Empty -> A) := by
    funext i
    exact Empty.elim i
  have hscoped :
      (s ∘ Sum.elim Empty.elim id) ∘ Sum.inr = s := by
    funext i
    rfl
  rw [hfree, hscoped]
  exact realizes_toBoundedFormula E phi s

end Constructible.Model

end
end GCHSource_Work_CUGCH_FormulaSchemeBridge


/- Source module: Solutions.Work_CUGCH_TransitiveZFClosure -/
section GCHSource_Work_CUGCH_TransitiveZFClosure
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/



/-!
# Basic closure of transitive set models of ZF

This file proves the elementary closure facts used in Section 6.2 of Wang
Fangting, *Axiomatic Set Theory*.  Each object is first obtained from the
corresponding axiom inside a set model `M`.  Transitivity then shows that the
internal object is extensionally equal to the ambient `ZFSet` construction.

No ambient separation or replacement operation is used as a substitute for
an internal object.  Power set is deliberately absent: an internal power set
of `x` need not be the ambient `x.powerset`.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-- The empty-set axiom in a transitive ZF model produces the ambient empty
set, not merely an object with no members from the model. -/
theorem exists_zfCarrier_eq_empty {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) :
    Exists fun e : ZFCarrier M => e.1 = (∅ : ZFSet.{u}) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .emptySet with ⟨e, he⟩
  refine ⟨e, ?_⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hze
    have hzM : z ∈ M := hM.1.mem_trans hze e.2
    have hzNot : z ∉ e.1 := by
      have hzNotInternal := he ⟨z, hzM⟩
      change z ∉ e.1 at hzNotInternal
      exact hzNotInternal
    exact (hzNot hze).elim
  · intro hzEmpty
    exact (ZFSet.notMem_empty z hzEmpty).elim

/-- A transitive ZF model contains the ambient empty set. -/
theorem empty_mem_of_isTransitiveZFModel {M : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) :
    (∅ : ZFSet.{u}) ∈ M := by
  rcases exists_zfCarrier_eq_empty hM with ⟨e, he⟩
  simpa only [he] using e.2

/-- The Pairing axiom in a transitive ZF model produces the ambient unordered
pair of its two arguments. -/
theorem exists_zfCarrier_eq_unorderedPair {M x y : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) (hy : y ∈ M) :
    Exists fun p : ZFCarrier M => p.1 = ({x, y} : ZFSet.{u}) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  let xM : ZFCarrier M := ⟨x, hx⟩
  let yM : ZFCarrier M := ⟨y, hy⟩
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .pairing xM yM with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hzp
    have hzM : z ∈ M := hM.1.mem_trans hzp p.2
    let zM : ZFCarrier M := ⟨z, hzM⟩
    have hzPair := (hp zM).mp hzp
    rcases hzPair with hzx | hzy
    · exact ZFSet.mem_pair.mpr (Or.inl (congrArg Subtype.val hzx))
    · exact ZFSet.mem_pair.mpr (Or.inr (congrArg Subtype.val hzy))
  · intro hzPair
    rcases ZFSet.mem_pair.mp hzPair with hzx | hzy
    · subst z
      exact (hp xM).mpr (Or.inl rfl)
    · subst z
      exact (hp yM).mpr (Or.inr rfl)

/-- A transitive ZF model is closed under ambient unordered pairing. -/
theorem unorderedPair_mem_of_isTransitiveZFModel {M x y : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) (hy : y ∈ M) :
    ({x, y} : ZFSet.{u}) ∈ M := by
  rcases exists_zfCarrier_eq_unorderedPair hM hx hy with ⟨p, hp⟩
  simpa only [hp] using p.2

/-- A transitive ZF model is closed under ambient singletons. -/
theorem singleton_mem_of_isTransitiveZFModel {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    ({x} : ZFSet.{u}) ∈ M := by
  rw [← ZFSet.pair_eq_singleton x]
  exact unorderedPair_mem_of_isTransitiveZFModel hM hx hx

/-- The Union axiom in a transitive ZF model produces the ambient union of
the argument. -/
theorem exists_zfCarrier_eq_sUnion {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    Exists fun union : ZFCarrier M => union.1 = ZFSet.sUnion x := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  let xM : ZFCarrier M := ⟨x, hx⟩
  rcases FirstOrder.SetTheory.ZFAxiom.toProp_of_model
      (M := ZFCarrier M) .union xM with ⟨union, hunion⟩
  refine ⟨union, ?_⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro hzUnion
    have hzM : z ∈ M := hM.1.mem_trans hzUnion union.2
    rcases (hunion ⟨z, hzM⟩).mp hzUnion with ⟨yM, hyx, hzy⟩
    exact ZFSet.mem_sUnion.mpr ⟨yM.1, hyx, hzy⟩
  · intro hzUnion
    rcases ZFSet.mem_sUnion.mp hzUnion with ⟨y, hyx, hzy⟩
    have hyM : y ∈ M := hM.1.mem_trans hyx hx
    have hzM : z ∈ M := hM.1.mem_trans hzy hyM
    exact (hunion ⟨z, hzM⟩).mpr ⟨⟨y, hyM⟩, hyx, hzy⟩

/-- A transitive ZF model is closed under ambient union. -/
theorem sUnion_mem_of_isTransitiveZFModel {M x : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) :
    ZFSet.sUnion x ∈ M := by
  rcases exists_zfCarrier_eq_sUnion hM hx with ⟨union, hunion⟩
  simpa only [hunion] using union.2

/-- A transitive ZF model is closed under the ambient Kuratowski ordered-pair
coding used throughout the constructible-universe development. -/
theorem kuratowskiPair_mem_of_isTransitiveZFModel {M x y : ZFSet.{u}}
    (hM : IsTransitiveZFModel M) (hx : x ∈ M) (hy : y ∈ M) :
    ZFSet.pair x y ∈ M := by
  have hSingleton : ({x} : ZFSet.{u}) ∈ M :=
    singleton_mem_of_isTransitiveZFModel hM hx
  have hPair : ({x, y} : ZFSet.{u}) ∈ M :=
    unorderedPair_mem_of_isTransitiveZFModel hM hx hy
  simpa only [ZFSet.pair] using
    unorderedPair_mem_of_isTransitiveZFModel hM hSingleton hPair

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TransitiveZFClosure


/- Source module: Solutions.Work_CUGCH_TransitiveZFSeparation -/
section GCHSource_Work_CUGCH_TransitiveZFSeparation
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Separation inside a transitive ZF set model

For an `FOFormula`, parameters from a transitive ZF set model `M`, and an
internal set `a`, the Separation scheme first supplies an internal result.
The formula-syntax bridges and transitivity then identify that result with the
ambient `ZFSet.sep` whose predicate is restricted satisfaction in `M`.

Thus `ZFSet.sep` occurs only as an extensional description of an object already
obtained from the model's own Separation axiom.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-- The raw tuple underlying a tuple of members of an internal set. -/
def zfCarrierTupleVal {M : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier M) n) : Tuple ZFSet.{u} n :=
  fun i => (s i).1

/-- Taking values commutes with appending one member to a subtype tuple. -/
theorem zfCarrierTupleVal_finSnoc {M : ZFSet.{u}} {n : Nat}
    (s : Tuple (ZFCarrier M) n) (x : ZFCarrier M) :
    zfCarrierTupleVal (Fin.snoc s x) =
      snoc (zfCarrierTupleVal s) x.1 := by
  rw [← snoc_eq_finSnoc]
  exact subtypeVal_snoc s x

/-- A formula in scheme-variable form has exactly the expected raw restricted
semantics after appending one candidate element. -/
theorem realize_toSchemeFormula_finSnoc_iff_satisfiesIn
    {M : ZFSet.{u}} {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier M) n) (x : ZFCarrier M) :
    letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
      FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
    (toSchemeFormula phi).Realize (Fin.snoc params x) <->
      SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (zfCarrierTupleVal params) x.1) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  calc
    (toSchemeFormula phi).Realize (Fin.snoc params x) <->
        FOFormula.Satisfies (zfCarrierMem M) phi
          (Fin.snoc params x) :=
      realize_toSchemeFormula (zfCarrierMem M) phi (Fin.snoc params x)
    _ <-> SatisfiesIn (M : Set ZFSet.{u}) phi
          (zfCarrierTupleVal (Fin.snoc params x)) :=
      satisfies_zfCarrier_iff_satisfiesIn M phi (Fin.snoc params x)
    _ <-> SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (zfCarrierTupleVal params) x.1) := by
      rw [zfCarrierTupleVal_finSnoc]

/-- The internal witness supplied by Separation is extensionally the ambient
restricted-satisfaction separation of `a`. -/
theorem exists_zfCarrier_eq_satisfiesIn_sep
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M) :
    Exists fun b : ZFCarrier M =>
      b.1 = a.1.sep fun x =>
        SatisfiesIn (M : Set ZFSet.{u}) phi
          (snoc (zfCarrierTupleVal params) x) := by
  letI : FirstOrder.Language.setTheory.Structure (ZFCarrier M) :=
    FirstOrder.Language.setTheoryStructure (zfCarrierMem M)
  letI : ZFCarrier M ⊨ FirstOrder.Language.Theory.ZF := by
    simpa only [ZFSetModelsZF] using hM.2
  have hSeparation := FirstOrder.SetTheory.ZFAxiom.toProp_of_model
    (M := ZFCarrier M)
    (.separation n (toSchemeFormula phi))
  rcases hSeparation params a with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sep]
  constructor
  · intro hxb
    have hxM : x ∈ M := hM.1.mem_trans hxb b.2
    let xM : ZFCarrier M := ⟨x, hxM⟩
    have hInternal := (hb xM).mp hxb
    change x ∈ a.1 ∧
      (toSchemeFormula phi).Realize (Fin.snoc params xM) at hInternal
    exact ⟨hInternal.1,
      (realize_toSchemeFormula_finSnoc_iff_satisfiesIn
        phi params xM).mp hInternal.2⟩
  · rintro ⟨hxa, hphi⟩
    have hxM : x ∈ M := hM.1.mem_trans hxa a.2
    let xM : ZFCarrier M := ⟨x, hxM⟩
    apply (hb xM).mpr
    change x ∈ a.1 ∧
      (toSchemeFormula phi).Realize (Fin.snoc params xM)
    exact ⟨hxa,
      (realize_toSchemeFormula_finSnoc_iff_satisfiesIn
        phi params xM).mpr hphi⟩

/-- The ambient set described by restricted satisfaction belongs to `M`
because it is equal to the model's own Separation witness. -/
theorem satisfiesIn_sep_mem_of_isTransitiveZFModel
    {M : ZFSet.{u}} (hM : IsTransitiveZFModel M)
    {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple (ZFCarrier M) n) (a : ZFCarrier M) :
    (a.1.sep fun x =>
      SatisfiesIn (M : Set ZFSet.{u}) phi
        (snoc (zfCarrierTupleVal params) x)) ∈ M := by
  rcases exists_zfCarrier_eq_satisfiesIn_sep hM phi params a with
    ⟨b, hb⟩
  simpa only [hb] using b.2

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TransitiveZFSeparation


/- Source module: Solutions.Work_CUGCH_TransitiveZFFunctionGraph -/
section GCHSource_Work_CUGCH_TransitiveZFFunctionGraph
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Internally represented function graphs in transitive ZF set models

Given a formula `phi(params, x, y)` that has one unique model-internal value
for each `x` in an internal domain, this file constructs the actual internal
Kuratowski graph

`{ <x,y> | x in a and M satisfies phi(params,x,y) }`.

The graph is obtained by applying the model's Replacement scheme to the
object-language formula

`exists y, phi(params,x,y) and q = <x,y>`.

Thus neither an external Lean function nor `ZFSet.range` is used as a
substitute for the internally represented graph.
-/

section

universe u

namespace Constructible.Model

noncomputable section

/-! ## The object-language graph-output formula -/

/-- Rename `(params,x,y)` into `(params,x,q,y)`. -/
def replacementGraphPredicateRename {n : Nat} :
    Fin (n + 2) -> Fin (n + 3) :=
  Fin.lastCases
    (Fin.last (n + 2))
    (fun j => Fin.lastCases
      (Fin.castSucc (Fin.castSucc (Fin.last n)))
      (fun i => i.castSucc.castSucc.castSucc)
      j)

/-- The renaming has the intended effect after introducing the value
witness `y`. -/
theorem comp_replacementGraphPredicateRename {A : Type u} {n : Nat}
    (params : Tuple A n) (x q y : A) :
    (fun i => snoc (snoc (snoc params x) q) y
      (replacementGraphPredicateRename i)) =
      snoc (snoc params x) y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [replacementGraphPredicateRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [replacementGraphPredicateRename]
    · simp [replacementGraphPredicateRename]

/-- The input coordinate in `(params,x,q,y)`. -/
def replacementGraphInputIndex (n : Nat) : Fin (n + 3) :=
  (Fin.last n).castSucc.castSucc

/-- The prospective pair coordinate in `(params,x,q,y)`. -/
def replacementGraphPairIndex (n : Nat) : Fin (n + 3) :=
  (Fin.last (n + 1)).castSucc

/-- The value witness coordinate in `(params,x,q,y)`. -/
def replacementGraphValueIndex (n : Nat) : Fin (n + 3) :=
  Fin.last (n + 2)

/-- `replacementGraphFormula phi(params,x,q)` says that `q` is the
Kuratowski pair of `x` with the unique value selected by `phi`. -/
def replacementGraphFormula {n : Nat} (phi : FOFormula (n + 2)) :
    FOFormula (n + 2) :=
  .ex (.conj
    (FOFormula.rename replacementGraphPredicateRename phi)
    (Delta0Formula.kuratowskiPairEqAt
      (replacementGraphPairIndex n)
      (replacementGraphInputIndex n)
      (replacementGraphValueIndex n)).toFO)







/-! ## Internal graph existence -/



/-! ## Identification with an ambient function restriction -/





/-! ## Packaging through `FunctionAbsoluteTo` -/





end

end Constructible.Model

end
end GCHSource_Work_CUGCH_TransitiveZFFunctionGraph


/- Source module: Solutions.Work_CUGCH_ReplacementFunctionGraphLCarrier -/
section GCHSource_Work_CUGCH_ReplacementFunctionGraphLCarrier
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/





/-!
# Replacement function graphs in the constructible universe

Given a formula with one unique `LCarrier` output on an internal domain,
Replacement is applied to the formula which outputs the Kuratowski pair of
the input and value.  The result is an actual member of `L` whose elements
are exactly those graph pairs.  No external `ZFSet.range` is used.
-/

section

universe u

namespace Constructible.Model

noncomputable section

local notation "LMem" => lCarrierMem

/-! ## Exact semantics of the pair-output formula -/

@[simp]
theorem satisfies_replacementGraphFormula_lCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (x q : LCarrier.{u}) :
    FOFormula.Satisfies LMem (replacementGraphFormula phi)
        (snoc (snoc params x) q) ↔
      ∃ y : LCarrier.{u},
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y) ∧
          q.1 = ZFSet.pair x.1 y.1 := by
  simp only [replacementGraphFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename,
    comp_replacementGraphPredicateRename,
    replacementGraphPairIndex, replacementGraphInputIndex,
    replacementGraphValueIndex]
  apply exists_congr
  intro y
  apply and_congr_right
  intro _hy
  rw [Delta0Formula.satisfies_toFO_lCarrier_absolute,
    Delta0Formula.satisfies_toFO,
    Delta0Formula.satisfies_kuratowskiPairEqAt]
  simp only [snoc_last, snoc_castSucc]

/-! ## The actual Replacement graph -/

/-- Formula-functional Replacement on `LCarrier` produces the actual
Kuratowski graph, with an exact raw-membership specification. -/
theorem exists_replacementFunctionGraphLCarrier
    {n : Nat} (phi : FOFormula (n + 2))
    (params : Tuple LCarrier.{u} n) (domain : LCarrier.{u})
    (hfun : ∀ x : LCarrier.{u}, x.1 ∈ domain.1 →
      ExistsUnique fun y : LCarrier.{u} =>
        FOFormula.Satisfies LMem phi (snoc (snoc params x) y)) :
    ∃ graph : LCarrier.{u}, ∀ q : ZFSet.{u},
      q ∈ graph.1 ↔
        ∃ x : LCarrier.{u}, x.1 ∈ domain.1 ∧
          ∃ y : LCarrier.{u},
            FOFormula.Satisfies LMem phi
              (snoc (snoc params x) y) ∧
            q = ZFSet.pair x.1 y.1 := by
  have hpairFun : ∀ x : LCarrier.{u}, x.1 ∈ domain.1 →
      ExistsUnique fun q : LCarrier.{u} =>
        FOFormula.Satisfies LMem (replacementGraphFormula phi)
          (snoc (snoc params x) q) := by
    intro x hx
    rcases hfun x hx with ⟨y, hy, hyUnique⟩
    let q : LCarrier.{u} := orderedPairLCarrier x y
    refine ⟨q, ?_, ?_⟩
    · apply (satisfies_replacementGraphFormula_lCarrier
        phi params x q).mpr
      exact ⟨y, hy, rfl⟩
    · intro q' hq'
      rcases (satisfies_replacementGraphFormula_lCarrier
          phi params x q').mp hq' with
        ⟨y', hy', hq'⟩
      have hyy' : y' = y := hyUnique y' hy'
      apply Subtype.ext
      rw [hq', hyy']
      rfl
  rcases exists_replacementLCarrier
      (replacementGraphFormula phi) params domain hpairFun with
    ⟨graph, hgraph⟩
  refine ⟨graph, ?_⟩
  intro q
  constructor
  · intro hq
    let qL : LCarrier.{u} := ⟨q, mem_L_of_mem hq graph.2⟩
    rcases (hgraph qL).mp hq with ⟨x, hx, hpairFormula⟩
    rcases (satisfies_replacementGraphFormula_lCarrier
        phi params x qL).mp hpairFormula with
      ⟨y, hy, hqPair⟩
    exact ⟨x, hx, y, hy, hqPair⟩
  · rintro ⟨x, hx, y, hy, hqPair⟩
    have hqL : q ∈ L := by
      rw [hqPair]
      exact orderedPair_mem_L x.2 y.2
    let qL : LCarrier.{u} := ⟨q, hqL⟩
    apply (hgraph qL).mpr
    refine ⟨x, hx, ?_⟩
    apply (satisfies_replacementGraphFormula_lCarrier
      phi params x qL).mpr
    exact ⟨y, hy, hqPair⟩

end

end Constructible.Model

end
end GCHSource_Work_CUGCH_ReplacementFunctionGraphLCarrier


/- Source module: Solutions.Work_CUGCH_InternalCardinalUnion -/
section GCHSource_Work_CUGCH_InternalCardinalUnion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# Internally represented injections for indexed unions

This file isolates the graph-theoretic core of the cardinal union argument.
All functions in the statement are represented by actual constructible sets.
In particular, the family of fiber injections is an input graph rather than
an ambient choice function.
-/

section

universe u

namespace Constructible.ContinuumFormula

/-- A total internally represented function graph. -/
def IsFunctionGraph {A : Type u} (E : A -> A -> Prop)
    (graph domain codomain : A) : Prop :=
  IsGraphBetween E graph domain codomain /\
    forall x : A, E x domain -> HasUniqueImage E graph x codomain





/-- The semantic relation which combines a selected fiber index with the
value of the selected fiber injection. -/
def CardinalUnionRel {A : Type u} (E : A -> A -> Prop)
    (selector indexedFamily injectionFamily x output : A) : Prop :=
  exists index fiber injection value : A,
    GraphValue E selector x index /\
      GraphValue E indexedFamily index fiber /\
        GraphValue E injectionFamily index injection /\
          GraphValue E injection x value /\
            IsKuratowskiPairOf E output index value

/-- Layout `[selector,indexedFamily,injectionFamily,x,output]`.
The four witnesses are respectively the chosen index, its fiber, the
fiber-injection graph, and the image value. -/
def cardinalUnionPredicate : FOFormula 5 :=
  .ex (.ex (.ex (.ex
    (.conj
      (graphValueAt (0 : Fin 9) (3 : Fin 9) (5 : Fin 9))
      (.conj
        (graphValueAt (1 : Fin 9) (5 : Fin 9) (6 : Fin 9))
        (.conj
          (graphValueAt (2 : Fin 9) (5 : Fin 9) (7 : Fin 9))
          (.conj
            (graphValueAt (7 : Fin 9) (3 : Fin 9) (8 : Fin 9))
            (kuratowskiPairAt
              (4 : Fin 9) (5 : Fin 9) (8 : Fin 9)))))))))

 theorem cardinalUnion_assignment
    (selector indexedFamily injectionFamily x output
      index fiber injection value : Constructible.Model.LCarrier.{u}) :
    snoc (snoc (snoc (snoc
      ![selector, indexedFamily, injectionFamily, x, output]
      index) fiber) injection) value =
      ![selector, indexedFamily, injectionFamily, x, output,
        index, fiber, injection, value] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_cardinalUnionPredicate
    (selector indexedFamily injectionFamily x output :
      Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      cardinalUnionPredicate
      ![selector, indexedFamily, injectionFamily, x, output] <->
      CardinalUnionRel Constructible.Model.lCarrierMem
        selector indexedFamily injectionFamily x output := by
  simp only [cardinalUnionPredicate, FOFormula.Satisfies,
    satisfies_graphValueAt, satisfies_kuratowskiPairAt,
    CardinalUnionRel]
  apply exists_congr
  intro index
  apply exists_congr
  intro fiber
  apply exists_congr
  intro injection
  apply exists_congr
  intro value
  rw [cardinalUnion_assignment]
  rfl

 theorem cardinalUnion_relation_assignment
    (selector indexedFamily injectionFamily x output :
      Constructible.Model.LCarrier.{u}) :
    snoc (snoc ![selector, indexedFamily, injectionFamily] x) output =
      ![selector, indexedFamily, injectionFamily, x, output] := by
  funext i
  fin_cases i <;> rfl

@[simp]
theorem satisfies_cardinalUnionRelation
    (selector indexedFamily injectionFamily x output :
      Constructible.Model.LCarrier.{u}) :
    FOFormula.Satisfies Constructible.Model.lCarrierMem
      cardinalUnionPredicate
      (snoc (snoc ![selector, indexedFamily, injectionFamily] x) output) <->
      CardinalUnionRel Constructible.Model.lCarrierMem
        selector indexedFamily injectionFamily x output := by
  rw [cardinalUnion_relation_assignment,
    satisfies_cardinalUnionPredicate]

/-! ## Conditional internal family interfaces -/

/-- A selector assigns to each member of a union an index of a fiber which
contains it. -/
def SelectsContainingFiber {A : Type u} (E : A -> A -> Prop)
    (selector union index indexedFamily : A) : Prop :=
  IsFunctionGraph E selector union index /\
    forall x i : A, E x union -> GraphValue E selector x i ->
      exists fiber : A,
        GraphValue E indexedFamily i fiber /\ E x fiber

/-- `injectionFamily` assigns to each index a graph injecting the
corresponding fiber into `kappa`.  Both assignments are internal graphs. -/
def IsFiberInjectionFamily {A : Type u} (E : A -> A -> Prop)
    (indexedFamily injectionFamily index family graphFamily kappa : A) : Prop :=
  IsFunctionGraph E indexedFamily index family /\
    IsFunctionGraph E injectionFamily index graphFamily /\
      forall i fiber injection : A, E i index ->
        GraphValue E indexedFamily i fiber ->
          GraphValue E injectionFamily i injection ->
            IsInjection E injection fiber kappa







end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalCardinalUnion


/- Source module: Solutions.Work_CUGCH_InternalStageCardinalUnion -/
section GCHSource_Work_CUGCH_InternalStageCardinalUnion
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The internally represented family of constructible stages

This file supplies the stage-family part of the standard cardinal estimate at
a limit level.  Replacement constructs the actual set of earlier stages, and
Separation constructs the actual graph sending an ordinal index to its stage.
Consequently the generic indexed-union theorem can be applied without taking
an externally indexed family as an internal graph.

The remaining inputs to the limit-cardinal argument are stated explicitly:
an internal selector choosing a containing stage, an internal family of
injection graphs for the fibers, and (when the final target is an ordinal
cardinal) the appropriate internal product absorption.  No ambient cardinal
comparison is converted into any of these graph witnesses.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A stage-valued functional relation -/

/-- `stage` is the stage coordinate of the canonical state at `index`. -/
def StageValueAt (index stage : LCarrier.{u}) : Prop :=
  exists relation : LCarrier.{u},
    Constructible.Model.StageStateAt index stage relation

/-- Layout `(fixed13, index, stage)`.  The hidden variable is the relation
coordinate of the stage state. -/
def stageValueAtFormula : FOFormula 15 :=
  .ex Constructible.Model.stageStateAtFormula

/-- The direct assignment for `stageValueAtFormula`. -/
def stageValueAtAssignment (index stage : LCarrier.{u}) :
    Tuple LCarrier.{u} 15 :=
  snoc (snoc Constructible.Model.stageHistoryFixedParameters index) stage

@[simp]
theorem satisfies_stageValueAtFormula
    (index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageValueAtFormula
        (stageValueAtAssignment index stage) ↔
      StageValueAt index stage := by
  simp only [stageValueAtFormula, FOFormula.Satisfies, StageValueAt]
  apply exists_congr
  intro relation
  change FOFormula.Satisfies LMem
      Constructible.Model.stageStateAtFormula
        (Constructible.Model.stageStateAtLAssignment
          index stage relation) ↔ _
  exact Constructible.Model.satisfies_stageStateAtFormula
    index stage relation

/-- At a canonical ordinal index, the stage coordinate is exactly the
externally defined level packaged as an `LCarrier`. -/
theorem stageValueAt_ordinal_iff
    (ordinal : Ordinal.{u}) (stage : LCarrier.{u}) :
    StageValueAt (ordinalLCarrier ordinal) stage ↔
      stage = stageLCarrier ordinal := by
  constructor
  · rintro ⟨relation, hstate⟩
    exact (Constructible.Model.stageStateAt_ordinal_outputs_unique
      ordinal hstate
        (Constructible.Model.stageHistoryData ordinal).state).1
  · rintro rfl
    exact ⟨(Constructible.Model.stageHistoryData ordinal).relation,
      (Constructible.Model.stageHistoryData ordinal).state⟩

/-! ## Replacement of the earlier stages -/

/-- Replacement produces the set of all stages strictly below `bound`. -/
theorem exists_stageValueFamily (bound : Ordinal.{u}) :
    exists family : LCarrier.{u},
      forall stage : LCarrier.{u},
        stage.1 ∈ family.1 ↔
          exists ordinal : Ordinal.{u},
            ordinal < bound /\ stage = stageLCarrier ordinal := by
  have hfun : forall index : LCarrier.{u},
      index.1 ∈ (ordinalLCarrier bound).1 ->
        ExistsUnique fun stage : LCarrier.{u} =>
          FOFormula.Satisfies LMem stageValueAtFormula
            (snoc (snoc Constructible.Model.stageHistoryFixedParameters
              index) stage) := by
    intro index hindex
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    refine ⟨stageLCarrier ordinal, ?_, ?_⟩
    · apply (satisfies_stageValueAtFormula
        (ordinalLCarrier ordinal) (stageLCarrier ordinal)).mpr
      exact (stageValueAt_ordinal_iff ordinal
        (stageLCarrier ordinal)).mpr rfl
    · intro other hother
      exact (stageValueAt_ordinal_iff ordinal other).mp
        ((satisfies_stageValueAtFormula
          (ordinalLCarrier ordinal) other).mp hother)
  rcases Constructible.Model.exists_replacementLCarrier
      stageValueAtFormula
      Constructible.Model.stageHistoryFixedParameters
      (ordinalLCarrier bound) hfun with ⟨family, hfamily⟩
  refine ⟨family, ?_⟩
  intro stage
  rw [hfamily]
  constructor
  · rintro ⟨index, hindex, hstage⟩
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    refine ⟨ordinal, hordinal, ?_⟩
    exact (stageValueAt_ordinal_iff ordinal stage).mp
      ((satisfies_stageValueAtFormula
        (ordinalLCarrier ordinal) stage).mp hstage)
  · rintro ⟨ordinal, hordinal, rfl⟩
    refine ⟨ordinalLCarrier ordinal,
      (ordinalLCarrier_mem_ordinalLCarrier_iff bound ordinal).mpr hordinal,
      ?_⟩
    apply (satisfies_stageValueAtFormula
      (ordinalLCarrier ordinal) (stageLCarrier ordinal)).mpr
    exact (stageValueAt_ordinal_iff ordinal
      (stageLCarrier ordinal)).mpr rfl

/-- The canonical choice of the Replacement-generated earlier-stage family.
Only its extensional specification is used below. -/
noncomputable def stageValueFamily (bound : Ordinal.{u}) : LCarrier.{u} :=
  Classical.choose (exists_stageValueFamily bound)

@[simp]
theorem mem_stageValueFamily_iff
    (bound : Ordinal.{u}) (stage : LCarrier.{u}) :
    stage.1 ∈ (stageValueFamily bound).1 ↔
      exists ordinal : Ordinal.{u},
        ordinal < bound /\ stage = stageLCarrier ordinal :=
  Classical.choose_spec (exists_stageValueFamily bound) stage



/-! ## The internally represented index-to-stage graph -/

/-- Rename `(fixed13,index,stage)` into
`(fixed13,bound,index,stage)`. -/
def boundedStageValueAtRename : Fin 15 -> Fin 16 :=
  Fin.lastCases
    (15 : Fin 16)
    (fun i14 => Fin.lastCases
      (14 : Fin 16)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

/-- Layout `(fixed13,bound,index,stage)`. -/
def boundedStageValueAtFormula : FOFormula 16 :=
  .conj
    (.mem (14 : Fin 16) (13 : Fin 16))
    (FOFormula.rename boundedStageValueAtRename stageValueAtFormula)

/-- Direct assignment for the bounded stage-valued relation. -/
def boundedStageValueAtAssignment
    (bound index stage : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  snoc (snoc
    (snoc Constructible.Model.stageHistoryFixedParameters bound)
    index) stage

theorem comp_boundedStageValueAtRename
    (bound index stage : LCarrier.{u}) :
    (fun i => boundedStageValueAtAssignment bound index stage
      (boundedStageValueAtRename i)) =
      stageValueAtAssignment index stage := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun _i13 => ?_) i14
    · rfl
    · simp only [boundedStageValueAtRename, Fin.lastCases_castSucc]
      rw [show Fin.castLE (by decide) _i13 =
          _i13.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [boundedStageValueAtAssignment, stageValueAtAssignment,
        snoc_castSucc]

@[simp]
theorem satisfies_boundedStageValueAtFormula
    (bound index stage : LCarrier.{u}) :
    FOFormula.Satisfies LMem boundedStageValueAtFormula
        (boundedStageValueAtAssignment bound index stage) ↔
      index.1 ∈ bound.1 /\ StageValueAt index stage := by
  simp only [boundedStageValueAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename]
  rw [comp_boundedStageValueAtRename,
    satisfies_stageValueAtFormula]
  rfl

/-- A support containing both the ordinal index set and the family of stage
values. -/
def stageValueGraphSupport (bound : Ordinal.{u}) : LCarrier.{u} :=
  Constructible.Model.unionLCarrier
    (ordinalLCarrier bound) (stageValueFamily bound)

/-- The actual constructible graph sending each `beta < bound` to `L_beta`. -/
noncomputable def stageValueGraph (bound : Ordinal.{u}) : LCarrier.{u} :=
  Constructible.Model.canonicalDefinableRelationGraph
    boundedStageValueAtFormula
    (snoc Constructible.Model.stageHistoryFixedParameters
      (ordinalLCarrier bound))
    (stageValueGraphSupport bound)

@[simp]
theorem graphValue_stageValueGraph_iff
    (bound : Ordinal.{u}) (index stage : LCarrier.{u}) :
    GraphValue LMem (stageValueGraph bound) index stage ↔
      index.1 ∈ (ordinalLCarrier bound).1 /\
        StageValueAt index stage := by
  rw [graphValue_lCarrier_iff_graphRel]
  simp only [stageValueGraph,
    Constructible.Model.graphRel_canonicalDefinableRelationGraph_iff]
  change
    (index.1 ∈ (stageValueGraphSupport bound).1 /\
      stage.1 ∈ (stageValueGraphSupport bound).1 /\
        FOFormula.Satisfies LMem boundedStageValueAtFormula
          (boundedStageValueAtAssignment
            (ordinalLCarrier bound) index stage)) ↔ _
  rw [satisfies_boundedStageValueAtFormula]
  constructor
  · rintro ⟨_hindexSupport, _hstageSupport, hindex, hstage⟩
    exact ⟨hindex, hstage⟩
  · rintro ⟨hindex, hstage⟩
    have hindexSupport :
        index.1 ∈ (stageValueGraphSupport bound).1 := by
      apply (Constructible.Model.mem_unionLCarrier_iff
        (ordinalLCarrier bound) (stageValueFamily bound) index).mpr
      exact Or.inl hindex
    rcases Constructible.Model.exists_eq_ordinalLCarrier_of_mem hindex with
      ⟨ordinal, hordinal, rfl⟩
    have hstageEq : stage = stageLCarrier ordinal :=
      (stageValueAt_ordinal_iff ordinal stage).mp hstage
    have hstageFamily : stage.1 ∈ (stageValueFamily bound).1 := by
      rw [hstageEq]
      exact (mem_stageValueFamily_iff bound
        (stageLCarrier ordinal)).mpr ⟨ordinal, hordinal, rfl⟩
    have hstageSupport :
        stage.1 ∈ (stageValueGraphSupport bound).1 := by
      apply (Constructible.Model.mem_unionLCarrier_iff
        (ordinalLCarrier bound) (stageValueFamily bound) stage).mpr
      exact Or.inr hstageFamily
    exact ⟨hindexSupport, hstageSupport, hindex, hstage⟩



/-! ## The standard limit-cardinal step -/





end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_InternalStageCardinalUnion


/- Source module: Solutions.Work_CUGCH_CanonicalLimitStageSelector -/
section GCHSource_Work_CUGCH_CanonicalLimitStageSelector
set_option autoImplicit false
/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/




/-!
# The canonical containing-stage selector at a limit

For an element of a nonzero limit stage, this file selects the least earlier
stage containing it.  The selector is an actual constructible graph obtained
by Separation from a fixed first-order formula.  The external `firstStage`
operation appears only in the proof that this graph is total and single
valued; it is not used as an internal graph witness.
-/

section

universe u

namespace Constructible.ContinuumFormula

open Constructible.Model

local notation "LMem" => Constructible.Model.lCarrierMem

noncomputable section

/-! ## A stage contains an element -/

/-- The stage at `index` contains `x`. -/
def StageContains (x index : LCarrier.{u}) : Prop :=
  exists stage : LCarrier.{u},
    StageValueAt index stage /\ x.1 ∈ stage.1

/-- Layout `(fixed13,x,index)`.  The hidden variable is the stage value. -/
def stageContainsAtFormula : FOFormula 15 :=
  .ex (.conj
    (FOFormula.rename boundedStageValueAtRename stageValueAtFormula)
    (.mem (13 : Fin 16) (15 : Fin 16)))

/-- The direct assignment for the stage-containment relation. -/
def stageContainsAtAssignment (x index : LCarrier.{u}) :
    Tuple LCarrier.{u} 15 :=
  stageValueAtAssignment x index

@[simp]
theorem satisfies_stageContainsAtFormula
    (x index : LCarrier.{u}) :
    FOFormula.Satisfies LMem stageContainsAtFormula
        (stageContainsAtAssignment x index) ↔
      StageContains x index := by
  simp only [stageContainsAtFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, StageContains]
  apply exists_congr
  intro stage
  change
    (FOFormula.Satisfies LMem stageValueAtFormula
        (fun i => boundedStageValueAtAssignment x index stage
          (boundedStageValueAtRename i)) /\
      x.1 ∈ stage.1) ↔ _
  rw [comp_boundedStageValueAtRename,
    satisfies_stageValueAtFormula]



/-! ## Least containing indices -/

/-- Rename `(fixed13,x,index)` into the context
`(fixed13,bound,x,current,earlier)`, selecting the last variable as the new
index. -/
def earlierStageContainsRename : Fin 15 -> Fin 17 :=
  Fin.lastCases
    (16 : Fin 17)
    (fun i14 => Fin.lastCases
      (14 : Fin 17)
      (fun i13 => Fin.castLE (by decide) i13)
      i14)

 theorem comp_earlierStageContainsRename
    (bound x current earlier : LCarrier.{u}) :
    (fun i => snoc
      (boundedStageValueAtAssignment bound x current) earlier
        (earlierStageContainsRename i)) =
      stageContainsAtAssignment x earlier := by
  funext i
  refine Fin.lastCases ?_ (fun i14 => ?_) i
  · rfl
  · refine Fin.lastCases ?_ (fun i13 => ?_) i14
    · rfl
    · simp only [earlierStageContainsRename, Fin.lastCases_castSucc]
      rw [show Fin.castLE (by decide) i13 =
          i13.castSucc.castSucc.castSucc.castSucc by
        apply Fin.ext
        rfl]
      simp only [boundedStageValueAtAssignment,
        stageContainsAtAssignment, stageValueAtAssignment, snoc_castSucc]

/-- Semantic predicate: `index` is the least member of `bound` whose stage
contains `x`. -/
def IsLeastContainingStage
    (bound x index : LCarrier.{u}) : Prop :=
  index.1 ∈ bound.1 /\
    StageContains x index /\
      forall earlier : LCarrier.{u}, earlier.1 ∈ index.1 ->
        Not (StageContains x earlier)

/-- Layout `(fixed13,bound,x,index)`. -/
def leastContainingStageFormula : FOFormula 16 :=
  .conj
    (.mem (15 : Fin 16) (13 : Fin 16))
    (.conj
      (FOFormula.rename boundedStageValueAtRename stageContainsAtFormula)
      (FOFormula.boundedAll (15 : Fin 16)
        (.neg (FOFormula.rename earlierStageContainsRename
          stageContainsAtFormula))))

/-- Direct assignment for the least-containing-stage formula. -/
def leastContainingStageAssignment
    (bound x index : LCarrier.{u}) : Tuple LCarrier.{u} 16 :=
  boundedStageValueAtAssignment bound x index

@[simp]
theorem satisfies_leastContainingStageFormula
    (bound x index : LCarrier.{u}) :
    FOFormula.Satisfies LMem leastContainingStageFormula
        (leastContainingStageAssignment bound x index) ↔
      IsLeastContainingStage bound x index := by
  simp only [leastContainingStageFormula, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_boundedAll,
    IsLeastContainingStage, leastContainingStageAssignment]
  rw [comp_boundedStageValueAtRename]
  rw [show FOFormula.Satisfies LMem stageContainsAtFormula
        (stageValueAtAssignment x index) ↔ StageContains x index by
      simpa only [stageContainsAtAssignment] using
        (satisfies_stageContainsAtFormula x index)]
  apply and_congr_right
  intro _hindex
  apply and_congr_right
  intro _hcontains
  apply forall_congr'
  intro earlier
  rw [comp_earlierStageContainsRename,
    satisfies_stageContainsAtFormula]
  change (earlier.1 ∈ index.1 -> Not (StageContains x earlier)) ↔ _
  rfl

/-! ## The Separation-generated selector graph -/

/-- The actual constructible graph selecting the least containing stage. -/
noncomputable def leastContainingStageGraph
    (limit : Ordinal.{u}) : LCarrier.{u} :=
  Constructible.Model.canonicalDefinableRelationGraph
    leastContainingStageFormula
    (snoc Constructible.Model.stageHistoryFixedParameters
      (ordinalLCarrier limit))
    (stageLCarrier limit)

@[simp]
theorem graphValue_leastContainingStageGraph_iff
    (limit : Ordinal.{u}) (x index : LCarrier.{u}) :
    GraphValue LMem (leastContainingStageGraph limit) x index ↔
      x.1 ∈ (stageLCarrier limit).1 /\
        IsLeastContainingStage (ordinalLCarrier limit) x index := by
  rw [graphValue_lCarrier_iff_graphRel]
  simp only [leastContainingStageGraph,
    Constructible.Model.graphRel_canonicalDefinableRelationGraph_iff]
  change
    (x.1 ∈ (stageLCarrier limit).1 /\
      index.1 ∈ (stageLCarrier limit).1 /\
        FOFormula.Satisfies LMem leastContainingStageFormula
          (leastContainingStageAssignment
            (ordinalLCarrier limit) x index)) ↔ _
  rw [satisfies_leastContainingStageFormula]
  constructor
  · rintro ⟨hx, _hindexStage, hleast⟩
    exact ⟨hx, hleast⟩
  · rintro ⟨hx, hleast⟩
    have hindexStage : index.1 ∈ (stageLCarrier limit).1 := by
      change index.1 ∈ LStageZF limit
      exact (ordinal_stage_invariants limit).2 hleast.1
    exact ⟨hx, hindexStage, hleast⟩







/-! ## Limit and Hartogs corollaries with the selector discharged -/





end

end Constructible.ContinuumFormula

end
end GCHSource_Work_CUGCH_CanonicalLimitStageSelector


