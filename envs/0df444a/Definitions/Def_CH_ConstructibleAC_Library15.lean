-- Prove2me | Definitions.Def_CH_ConstructibleAC_Library15
-- name    : CH_ConstructibleAC_Library15
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T01:40:59.192799+00:00
-- url     : https://prove2.me/theorems/8a9d239c-3fba-4195-ab2e-5222a96b8b85
-- title:
--   Identifying the platform constructible hierarchy
-- statement:
--   The platform and the reference construction use different presentations of first-order membership formulas and opposite conventions for the distinguished variable. Explicit language maps and coordinate permutations identify their definable-power-set operations. Transfinite induction then identifies every hierarchy stage, and hence their full carriers by an equivalence preserving the underlying ambient set. This library supplies that equivalence for transporting the internal choice-set result to the platform statement.
--
--   This semantic bridge adapts the [formalization by Zike Liu](https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53), copyright 2026, Apache-2.0, to the existing Prove2Me definitions. It does not change the target's definition of the constructible hierarchy.
--
--   The construction uses the external constructible universe over ambient `ZFSet` sets.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Prove2Me adaptation by Wentao Li (Victor), with OpenAI Codex assistance. Andrew Marks, Set Theory, Definition 20.2 and Theorem 20.9, printed pp. 86 and 88, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf; reference formalization by Zike Liu, https://github.com/05-02-07/lean-constructible-universe/tree/7f5a7d03d63d9769172f17350bbe8303996e5b53

import Definitions.Def_CH_ConstructibleAC_Library14
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

/-!
# Adaptation of Zike Liu's constructible-universe Choice proof

Original formalization: Copyright (c) 2026 Zike Liu, Apache-2.0.
Source: https://github.com/05-02-07/lean-constructible-universe
Commit: 7f5a7d03d63d9769172f17350bbe8303996e5b53.
All original per-file copyright notices are retained below.

**Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.

This credit concerns the Prove2Me adaptation and semantic bridge. The original
well-ordering formalization is by Zike Liu, credited above and in each source section.
-/

set_option autoImplicit false



namespace ContinuumHypothesis.Constructible
open FirstOrder FirstOrder.Language
noncomputable section
open Classical
set_option Elab.async false

 def toNativeLanguage : setLang →ᴸ FirstOrder.Language.setTheory where
  onFunction := fun {_} f => Empty.elim f
  onRelation := fun {_} r => match r with | SetRel.mem => .mem

 def fromNativeLanguage : FirstOrder.Language.setTheory →ᴸ setLang where
  onFunction := fun {_} f => Empty.elim f
  onRelation := fun {_} r => match r with | .mem => SetRel.mem

 instance nativeSetStructure (a : ZFSet.{0}) :
    FirstOrder.Language.setTheory.Structure a :=
  FirstOrder.Language.setTheoryStructure (fun x y : a => x.val ∈ y.val)

 instance toNativeExpansion (a : ZFSet.{0}) : toNativeLanguage.IsExpansionOn a where
  map_onFunction := fun {_} f => Empty.elim f
  map_onRelation := fun r _ => by cases r; rfl

 instance fromNativeExpansion (a : ZFSet.{0}) : fromNativeLanguage.IsExpansionOn a where
  map_onFunction := fun {_} f => Empty.elim f
  map_onRelation := fun r _ => by cases r; rfl

 def firstToLast (n : ℕ) : Fin (n+1) → Fin (n+1) :=
  Fin.cases (Fin.last n) Fin.castSucc

 def lastToFirst (n : ℕ) : Fin (n+1) → Fin (n+1) :=
  Fin.lastCases 0 Fin.succ

 theorem snoc_firstToLast {A : Type*} {n : ℕ} (p : Fin n → A) (x : A) :
    Fin.snoc p x ∘ firstToLast n = Fin.cases x p := by
  funext i
  cases i using Fin.cases <;> simp [firstToLast]

 theorem cases_lastToFirst {A : Type*} {n : ℕ} (p : Fin n → A) (x : A) :
    (Fin.cases x p : Fin (n+1) → A) ∘ lastToFirst n = Fin.snoc p x := by
  funext i
  cases i using Fin.lastCases <;> simp [lastToFirst]

 def toNativeBounded {n : ℕ} (φ : setLang.Formula (Fin (n+1))) :
    FirstOrder.Language.setTheory.BoundedFormula Empty (n+1) :=
  BoundedFormula.relabel (n := n+1) Sum.inr ((toNativeLanguage.onFormula φ).relabel (firstToLast n))

 theorem realize_toNativeBounded (a : ZFSet.{0}) {n : ℕ}
    (φ : setLang.Formula (Fin (n+1))) (p : Fin n → a) (x : a) :
    _root_.Constructible.Model.realizes (_root_.Constructible.zfCarrierMem a)
      (toNativeBounded φ) (_root_.Constructible.snoc p x) ↔ φ.Realize (Fin.cases x p) := by
  unfold _root_.Constructible.Model.realizes
  rw [_root_.Constructible.Model.snoc_eq_finSnoc]
  change BoundedFormula.Realize (toNativeBounded φ) (Empty.elim : Empty → a)
    (Fin.snoc p x) ↔ _
  rw [toNativeBounded, Formula.realize_relabel_sumInr, Formula.realize_relabel,
    snoc_firstToLast]
  exact LHom.realize_onFormula toNativeLanguage φ

 def fromNativeBounded {n : ℕ}
    (φ : FirstOrder.Language.setTheory.BoundedFormula Empty (n+1)) :
    setLang.Formula (Fin (n+1)) :=
  (fromNativeLanguage.onFormula (φ.toFormula.relabel (Sum.elim Empty.elim id))).relabel
    (lastToFirst n)

 theorem realize_fromNativeBounded (a : ZFSet.{0}) {n : ℕ}
    (φ : FirstOrder.Language.setTheory.BoundedFormula Empty (n+1))
    (p : Fin n → a) (x : a) :
    (fromNativeBounded φ).Realize (Fin.cases x p) ↔
      _root_.Constructible.Model.realizes (_root_.Constructible.zfCarrierMem a)
        φ (_root_.Constructible.snoc p x) := by
  rw [fromNativeBounded, Formula.realize_relabel, cases_lastToFirst,
    LHom.realize_onFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  unfold _root_.Constructible.Model.realizes
  rw [_root_.Constructible.Model.snoc_eq_finSnoc]
  simp only [Function.comp_assoc, Sum.elim_comp_inr, Function.comp_id, Unique.eq_default]
  rfl

 theorem definableSubsets_eq_native (a : ZFSet.{0}) :
    definableSubsets a = _root_.Constructible.DefZF a := by
  apply ZFSet.ext
  intro b
  rw [definableSubsets, ZFSet.mem_sep, ZFSet.mem_powerset,
    _root_.Constructible.Model.mem_DefZF_iff_exists_realizes]
  constructor
  · rintro ⟨hba, n, φ, p, hφ⟩
    refine ⟨hba, n, p, toNativeBounded φ, fun x => ?_⟩
    exact (hφ x).trans (realize_toNativeBounded a φ p x).symm
  · rintro ⟨hba, n, p, φ, hφ⟩
    refine ⟨hba, n, fromNativeBounded φ, p, fun x => ?_⟩
    exact (hφ x).trans (realize_fromNativeBounded a φ p x).symm

 theorem level_eq_native (α : Ordinal.{0}) :
    level α = _root_.Constructible.LStageZF α := by
  induction α using Ordinal.limitRecOn with
  | zero => rw [level_zero, _root_.Constructible.LStageZF_zero]
  | add_one α ih =>
    rw [level_add_one, ← Order.succ_eq_add_one, _root_.Constructible.LStageZF_succ,
      ih, definableSubsets_eq_native]
  | limit α hα ih =>
    apply ZFSet.ext
    intro x
    rw [level_limit α hα, ZFSet.mem_iUnion,
      _root_.Constructible.mem_LStageZF_limit_iff hα]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i.toOrd.val, i.toOrd.property, (ih i.toOrd.val i.toOrd.property) ▸ hi⟩
    · rintro ⟨β, hβ, hx⟩
      refine ⟨Ordinal.ToType.mk ⟨β, hβ⟩, ?_⟩
      have hx' : x ∈ level β := (ih β hβ).symm ▸ hx
      simpa using hx'

 theorem constructible_iff_native (x : ZFSet.{0}) :
    IsConstructible x ↔ x ∈ _root_.Constructible.L := by
  simp only [IsConstructible, _root_.Constructible.mem_L_iff, level_eq_native]

 def nativeCarrierEquiv : Carrier ≃ _root_.Constructible.Model.LCarrier.{0} where
  toFun := fun x => ⟨x.val, (constructible_iff_native x.val).mp x.property⟩
  invFun := fun x => ⟨x.val, (constructible_iff_native x.val).mpr x.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

 def ChoiceOn (M : Type 1) (val : M → ZFSet.{0}) : Prop :=
  ∀ a : M, (∀ x : M, val x ∈ val a → ∃ y : M, val y ∈ val x) →
    (∀ x : M, val x ∈ val a → ∀ y : M, val y ∈ val a → x ≠ y →
      ∀ z : M, val z ∈ val x → val z ∉ val y) →
    ∃ c : M, ∀ x : M, val x ∈ val a →
      ∃ y : M, val y ∈ val x ∧ val y ∈ val c ∧
        ∀ z : M, val z ∈ val x → val z ∈ val c → z = y


















end
end ContinuumHypothesis.Constructible


