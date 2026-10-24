-- Prove2me | Definitions.Def_CH_Constructible
-- name    : CH_Constructible
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-23T23:11:11.24986+00:00
-- url     : https://prove2.me/theorems/be86016c-736f-4b0f-b3f5-cda4a7c6ae3f
-- title:
--   Gödel's constructible hierarchy over ZFC sets
-- statement:
--   Let $\mathrm{Def}(a)$ be the subsets of $a$ definable over $(a,\in)$ with finitely many parameters. Define
--   $$L_0=\varnothing,\qquad L_{\alpha+1}=\mathrm{Def}(L_\alpha),\qquad L_\lambda=\bigcup_{\alpha<\lambda}L_\alpha.$$
--   The membership structure on $L=\bigcup_\alpha L_\alpha$ is the common object for subsequent model theorems.
--
--   **Formalization Note** The construction uses Mathlib's ambient ZFC sets and small ordinals. Its carrier lives in Lean's next universe; it is not an internal construction in an arbitrary ZF model.
-- source:
--   Andrew Marks, Set Theory, updated January 31, 2026, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf, p. 86, definition of Def(M) and Definition 20.2; immediate recursion equations and the empty-set witness.

import Definitions.Def_CH_ZFC

/-!
# The constructible hierarchy inside Mathlib's ZFC sets

`definableSubsets a` consists of the subsets of `a` defined over `(a, ∈)`
by a first-order formula with finitely many parameters from `a`.
`level` iterates this operation through the small ordinals. Its union is
represented by the subtype `Carrier`, with the inherited membership relation.

Reference: Andrew Marks, Set Theory (January 31, 2026), Definition 20.2,
pp. 86–87, https://math.berkeley.edu/~marks/notes/set_theory_notes_4.pdf.

This is an external construction in Lean's ambient universe, not a definition
of constructibility inside an arbitrary possibly nonstandard model of ZF.
-/

namespace ContinuumHypothesis.Constructible

open FirstOrder FirstOrder.Language

noncomputable section

/-- A subset of the ambient ZFC sets, viewed as a membership structure. -/
def membershipStructure (s : Set ZFSet.{0}) : setLang.Structure s where
  funMap := fun f => Empty.elim f
  RelMap := fun r v => match r with
    | SetRel.mem => (v 0).val ∈ (v 1).val

instance setStructure (a : ZFSet.{0}) : setLang.Structure a :=
  membershipStructure (a : Set ZFSet.{0})

/-- The definable power set: formulas may use any finite tuple of parameters. -/
def definableSubsets (a : ZFSet.{0}) : ZFSet.{0} :=
  ZFSet.sep (fun b =>
    ∃ (n : ℕ) (φ : setLang.Formula (Fin (n + 1))) (p : Fin n → a),
      ∀ x : a, x.val ∈ b ↔ φ.Realize (Fin.cases x p)) (ZFSet.powerset a)

/-- Gödel's hierarchy: empty at zero, definable subsets at successors,
and the union of the preceding levels at nonzero limits. -/
def level (α : Ordinal.{0}) : ZFSet.{0} :=
  Ordinal.limitRecOn α ∅ (fun _ a => definableSubsets a)
    (fun β _ previous => ZFSet.iUnion (fun i : β.ToType =>
      previous i.toOrd.val i.toOrd.property))

@[simp] theorem level_zero : level 0 = ∅ := by
  simp [level]

@[simp] theorem level_add_one (α : Ordinal.{0}) :
    level (α + 1) = definableSubsets (level α) := by
  simp [level]

theorem level_limit (α : Ordinal.{0}) (h : Order.IsSuccLimit α) :
    level α = ZFSet.iUnion (fun i : α.ToType => level i.toOrd.val) := by
  unfold level
  rw [Ordinal.limitRecOn_limit _ _ _ _ h]

@[simp] theorem empty_mem_definableSubsets (a : ZFSet.{0}) :
    (∅ : ZFSet.{0}) ∈ definableSubsets a := by
  rw [definableSubsets, ZFSet.mem_sep]
  refine ⟨by simp, 0, ⊥, Fin.elim0, ?_⟩
  intro x
  simp

/-- The class of all constructible sets. -/
def IsConstructible (x : ZFSet.{0}) : Prop := ∃ α : Ordinal.{0}, x ∈ level α

/-- The constructible universe as a type in the ambient metatheory. -/
abbrev Carrier : Type 1 := {x : ZFSet.{0} // IsConstructible x}

instance carrierStructure : setLang.Structure Carrier :=
  membershipStructure {x | IsConstructible x}

instance carrierNonempty : Nonempty Carrier := by
  refine ⟨⟨∅, 0 + 1, ?_⟩⟩
  rw [level_add_one, level_zero]
  exact empty_mem_definableSubsets ∅

end

end ContinuumHypothesis.Constructible


