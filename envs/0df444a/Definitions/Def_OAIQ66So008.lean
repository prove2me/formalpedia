-- Prove2me | Definitions.Def_OAIQ66So008
-- name    : OAIQ66So008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:11:33.658934+00:00
-- url     : https://prove2.me/theorems/f8798d28-2a48-49e1-9c91-1cfa88de8a38
-- title:
--   Definitions bundle OAIQ66So008 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 293 declarations of OpenAI's Lean: 96 definitions, 5 inductive types or structures, 1 instance and 191 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.BoundedEncoding.WordCalculus.rawMatrixAction`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.CodeTable.Contextual`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.CodeTable.ZeroIdeal`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.CodeTable.output`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.CodeTable.table`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.CodedSearch.lt`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.DelimiterCode`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.DelimiterCode.alphabet`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.DelimiterCode.block`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.DelimiterCode.cost`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.DelimiterCode.encode`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.DelimiterCode.map`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.EncodedCanonical.candidates`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.EncodedCanonical.least`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.FiniteParameter.select`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.FiniteSearch`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.PaddedCode.body`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.PaddedCode.code`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.PaddedCode.symbols`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.PaddedCode.words`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.PaddedCode.wordsOver`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Array.Name`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Array.algebraValue`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Array.entry`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Array.product`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Array.value`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.Point`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.Word`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Finite.traverse`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.Column`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.Name`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.Raw`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.columnCost`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.columnKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.columnValue`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.cost`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.matrixKey`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.maximum`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.mulVec`, `OAI.SimpleFInftyOvergroups.EffectiveNames.MatrixNames.oneName` and 61 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_NonunitalCompression`, `FiniteType_OrderListChainsBased`, `FiniteType_ProductGroupHomology`, `FiniteType_RingExchange`, `FiniteType_StageConstruction`, `SimpleOvergroups_ActionCorner`, `SimpleOvergroups_ActionMonoid`, `SimpleOvergroups_ArrayNames`, `SimpleOvergroups_ArrayOperations`, `SimpleOvergroups_CanonicalNames`, `SimpleOvergroups_CodeEmbedding`, `SimpleOvergroups_ContextualTables`, `SimpleOvergroups_ContractedNormalForms`, `SimpleOvergroups_EffectiveCode`, `SimpleOvergroups_EffectiveFamilies`, `SimpleOvergroups_EffectiveTables`, `SimpleOvergroups_EnlargementNames`, `SimpleOvergroups_FamilyProgram`, `SimpleOvergroups_FamilyTables`, `SimpleOvergroups_FiniteNames`, `SimpleOvergroups_MatrixNames`, `SimpleOvergroups_MatrixWords`, `SimpleOvergroups_PolynomialBounds`, `SimpleOvergroups_PolynomialNames`, `SimpleOvergroups_RingAssemblyTools`, `SimpleOvergroups_SemanticActions`, `SimpleOvergroups_ThreeCodes`, `SimpleOvergroups_TruncatedAction`, `SimpleOvergroups_TwoEnlargements`, `SimpleOvergroups_VariableCode`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So014`, `OAIQ66So015` and `OAIQ66So016`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ066_SO.FiniteType_NonunitalCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
section
variable {n R S : Type*} [Ring R] [Ring S] [Fintype n] [DecidableEq n]

def matrixCoefficient (φ : R →ₙ+* S) : Matrix n n R →ₙ+* Matrix n n S where
  toFun A := A.map φ
  map_zero' := by ext; simp
  map_add' A B := by ext; simp
  map_mul' A B := Matrix.map_mul

omit [DecidableEq n] in
@[simp] lemma matrixCoefficient_apply (φ : R →ₙ+* S) (A : Matrix n n R) (i j : n) :
    matrixCoefficient φ A i j = φ (A i j) := rfl

end

variable {n m R : Type*} [Ring R] [Fintype n] [DecidableEq n]

def matrixVector (A : Matrix n n R) : (n → Multiplicative R) →* (n → Multiplicative R) where
  toFun v i := Multiplicative.ofAdd (A.mulVec (fun j => (v j).toAdd) i)
  map_one' := by
    ext i
    exact congrFun (Matrix.mulVec_zero A) i
  map_mul' v w := by
    ext i
    exact congrFun (Matrix.mulVec_add A (fun j => (v j).toAdd) (fun j => (w j).toAdd)) i

omit [DecidableEq n] in
@[simp] lemma matrixVector_apply (A : Matrix n n R) (v : n → Multiplicative R) (i : n) :
    (matrixVector A v i).toAdd = A.mulVec (fun j => (v j).toAdd) i := rfl

@[simp] lemma matrixVector_one (v : n → Multiplicative R) : matrixVector (1 : Matrix n n R) v = v := by
  ext i
  simp [matrixVector]

omit [DecidableEq n] in
lemma matrixVector_mul (A B : Matrix n n R) (v : n → Multiplicative R) :
    matrixVector (A*B) v = matrixVector A (matrixVector B v) := by
  ext i
  simp only [matrixVector_apply, ← Matrix.mulVec_mulVec]

def vectorMatrix (A : Matrix n n R) : (n → Multiplicative R) →* (n → Multiplicative R) where
  toFun v i := Multiplicative.ofAdd (Matrix.vecMul (fun j => (v j).toAdd) A i)
  map_one' := by
    ext i
    exact congrFun (Matrix.zero_vecMul A) i
  map_mul' v w := by
    ext i
    exact congrFun (Matrix.add_vecMul A (fun j => (v j).toAdd) (fun j => (w j).toAdd)) i

omit [DecidableEq n] in
@[simp] lemma vectorMatrix_apply (A : Matrix n n R) (v : n → Multiplicative R) (i : n) :
    (vectorMatrix A v i).toAdd = Matrix.vecMul (fun j => (v j).toAdd) A i := rfl

@[simp] lemma vectorMatrix_one (v : n → Multiplicative R) : vectorMatrix (1 : Matrix n n R) v = v := by
  ext i
  simp [vectorMatrix]

omit [DecidableEq n] in
lemma vectorMatrix_mul (A B : Matrix n n R) (v : n → Multiplicative R) :
    vectorMatrix (A*B) v = vectorMatrix B (vectorMatrix A v) := by
  ext i
  simp only [vectorMatrix_apply, ← Matrix.vecMul_vecMul]

variable [Fintype m] [DecidableEq m]

def matrixRelabel (e : n ≃ m) : (Matrix n n R)ˣ →* (Matrix m m R)ˣ :=
  Units.map (Matrix.reindexRingEquiv R e).toMonoidHom

@[simp] lemma matrixRelabel_apply (e : n ≃ m) (A : (Matrix n n R)ˣ) (i j : m) :
    (matrixRelabel e A).val i j = A.val (e.symm i) (e.symm j) := rfl

def embeddingCompletion (f : n ↪ m) : n ⊕ ((Set.range f)ᶜ : Set m) ≃ m := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective f f.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range f))

omit [DecidableEq n] [Fintype m] in
@[simp] lemma embeddingCompletion_inl (f : n ↪ m) (i : n) :
    embeddingCompletion f (Sum.inl i) = f i := rfl

lemma matrixVector_single_apply (A : Matrix n n R) (j : n) (a : R) (i : n) :
    (matrixVector A (Pi.mulSingle j (Multiplicative.ofAdd a)) i).toAdd = A i j*a := by
  change (A.mulVec (Pi.single j a)) i = _
  simp

lemma vectorMatrix_single_apply (A : Matrix n n R) (j : n) (a : R) (i : n) :
    (vectorMatrix A (Pi.mulSingle j (Multiplicative.ofAdd a)) i).toAdd = a*A j i := by
  change (Matrix.vecMul (Pi.single j a) A) i = _
  simp

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_RingExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
section
variable {R : Type*} [Ring R]

abbrev SixIndices := (Fin 2 ⊕ Fin 2) ⊕ Fin 2

end

variable {R m : Type*} [Ring R]

def scalarWeight₀ (u : Rˣ) : SixIndices → Rˣ
  | Sum.inl (Sum.inl _) => u
  | _ => 1

def scalarWeight₁ (u : Rˣ) : SixIndices → Rˣ
  | Sum.inl (Sum.inr _) => u
  | _ => 1

def scalarWeight₂ (u : Rˣ) : SixIndices → Rˣ
  | Sum.inr _ => u
  | _ => 1

lemma scalarWeight_product (u : Rˣ) :
    scalarWeight₀ u * scalarWeight₁ u * scalarWeight₂ u = fun _ => u := by
  funext i
  rcases i with (i|i)|i <;> simp [scalarWeight₀,scalarWeight₁,scalarWeight₂]

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace StageConstruction
variable {R : Type*} [Ring R]
abbrev Seven := Fin 6 ⊕ Unit

end StageConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin
abbrev Cantor := Stream' Bool

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderListChainsBased
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

namespace SteinChains
section
variable (V : Type*)
abbrev Face := {F : Finset V // F.Nonempty}
end

end SteinChains

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ActionMonoid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceActionMonoid
universe u v
variable (V : Type u) (Z : Type v) [Group V] [MulAction V Z]

inductive Generator
  | grp : V → Generator
  | pre : Z → Generator
  | delete : Z → Generator
  | zero : Generator

abbrev Word := FreeMonoid (Generator V Z)

inductive Relation : Word V Z → Word V Z → Prop
  | group_mul (g h : V) : Relation
      (.of (.grp g) * .of (.grp h)) (.of (.grp (g * h)))
  | group_one : Relation (.of (.grp 1)) 1
  | delete_prefix (z : Z) : Relation (.of (.delete z) * .of (.pre z)) 1
  | delete_prefix_ne (y z : Z) (h : y ≠ z) : Relation
      (.of (.delete y) * .of (.pre z)) (.of .zero)
  | group_prefix (g : V) (z : Z) : Relation
      (.of (.grp g) * .of (.pre z)) (.of (.pre (g • z)))
  | delete_group (z : Z) (g : V) : Relation
      (.of (.delete z) * .of (.grp g)) (.of (.delete (g⁻¹ • z)))
  | zero_left (a : Generator V Z) : Relation (.of .zero * .of a) (.of .zero)
  | zero_right (a : Generator V Z) : Relation (.of a * .of .zero) (.of .zero)

abbrev M := PresentedMonoid (Relation V Z)

variable {V Z}

def of (a : Generator V Z) : M V Z := PresentedMonoid.of (Relation V Z) a

def omega : M V Z := of .zero

def prepend (z : Z) : M V Z := of (.pre z)
def delete (z : Z) : M V Z := of (.delete z)

def groupMap : V →* M V Z where
  toFun g := of (.grp g)
  map_one' := PresentedMonoid.mk_eq_mk_of_rel (Relation.group_one (V := V) (Z := Z))
  map_mul' g h := (PresentedMonoid.mk_eq_mk_of_rel (Relation.group_mul (V := V) (Z := Z) g h)).symm

@[simp] lemma of_grp (g : V) : of (.grp g) = groupMap (Z := Z) g := rfl

@[simp] lemma delete_prefix (z : Z) : delete (V := V) z * prepend z = 1 :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.delete_prefix (V := V) (Z := Z) z)

lemma delete_prefix_ne (y z : Z) (h : y ≠ z) :
    delete (V := V) y * prepend z = omega :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.delete_prefix_ne (V := V) (Z := Z) y z h)

lemma group_prefix (g : V) (z : Z) : groupMap g * prepend z = prepend (V := V) (g • z) :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.group_prefix (V := V) (Z := Z) g z)

lemma delete_group (z : Z) (g : V) : delete (V := V) z * groupMap g = delete (g⁻¹ • z) :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.delete_group (V := V) (Z := Z) z g)

@[simp] lemma omega_of (a : Generator V Z) : omega * of a = omega :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.zero_left (V := V) (Z := Z) a)

@[simp] lemma of_omega (a : Generator V Z) : of a * omega = omega :=
  PresentedMonoid.mk_eq_mk_of_rel (Relation.zero_right (V := V) (Z := Z) a)

@[simp] lemma omega_mul (a : M V Z) : omega * a = omega := by
  induction a using PresentedMonoid.inductionOn with | h w =>
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [map_mul, ← mul_assoc]
      exact (congrArg (· * PresentedMonoid.mk (Relation V Z) w) (omega_of a)).trans ih

@[simp] lemma mul_omega (a : M V Z) : a * omega = omega := by
  induction a using PresentedMonoid.inductionOn with | h w =>
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [map_mul, mul_assoc, ih]
      exact of_omega a

def prefixes (l : List Z) : M V Z := (l.map prepend).prod

def deletions (l : List Z) : M V Z := (l.reverse.map delete).prod

@[simp] lemma prefixes_nil : prefixes (V := V) ([] : List Z) = 1 := rfl
@[simp] lemma deletions_nil : deletions (V := V) ([] : List Z) = 1 := rfl
@[simp] lemma prefixes_cons (z : Z) (l : List Z) :
    prefixes (V := V) (z :: l) = prepend z * prefixes l := rfl

@[simp] lemma deletions_cons (z : Z) (l : List Z) :
    deletions (V := V) (z :: l) = deletions l * delete z := by
  simp [deletions]

def normal (l : List Z) (g : V) (r : List Z) : M V Z :=
  prefixes l * groupMap g * deletions r

lemma prepend_normal (z : Z) (l : List Z) (g : V) (r : List Z) :
    prepend z * normal l g r = normal (z :: l) g r := by
  simp only [normal, prefixes_cons, mul_assoc]

lemma group_normal_nil (h g : V) (r : List Z) :
    groupMap h * normal [] g r = normal [] (h * g) r := by
  simp [normal, map_mul, mul_assoc]

lemma group_normal_cons (h : V) (z : Z) (l : List Z) (g : V) (r : List Z) :
    groupMap h * normal (z :: l) g r = normal ((h • z) :: l) g r := by
  simp only [normal, prefixes_cons, ← mul_assoc, group_prefix]

lemma delete_normal_nil (z : Z) (g : V) (r : List Z) :
    delete z * normal [] g r = normal [] 1 (r ++ [g⁻¹ • z]) := by
  simp [normal, ← mul_assoc, delete_group, deletions]

lemma delete_normal_cons (z : Z) (l : List Z) (g : V) (r : List Z) :
    delete z * normal (z :: l) g r = normal l g r := by
  simp only [normal, prefixes_cons, ← mul_assoc, delete_prefix, one_mul]

lemma delete_normal_cons_ne (y z : Z) (h : y ≠ z) (l : List Z) (g : V) (r : List Z) :
    delete y * normal (z :: l) g r = omega := by
  simp only [normal, prefixes_cons, ← mul_assoc, delete_prefix_ne y z h, omega_mul]

abbrev State := List Z × V

def headAction (g : V) : State (V := V) (Z := Z) → State (V := V) (Z := Z)
  | ([], v) => ([], g * v)
  | (z :: zs, v) => (g • z :: zs, v)

noncomputable section
local instance instDecidableEq_solutions : DecidableEq Z := Classical.decEq _

def generatorAction : Generator V Z → Function.End (Option (State (V := V) (Z := Z)))
  | .grp g => Option.map (headAction g)
  | .pre z => Option.map (fun s => (z :: s.1, s.2))
  | .delete z => fun s => match s with
    | none => none
    | some ([], _) => none
    | some (y :: ys, v) => if z = y then some (ys, v) else none
  | .zero => fun _ => none

@[simp] lemma end_mul_apply {A : Type*} (f g : Function.End A) (a : A) :
    (f * g) a = f (g a) := rfl
@[simp] lemma end_one_apply {A : Type*} (a : A) : (1 : Function.End A) a = a := rfl

lemma generatorAction_relations (a b : Word V Z) (h : Relation V Z a b) :
    FreeMonoid.lift generatorAction a = FreeMonoid.lift generatorAction b := by
  cases h with
  | group_mul g h =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s with
    | none => rfl
    | some p =>
      rcases p with ⟨l, v⟩
      cases l <;> simp [generatorAction, headAction, mul_assoc, mul_smul]
  | group_one =>
    simp only [FreeMonoid.lift_eval_of, map_one]
    funext s
    simp only [end_one_apply]
    cases s with
    | none => rfl
    | some p =>
      rcases p with ⟨l, v⟩
      cases l <;> simp [generatorAction, headAction]
  | delete_prefix z =>
    simp only [map_mul, FreeMonoid.lift_eval_of, map_one]
    funext s
    simp only [end_mul_apply, end_one_apply]
    cases s <;> simp [generatorAction]
  | delete_prefix_ne y z h =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s <;> simp [generatorAction, h]
  | group_prefix g z =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s <;> simp [generatorAction, headAction]
  | delete_group z g =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases s with
    | none => rfl
    | some p =>
      rcases p with ⟨l, v⟩
      cases l with
      | nil => rfl
      | cons y ys =>
        have hi : z = g • y ↔ g⁻¹ • z = y := by
          constructor
          · intro h
            rw [h, inv_smul_smul]
          · intro h
            rw [← h, smul_inv_smul]
        simp only [generatorAction, Option.map_some, headAction]
        simp only [hi]
  | zero_left a =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    rfl
  | zero_right a =>
    simp only [map_mul, FreeMonoid.lift_eval_of]
    funext s
    simp only [end_mul_apply]
    cases a <;> rfl

def representation : M V Z →* Function.End (Option (State (V := V) (Z := Z))) :=
  PresentedMonoid.lift generatorAction generatorAction_relations

@[simp] lemma representation_of (a : Generator V Z) :
    representation (of a) = generatorAction a := rfl

@[simp] lemma representation_omega (s : Option (State (V := V) (Z := Z))) :
    representation omega s = none := rfl

@[simp] lemma representation_group (g : V) (s : Option (State (V := V) (Z := Z))) :
    representation (groupMap (Z := Z) g) s = s.map (headAction g) := rfl

@[simp] lemma representation_prepend (z : Z) (s : Option (State (V := V) (Z := Z))) :
    representation (prepend (V := V) z) s = s.map (fun p => (z :: p.1, p.2)) := rfl

def strip : List Z → List Z → Option (List Z)
  | [], w => some w
  | _ :: _, [] => none
  | z :: zs, y :: ys => if z = y then strip zs ys else none

@[simp] lemma strip_append (r l : List Z) : strip r (r ++ l) = some l := by
  induction r with
  | nil => rfl
  | cons z r ih => simpa [strip] using ih

lemma strip_eq_some_iff (r k t : List Z) : strip r k = some t ↔ k = r ++ t := by
  induction r generalizing k with
  | nil => simp [strip]
  | cons z r ih =>
    cases k with
    | nil => simp [strip]
    | cons y k =>
      by_cases h : z = y
      · subst y
        simp [strip, ih]
      · simp [strip, h, Ne.symm h]

@[simp] lemma representation_prefixes (l : List Z)
    (s : Option (State (V := V) (Z := Z))) :
    representation (prefixes (V := V) l) s = s.map (fun p => (l ++ p.1, p.2)) := by
  induction l with
  | nil => simp
  | cons z l ih =>
    simp only [prefixes_cons, map_mul, end_mul_apply, ih, representation_prepend,
      Option.map_map]
    rfl

@[simp] lemma representation_delete_none (z : Z) :
    representation (delete (V := V) z) none = none := rfl

@[simp] lemma representation_delete_nil (z : Z) (v : V) :
    representation (delete (V := V) z) (some ([], v)) = none := rfl

@[simp] lemma representation_delete_cons (z y : Z) (k : List Z) (v : V) :
    representation (delete (V := V) z) (some (y :: k, v)) =
      if z = y then some (k, v) else none := rfl

@[simp] lemma representation_deletions_none (r : List Z) :
    representation (deletions (V := V) r) none = none := by
  induction r with
  | nil => rfl
  | cons z r ih =>
    simpa only [deletions_cons, map_mul, end_mul_apply, representation_delete_none] using ih

lemma representation_deletions (r : List Z) (k : List Z) (v : V) :
    representation (deletions (V := V) r) (some (k, v)) =
      (strip r k).map (fun t => (t, v)) := by
  induction r generalizing k with
  | nil => rfl
  | cons z r ih =>
    rw [deletions_cons, map_mul, end_mul_apply]
    cases k with
    | nil => simp [strip]
    | cons y k =>
      by_cases h : z = y
      · subst y
        simpa [strip] using ih k
      · simp [strip, h]

@[simp] lemma strip_self (r : List Z) : strip r r = some [] := by
  simpa only [List.append_nil] using strip_append r []

lemma representation_normal (l : List Z) (g : V) (r k : List Z) (v : V) :
    representation (normal l g r) (some (k, v)) =
      (strip r k).map (fun t =>
        let p := headAction g (t, v)
        (l ++ p.1, p.2)) := by
  simp only [normal, map_mul, end_mul_apply, representation_deletions,
    representation_group, representation_prefixes, Option.map_map]
  rfl

@[simp] lemma representation_normal_at (l : List Z) (g : V) (r : List Z) :
    representation (normal l g r) (some (r, 1)) = some (l, g) := by
  simp only [representation_normal, strip_self, Option.map_some, headAction,
    List.append_nil, mul_one]

lemma normal_ne_zero (l : List Z) (g : V) (r : List Z) : normal l g r ≠ omega := by
  intro h
  have e := congrArg (fun a : M V Z => representation a (some (r, 1))) h
  simp only [representation_normal_at, representation_omega, reduceCtorEq] at e

lemma normal_domain_prefix (l : List Z) (g : V) (r k : List Z) (v : V)
    (h : representation (normal l g r) (some (k, v)) ≠ none) : r <+: k := by
  cases hs : strip r k with
  | none => simp only [representation_normal, hs, Option.map_none, ne_eq, not_true_eq_false] at h
  | some t => exact ⟨t, ((strip_eq_some_iff _ _ _).mp hs).symm⟩

theorem normal_eq_parameters {l l' : List Z} {g g' : V} {r r' : List Z}
    (h : normal l g r = normal l' g' r') : l = l' ∧ g = g' ∧ r = r' := by
  have hr : r <+: r' := normal_domain_prefix l g r r' 1 (by
    rw [h, representation_normal_at]
    exact Option.some_ne_none _)
  have hr' : r' <+: r := normal_domain_prefix l' g' r' r 1 (by
    rw [← h, representation_normal_at]
    exact Option.some_ne_none _)
  have heq : r = r' := hr.eq_of_length (Nat.le_antisymm hr.length_le hr'.length_le)
  subst r'
  have e := congrArg (fun a : M V Z => representation a (some (r, 1))) h
  simp only [representation_normal_at, Option.some.injEq, Prod.mk.injEq] at e
  exact ⟨e.1, e.2, rfl⟩

@[simp] theorem normal_eq_iff {l l' : List Z} {g g' : V} {r r' : List Z} :
    normal l g r = normal l' g' r' ↔ l = l' ∧ g = g' ∧ r = r' := by
  constructor
  · exact normal_eq_parameters
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem groupMap_injective : Function.Injective (groupMap (V := V) (Z := Z)) := by
  intro g h heq
  have he : normal ([] : List Z) g [] = normal [] h [] := by
    simpa only [normal, prefixes_nil, deletions_nil, one_mul, mul_one] using heq
  exact (normal_eq_parameters he).2.1

end

namespace Algorithm
variable [DecidableEq Z]

abbrev Form := Option (List Z × V × List Z)

def eval : Form (V := V) (Z := Z) → M V Z
  | none => omega
  | some (l, g, r) => normal l g r

def step : Generator V Z → Form (V := V) (Z := Z) → Form (V := V) (Z := Z)
  | _, none => none
  | .zero, _ => none
  | .pre z, some (l, g, r) => some (z :: l, g, r)
  | .grp h, some ([], g, r) => some ([], h * g, r)
  | .grp h, some (z :: l, g, r) => some (h • z :: l, g, r)
  | .delete y, some ([], g, r) => some ([], 1, r ++ [g⁻¹ • y])
  | .delete y, some (z :: l, g, r) => if y = z then some (l, g, r) else none

def normalize : List (Generator V Z) → Form (V := V) (Z := Z)
  | [] => some ([], 1, [])
  | c :: w => step c (normalize w)

omit [DecidableEq Z] in
lemma eval_injective : Function.Injective (eval (V := V) (Z := Z)) := by
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some p => exact (normal_ne_zero p.1 p.2.1 p.2.2 hab.symm).elim
  | some p =>
    rcases p with ⟨l, g, r⟩
    cases b with
    | none => exact (normal_ne_zero l g r hab).elim
    | some p =>
      rcases p with ⟨l', g', r'⟩
      obtain ⟨rfl, rfl, rfl⟩ := normal_eq_parameters hab
      rfl

end Algorithm
end SourceActionMonoid

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ActionCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SimpleFInftyOvergroups.RingAssembly
open SourceActionMonoid
open scoped Classical
variable {V Y R : Type*} [Group V] [MulAction V Y] [Ring R]

local instance actionCornerMonoidWithZero : MonoidWithZero (M V Y) where
  __ := (inferInstance : Monoid (M V Y))
  zero := omega
  zero_mul := omega_mul
  mul_zero := mul_omega

variable (δ : M V Y →*₀ R)

def actionUnits : V →* Rˣ := (δ.toMonoidHom.comp groupMap).toHomUnits

theorem actionUnits_val (w : V) : (actionUnits δ w).val=δ (groupMap w) := rfl

theorem actionUnits_injective (hδ : Function.Injective δ) : Function.Injective (actionUnits δ) := by
  intro w v hwv
  apply groupMap_injective (Z:=Y)
  exact hδ (congrArg Units.val hwv)

theorem corner_ρS (w : V) (y : Y) : (actionUnits δ w).val * δ (prepend y)=δ (prepend (w • y)) := by
  rw [actionUnits_val,←map_mul,group_prefix]

theorem corner_Tρ (w : V) (y : Y) : δ (delete y) * (actionUnits δ w).val=δ (delete (w⁻¹ • y)) := by
  rw [actionUnits_val,←map_mul,delete_group]

end SimpleFInftyOvergroups.RingAssembly
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ArrayNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames.Array
noncomputable section
open scoped Classical
variable {A X D K : Type*} [AddCommMonoid D]
variable (coeff : A → D) (index : X → K)

abbrev Name (A X : Type*) := List (A × X)

def value (p : Name A X) : K →₀ D :=
  (p.map fun a => Finsupp.single (index a.2) (coeff a.1)).sum

@[simp] theorem value_nil : value coeff index [] = 0 := rfl
@[simp] theorem value_cons (a : A × X) (p : Name A X) :
    value coeff index (a::p) = Finsupp.single (index a.2) (coeff a.1) + value coeff index p := rfl
@[simp] theorem value_append (p q : Name A X) :
    value coeff index (p++q) = value coeff index p + value coeff index q := by
  simp [value]

theorem value_eq_zero_of_not_named (p : Name A X) (k : K)
    (h : ∀ a ∈ p, index a.2 ≠ k) : value coeff index p k = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [value_cons, Finsupp.add_apply, Finsupp.single_eq_of_ne (Ne.symm (h a List.mem_cons_self))]
    simpa using ih (fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem value_eq_iff (p q : Name A X) :
    value coeff index p = value coeff index q ↔
      ∀ a ∈ p++q, value coeff index p (index a.2) = value coeff index q (index a.2) := by
  constructor
  · intro h a _; rw [h]
  · intro h
    ext k
    by_cases hn : ∃ a ∈ p++q, index a.2 = k
    · obtain ⟨a,ha,rfl⟩ := hn
      exact h a ha
    · have hh : ∀ a ∈ p++q, index a.2 ≠ k := by simpa using hn
      rw [value_eq_zero_of_not_named coeff index p k (fun a ha => hh a (List.mem_append_left _ ha)),
        value_eq_zero_of_not_named coeff index q k (fun a ha => hh a (List.mem_append_right _ ha))]

theorem value_surjective (hc : Function.Surjective coeff) (hx : Function.Surjective index) :
    Function.Surjective (value coeff index) := by
  intro p
  induction p using Finsupp.induction with
  | zero => exact ⟨[], rfl⟩
  | single_add x d p hn hd ih =>
    obtain ⟨a,rfl⟩ := hc d
    obtain ⟨b,rfl⟩ := hx x
    obtain ⟨q,rfl⟩ := ih
    exact ⟨(a,b)::q, rfl⟩

theorem value_map_index {Y J : Type*} (f : X → Y) (j : Y → J) (g : K → J)
    (h : ∀ x, j (f x) = g (index x)) (p : Name A X) :
    value coeff j (p.map (fun a => (a.1, f a.2))) = Finsupp.mapDomain g (value coeff index p) := by
  induction p with
  | nil => simp
  | cons a p ih => simp [ih, h, Finsupp.mapDomain_add]

variable (zeroName : A) (addName : A → A → A)

def entry (p : Name A X) (x : X) : A :=
  (p.map fun a => if index a.2 = index x then a.1 else zeroName).foldl addName zeroName

theorem coefficient_fold
    (hadd : ∀ a b, coeff (addName a b) = coeff a + coeff b) (l : List A) (a : A) :
    coeff (l.foldl addName a) = coeff a + (l.map coeff).sum := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih => simp only [List.foldl_cons,ih,hadd,List.map_cons,List.sum_cons,add_assoc]

theorem entry_correct (hzero : coeff zeroName = 0)
    (hadd : ∀ a b, coeff (addName a b) = coeff a + coeff b) (p : Name A X) (x : X) :
    coeff (entry index zeroName addName p x) = value coeff index p (index x) := by
  rw [entry, coefficient_fold coeff addName hadd, hzero, zero_add]
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.map_cons,List.sum_cons,value_cons,Finsupp.add_apply,ih]
    congr 1
    by_cases h : index a.2 = index x
    · simp [h]
    · simp [h,hzero]

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ArrayOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SimpleFInftyOvergroups.EffectiveNames.Array
noncomputable section
open scoped Classical
variable {A G X D V Y : Type*}

def product (cmul : A → A → A) (op : G → X → X) (p : Name A G) (q : Name A X) : Name A X :=
  p.flatMap fun a => q.map fun b => (cmul a.1 b.1,op a.2 b.2)

@[simp] theorem product_nil (cmul : A → A → A) (op : G → X → X) (q : Name A X) :
    product cmul op [] q = [] := rfl
@[simp] theorem product_cons (cmul : A → A → A) (op : G → X → X)
    (a : A × G) (p : Name A G) (q : Name A X) :
    product cmul op (a::p) q = (q.map fun b => (cmul a.1 b.1,op a.2 b.2)) ++ product cmul op p q := rfl

 theorem product_bound (cmul : A → A → A) (op : G → X → X)
    (gc : G → ℕ) (xc : X → ℕ) (hop : ∀ g x, xc (op g x) = gc g + xc x)
    {p : Name A G} {q : Name A X} {b c : ℕ}
    (hp : ∀ a ∈ p, gc a.2 ≤ b) (hq : ∀ a ∈ q, xc a.2 ≤ c) :
    ∀ a ∈ product cmul op p q, xc a.2 ≤ b+c := by
  intro a ha
  obtain ⟨u,hu,hv⟩ := List.mem_flatMap.mp ha
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  simpa only [hop] using Nat.add_le_add (hp u hu) (hq w hw)

variable [Ring D] [Group V]
variable (coeff : A → D) (group : G → V)

def algebraValue (p : Name A G) : MonoidAlgebra D V := MonoidAlgebra.ofCoeff (value coeff group p)

@[simp] theorem algebraValue_nil : algebraValue coeff group [] = 0 := rfl
@[simp] theorem algebraValue_cons (a : A × G) (p : Name A G) :
    algebraValue coeff group (a::p) = MonoidAlgebra.single (group a.2) (coeff a.1) + algebraValue coeff group p := rfl
@[simp] theorem algebraValue_append (p q : Name A G) :
    algebraValue coeff group (p++q) = algebraValue coeff group p + algebraValue coeff group q := by
  simp only [algebraValue,value_append,MonoidAlgebra.ofCoeff_add]

 theorem algebraValue_product (cmul : A → A → A) (mul : G → G → G)
    (hc : ∀ a b, coeff (cmul a b) = coeff a * coeff b)
    (hg : ∀ g h, group (mul g h) = group g * group h) (p q : Name A G) :
    algebraValue coeff group (product cmul mul p q) = algebraValue coeff group p * algebraValue coeff group q := by
  induction p with
  | nil => simp
  | cons a p ih =>
    rw [product_cons,algebraValue_append,ih,algebraValue_cons,add_mul]
    congr 1
    clear ih
    induction q with
    | nil => simp
    | cons b q ih =>
      simp only [List.map_cons,algebraValue_cons,ih,hc,hg,mul_add,MonoidAlgebra.single_mul_single]

variable [MulAction V Y] (point : X → Y)

variable [Primcodable A] [Primcodable G] [Primcodable X]
 theorem primrec_product {cmul : A → A → A} {op : G → X → X}
    (hc : Primrec₂ cmul) (ho : Primrec₂ op) : Primrec₂ (product cmul op) := by
  unfold product
  apply Primrec.list_flatMap Primrec.fst
  change Primrec (fun p : (Name A G × Name A X) × (A × G) =>
    p.1.2.map fun b => (cmul p.2.1 b.1,op p.2.2 b.2))
  apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
  exact ((hc.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd)).pair
    (ho.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))).to₂

end
end SimpleFInftyOvergroups.EffectiveNames.Array

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_CanonicalNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SimpleFInftyOvergroups.EffectiveNames
noncomputable section
open scoped Classical
variable {A Q : Type*} [Primcodable A] (q : A → Q)

def acceptsName (a : A) (n : ℕ) : Bool :=
  (Encodable.decode (α := A) n).elim false (fun b => decide (q b = q a))

theorem acceptsName_iff (a : A) (n : ℕ) :
    acceptsName q a n = true ↔ ∃ b, Encodable.decode (α := A) n = some b ∧ q b = q a := by
  unfold acceptsName
  cases h : Encodable.decode (α := A) n <;> simp

theorem match_exists (a : A) : ∃ n, acceptsName q a n = true :=
  ⟨Encodable.encode a, (acceptsName_iff q a _).mpr ⟨a, Encodable.encodek a, rfl⟩⟩

def key (a : A) : ℕ := Nat.find (match_exists q a)

theorem key_spec (a : A) :
    ∃ b, Encodable.decode (α := A) (key q a) = some b ∧ q b = q a :=
  (acceptsName_iff q a _).mp (Nat.find_spec (match_exists q a))

theorem key_congr {a b : A} (h : q a = q b) : key q a = key q b := by
  apply Nat.le_antisymm
  · apply Nat.find_min'
    obtain ⟨c,hc,he⟩ := key_spec q b
    exact (acceptsName_iff q a _).mpr ⟨c,hc,he.trans h.symm⟩
  · apply Nat.find_min'
    obtain ⟨c,hc,he⟩ := key_spec q a
    exact (acceptsName_iff q b _).mpr ⟨c,hc,he.trans h⟩

theorem key_eq_iff (a b : A) : key q a = key q b ↔ q a = q b := by
  constructor
  · intro h
    obtain ⟨x,hx,he⟩ := key_spec q a
    obtain ⟨y,hy,hf⟩ := key_spec q b
    rw [h] at hx
    have hxy : x=y := Option.some.inj (hx.symm.trans hy)
    exact he.symm.trans (hxy ▸ hf)
  · exact key_congr q

def semanticKey (hq : Function.Surjective q) (x : Q) : ℕ :=
  key q (Classical.choose (hq x))

@[simp] theorem semanticKey_value (hq : Function.Surjective q) (a : A) :
    semanticKey q hq (q a) = key q a :=
  key_congr q (Classical.choose_spec (hq (q a)))

theorem semanticKey_injective (hq : Function.Surjective q) :
    Function.Injective (semanticKey q hq) := by
  intro x y h
  obtain ⟨a,rfl⟩ := hq x
  obtain ⟨b,rfl⟩ := hq y
  simpa only [semanticKey_value, key_eq_iff] using h

variable (heq : ComputablePred (fun p : A × A => q p.1 = q p.2))

include heq in
theorem computable_acceptsName : Computable₂ (acceptsName q) := by
  change Computable (fun p : A × ℕ =>
    (Encodable.decode (α := A) p.2).elim false (fun b => decide (q b = q p.1)))
  apply (Computable.option_casesOn (Computable.decode.comp Computable.snd)
    (Computable.const false) (heq.decide.comp
      (Computable.snd.pair (Computable.fst.comp Computable.fst))).to₂).of_eq
  intro p
  cases Encodable.decode (α := A) p.2 <;> rfl

include heq in
theorem computable_key : Computable (key q) := by
  have hb : Computable₂ (fun (a b : Bool) => decide (a=b)) := Primrec.eq.decide.to_comp
  have hc : Computable (fun p : A × ℕ => decide (acceptsName q p.1 p.2 = true)) :=
    hb.comp (computable_acceptsName q heq) (Computable.const true)
  exact Computable.find (P := fun a n => acceptsName q a n = true)
    hc.computablePred (match_exists q)

end
end SimpleFInftyOvergroups.EffectiveNames

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_VariableCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding

structure DelimiterCode (A S : Type*) where
  start : S
  stop : S
  distinct : start ≠ stop
  body : A → List S
  start_avoids : ∀ a, start ∉ body a
  stop_avoids : ∀ a, stop ∉ body a
  injective : Function.Injective body

namespace DelimiterCode
variable {A S : Type*} (C : DelimiterCode A S)

def block (a : A) : List S := C.start :: (C.body a ++ [C.stop])
def encode (w : List A) : List S := w.flatMap C.block

@[simp] theorem block_length (a : A) : (C.block a).length = (C.body a).length + 2 := by
  simp [block]
@[simp] theorem encode_nil : C.encode [] = [] := rfl
@[simp] theorem encode_cons (a : A) (w : List A) :
    C.encode (a :: w) = C.block a ++ C.encode w := rfl
@[simp] theorem encode_append (u v : List A) :
    C.encode (u ++ v) = C.encode u ++ C.encode v := by simp [encode]

theorem length_le_encode (w : List A) : 2 * w.length ≤ (C.encode w).length := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [encode_cons, List.length_append, block_length, List.length_cons]; omega

@[simp] theorem encode_eq_nil (w : List A) : C.encode w = [] ↔ w = [] := by
  constructor
  · intro h
    have := C.length_le_encode w
    simp only [h, List.length_nil] at this
    simpa using (show w.length = 0 by omega)
  · rintro rfl; rfl

theorem split_at_stop {t : S} {a b u v : List S} (ha : t ∉ a) (hb : t ∉ b)
    (he : a ++ t :: u = b ++ t :: v) : a = b ∧ u = v := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨rfl, (List.cons.inj he).2⟩
    | cons x b =>
      have hx := (List.cons.inj he).1
      exact (hb (by simp [hx])).elim
  | cons x a ih =>
    cases b with
    | nil =>
      have hx := (List.cons.inj he).1
      exact (ha (by simp [hx])).elim
    | cons y b =>
      obtain ⟨rfl, htail⟩ := List.cons.inj he
      obtain ⟨rfl, rfl⟩ := ih
        (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hb (List.mem_cons_of_mem _ h)) htail
      exact ⟨rfl, rfl⟩

theorem block_cancel {a b : A} {u v : List S}
    (he : C.block a ++ u = C.block b ++ v) : a = b ∧ u = v := by
  simp only [block, List.cons_append, List.append_assoc] at he
  obtain ⟨hab, huv⟩ := split_at_stop (C.stop_avoids a) (C.stop_avoids b)
    (List.cons.inj he).2
  exact ⟨C.injective hab, huv⟩

theorem prefix_decode {u v : List A} {y : List S}
    (h : C.encode v = C.encode u ++ y) : ∃ w, v = u ++ w ∧ y = C.encode w := by
  induction u generalizing v with
  | nil => exact ⟨v, rfl, h.symm⟩
  | cons a u ih =>
    cases v with
    | nil => simp [block] at h
    | cons b v =>
      simp only [encode_cons, List.append_assoc] at h
      obtain ⟨rfl, ht⟩ := C.block_cancel h
      obtain ⟨w, rfl, rfl⟩ := ih ht
      exact ⟨w, rfl, rfl⟩

theorem encode_injective : Function.Injective C.encode := by
  intro u v h
  obtain ⟨w, hu, hw⟩ := C.prefix_decode (y := []) (by simpa using h)
  have hw : w = [] := (C.encode_eq_nil w).mp hw.symm
  simpa only [hw, List.append_nil] using hu

theorem split_past_avoiding {b : S} {t z x y : List S} (ht : b ∉ t)
    (h : t ++ z = x ++ b :: y) : ∃ x', x = t ++ x' ∧ z = x' ++ b :: y := by
  induction t generalizing x with
  | nil => exact ⟨x, rfl, h⟩
  | cons a t ih =>
    cases x with
    | nil =>
      have ha : a = b := (List.cons.inj h).1
      exact (ht (by simp [ha])).elim
    | cons c x =>
      obtain ⟨rfl, htail⟩ := List.cons.inj h
      obtain ⟨x', rfl, hz⟩ := ih (fun hh => ht (List.mem_cons_of_mem _ hh)) htail
      exact ⟨x', rfl, hz⟩

theorem tail_avoids (a : A) : C.start ∉ C.body a ++ [C.stop] := by
  simp [C.start_avoids, C.distinct]

theorem marker_alignment {v : List A} {x y : List S}
    (h : C.encode v = x ++ C.start :: y) :
    ∃ u a w, v = u ++ a :: w ∧ x = C.encode u ∧
      y = C.body a ++ C.stop :: C.encode w := by
  induction v generalizing x with
  | nil => simp at h
  | cons a v ih =>
    cases x with
    | nil =>
      have hy : (C.body a ++ [C.stop]) ++ C.encode v = y := (List.cons.inj h).2
      exact ⟨[], a, v, rfl, rfl, by simpa only [List.append_assoc, List.singleton_append] using hy.symm⟩
    | cons b x =>
      obtain ⟨rfl, hv⟩ := List.cons.inj h
      obtain ⟨x', rfl, hv'⟩ :=
        split_past_avoiding (C.tail_avoids a) hv
      obtain ⟨u, b, w, rfl, hx, hy⟩ := ih hv'
      exact ⟨a :: u, b, w, rfl, by simp [block, hx], hy⟩

theorem occurrence_decode {v u : List A} (hu : u ≠ []) {x y : List S}
    (h : C.encode v = x ++ C.encode u ++ y) :
    ∃ p q, v = p ++ u ++ q ∧ x = C.encode p ∧ y = C.encode q := by
  cases u with
  | nil => contradiction
  | cons a u =>
    have hm : C.encode v = x ++ C.start :: (C.body a ++ C.stop :: (C.encode u ++ y)) := by
      simpa [block, List.append_assoc] using h
    obtain ⟨p, b, w, hv, rfl, _⟩ := C.marker_alignment hm
    have hh : C.encode (b :: w) = C.encode (a :: u) ++ y := by
      apply List.append_cancel_left (as := C.encode p)
      simpa only [hv, encode_append, List.append_assoc] using h
    obtain ⟨q, hq, hqy⟩ := C.prefix_decode hh
    exact ⟨p, q, by rw [hv, hq, List.append_assoc], rfl, hqy⟩

theorem overlap_decode {u v : List A} {p middle q : List S}
    (hm : middle ≠ []) (h₁ : C.encode u = p ++ middle)
    (h₂ : C.encode v = middle ++ q) :
    ∃ a b c, u = a ++ b ∧ v = b ++ c ∧ p = C.encode a ∧
      middle = C.encode b ∧ q = C.encode c := by
  cases v with
  | nil => simp at h₂; exact (hm h₂.1).elim
  | cons v vs =>
    cases middle with
    | nil => contradiction
    | cons m middle =>
      have hm' : m = C.start := (List.cons.inj h₂).1.symm
      subst m
      obtain ⟨a, b, bs, hu, hp, ht⟩ := C.marker_alignment h₁
      have hs : C.start :: middle = C.encode (b :: bs) := by simp [block, ht]
      obtain ⟨c, hv, hq⟩ := C.prefix_decode (show
        C.encode (v :: vs) = C.encode (b :: bs) ++ q by simpa [hs] using h₂)
      exact ⟨a, b :: bs, c, hu, hv, hp, hs, hq⟩

def cost (c : A → ℕ) (w : List A) : ℕ := (w.map c).sum
@[simp] theorem cost_nil (c : A → ℕ) : cost c [] = 0 := rfl
@[simp] theorem cost_cons (c : A → ℕ) (a : A) (w : List A) :
    cost c (a :: w) = c a + cost c w := rfl
@[simp] theorem cost_append (c : A → ℕ) (u v : List A) :
    cost c (u ++ v) = cost c u + cost c v := by simp [cost]

theorem cost_bound (c : A → ℕ)
    (hc : ∀ a, 10 * c a + 2 ≤ (C.block a).length) (w : List A) :
    10 * cost c w + 2 * w.length ≤ (C.encode w).length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have := hc a
    simp only [cost_cons, encode_cons, List.length_append, List.length_cons] at *
    omega

theorem cost_le_quota (c : A → ℕ)
    (hc : ∀ a, 10 * c a + 2 ≤ (C.block a).length)
    {w : List A} {n : ℕ} (hw : (C.encode w).length ≤ n) : cost c w ≤ n / 10 := by
  have := C.cost_bound c hc w
  omega

end DelimiterCode

theorem strict_dependency {n : ℕ} (hn : 0 < n) : 3 * (n / 10) < n := by omega

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding

namespace PaddedCode
section Syntax
variable {A : Type*} [Encodable A]

def body (cost : A → ℕ) (a : A) : List (Fin 4) :=
  List.replicate (Encodable.encode a) 0 ++ 1 :: List.replicate (10 * cost a) 0

def code (cost : A → ℕ) : DelimiterCode A (Fin 4) where
  start := 2
  stop := 3
  distinct := by decide
  body := body cost
  start_avoids := by intro a; simp [body]
  stop_avoids := by intro a; simp [body]
  injective := by
    intro a b he
    have hi (a : A) : (body cost a).idxOf 1 = Encodable.encode a := by
      rw [body, List.idxOf_append_of_notMem (by simp)]
      simp
    apply Encodable.encode_injective
    simpa only [hi] using congrArg (List.idxOf 1) he

@[simp] theorem block_length (cost : A → ℕ) (a : A) :
    ((code cost).block a).length = Encodable.encode a + 10 * cost a + 3 := by
  simp [DelimiterCode.block_length, code, body]
  omega

theorem descriptor_le_length (cost : A → ℕ) (a : A) :
    Encodable.encode a ≤ ((code cost).block a).length := by
  rw [block_length]; omega

theorem cost_padding (cost : A → ℕ) (a : A) :
    10 * cost a + 2 ≤ ((code cost).block a).length := by
  rw [block_length]; omega

def symbols (n : ℕ) : List A := (List.range (n + 1)).filterMap (Encodable.decode (α := A))

theorem mem_symbols_of_encode_le {a : A} {n : ℕ} (ha : Encodable.encode a ≤ n) :
    a ∈ symbols n := by
  apply List.mem_filterMap.mpr
  exact ⟨Encodable.encode a, List.mem_range.mpr (by omega), Encodable.encodek a⟩

def wordsOver (xs : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n + 1 => [] :: xs.flatMap (fun a => (wordsOver xs n).map (a :: ·))

omit [Encodable A] in
@[simp] theorem mem_wordsOver [Encodable A] (xs : List A) (n : ℕ) (w : List A) :
    w ∈ wordsOver xs n ↔ w.length ≤ n ∧ ∀ a ∈ w, a ∈ xs := by
  induction n generalizing w with
  | zero =>
    cases w <;> simp [wordsOver]
  | succ n ih =>
    cases w with
    | nil => simp [wordsOver]
    | cons a w =>
      rw [wordsOver, List.mem_cons]
      constructor
      · rintro (he | h)
        · cases he
        · obtain ⟨b, hb, h⟩ := List.mem_flatMap.mp h
          obtain ⟨v, hv, he⟩ := List.mem_map.mp h
          obtain ⟨rfl, rfl⟩ := List.cons.inj he
          obtain ⟨hlen, hs⟩ := (ih v).mp hv
          exact ⟨by simpa using Nat.succ_le_succ hlen,
            by simpa [List.mem_cons] using And.intro hb hs⟩
      · rintro ⟨hlen, hs⟩
        right
        refine List.mem_flatMap.mpr ⟨a, hs a List.mem_cons_self,
          List.mem_map.mpr ⟨w, ?_, rfl⟩⟩
        exact (ih w).mpr ⟨by simpa using hlen,
          fun b hb => hs b (List.mem_cons_of_mem _ hb)⟩

omit [Encodable A] in
theorem block_length_le_encode [Encodable A] (C : DelimiterCode A (Fin 4)) {a : A} {w : List A}
    (ha : a ∈ w) : (C.block a).length ≤ (C.encode w).length := by
  induction w with
  | nil => simp at ha
  | cons b w ih =>
    simp only [DelimiterCode.encode_cons, List.length_append]
    rcases List.mem_cons.mp ha with rfl | ha
    · omega
    · have := ih ha; omega

def words (cost : A → ℕ) (n : ℕ) : List (List A) :=
  (wordsOver (symbols n) n).filter fun w => ((code cost).encode w).length ≤ n

@[simp] theorem mem_words (cost : A → ℕ) (n : ℕ) (w : List A) :
    w ∈ words cost n ↔ ((code cost).encode w).length ≤ n := by
  simp only [words, List.mem_filter, decide_eq_true_eq]
  refine ⟨And.right, fun hw => ⟨?_, hw⟩⟩
  apply (mem_wordsOver _ _ _).mpr
  refine ⟨?_, ?_⟩
  · have := (code cost).length_le_encode w
    omega
  · intro a ha
    exact mem_symbols_of_encode_le
      ((descriptor_le_length cost a).trans ((block_length_le_encode _ ha).trans hw))

end Syntax

variable {A : Type*} [Primcodable A]

theorem primrec_replicate (b : Fin 4) : Primrec (fun n => List.replicate n b) :=
  (Primrec.nat_rec₁ [] (Primrec.list_cons.comp (Primrec.const b) Primrec.snd).to₂).of_eq
    (by intro n; induction n <;> simp_all [List.replicate_succ])

theorem primrec_block (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (code cost).block := by
  exact Primrec.list_cons.comp (Primrec.const 2)
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        ((primrec_replicate 0).comp Primrec.encode)
        (Primrec.list_cons.comp (Primrec.const 1)
          ((primrec_replicate 0).comp
            (Primrec.nat_mul.comp (Primrec.const 10) hc))))
      (Primrec.const [3]))

theorem primrec_encode (cost : A → ℕ) (hc : Primrec cost) :
    Primrec (code cost).encode :=
  Primrec.list_flatMap Primrec.id ((primrec_block cost hc).comp Primrec.snd).to₂

theorem primrec_symbols : Primrec (@symbols A _) :=
  Primrec.listFilterMap (Primrec.list_range.comp Primrec.succ)
    (Primrec.decode.comp Primrec.snd).to₂

theorem primrec_wordsOver : Primrec₂ (@wordsOver A) := by
  exact (Primrec.nat_rec (Primrec.const [[]])
    (Primrec.list_cons.comp (Primrec.const [])
      (Primrec.list_flatMap Primrec.fst
        (Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂).to₂)).to₂).of_eq
            fun ls n => by induction n <;> simp_all [wordsOver]

theorem primrec_words (cost : A → ℕ) (hc : Primrec cost) : Primrec (words cost) := by
  have hfilter : Primrec (fun n => (wordsOver (symbols n) n).filterMap
      (fun w => if ((code cost).encode w).length ≤ n then some w else none)) :=
    Primrec.listFilterMap (primrec_wordsOver.comp primrec_symbols Primrec.id)
      (Primrec.ite (Primrec.nat_le.comp
        (Primrec.list_length.comp ((primrec_encode cost hc).comp Primrec.snd))
        Primrec.fst) (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  apply hfilter.of_eq
  intro n
  simp only [words, ← List.filterMap_eq_filter, Option.guard, decide_eq_true_eq]

end PaddedCode
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open Relation

structure FiniteSearch {A S : Type*} (C : DelimiterCode A S) where
  words : ℕ → List (List A)
  mem_words : ∀ n w, w ∈ words n ↔ (C.encode w).length ≤ n

namespace EncodedCanonical
variable {A S Q : Type*} {r : S → S → Prop}
variable (C : DelimiterCode A S) (wf : WellFounded r) [Std.Trichotomous r]
  (q : List A → Q)

def candidates (w : List A) : Set (List A) :=
  {v | (C.encode v).length ≤ (C.encode w).length ∧ q v = q w}

noncomputable def least (w : List A) : List A :=
  (InvImage.wf C.encode (List.Shortlex.wf wf)).min (candidates C q w) ⟨w, le_rfl, rfl⟩

omit [Std.Trichotomous r] in
theorem least_mem [Std.Trichotomous r] (w : List A) : least C wf q w ∈ candidates C q w :=
  (InvImage.wf C.encode (List.Shortlex.wf wf)).min_mem _ _

theorem least_length (w : List A) : (C.encode (least C wf q w)).length ≤ (C.encode w).length :=
  (least_mem C wf q w).1

theorem least_class (w : List A) : q (least C wf q w) = q w := (least_mem C wf q w).2

omit [Std.Trichotomous r] in
theorem least_min [Std.Trichotomous r] {w v : List A} (hv : (C.encode v).length ≤ (C.encode w).length)
    (hq : q v = q w) : ¬ List.Shortlex r (C.encode v) (C.encode (least C wf q w)) :=
  (InvImage.wf C.encode (List.Shortlex.wf wf)).not_lt_min (candidates C q w) ⟨hv, hq⟩

theorem least_lt_or_eq (w : List A) :
    List.Shortlex r (C.encode (least C wf q w)) (C.encode w) ∨ least C wf q w = w := by
  by_cases h : List.Shortlex r (C.encode (least C wf q w)) (C.encode w)
  · exact Or.inl h
  · exact Or.inr (C.encode_injective
      (Std.Trichotomous.trichotomous _ _ h (least_min C wf q le_rfl rfl)))

theorem least_global_min {w v : List A} (hq : q v = q w) :
    ¬ List.Shortlex r (C.encode v) (C.encode (least C wf q w)) := by
  intro hd
  have hlen : (C.encode v).length ≤ (C.encode w).length := by
    have hm := least_length C wf q w
    have he := List.shortlex_def.mp hd
    omega
  exact least_min C wf q hlen hq hd

theorem least_congr {u v : List A} (hq : q u = q v) : least C wf q u = least C wf q v := by
  apply C.encode_injective
  exact Std.Trichotomous.trichotomous _ _
    (least_global_min C wf q ((least_class C wf q u).trans hq))
    (least_global_min C wf q ((least_class C wf q v).trans hq.symm))

theorem least_nil : least C wf q [] = [] := by
  have h := least_length C wf q []
  have h' : C.encode (least C wf q []) = [] := List.length_eq_zero_iff.mp (by simpa using h)
  exact (C.encode_eq_nil _).mp h'

end EncodedCanonical

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

noncomputable def output (v : List A) : List S :=
  if q v = none then [z] else C.encode (EncodedCanonical.least C wf q v)

noncomputable def table (n : ℕ) : List (List S × List S) := by
  classical
  exact ((E.words n).filter fun v => v ≠ [] ∧ output C wf q z v ≠ C.encode v).map
    (fun v => (C.encode v, output C wf q z v))

omit [Std.Trichotomous r] in
theorem mem_table [Std.Trichotomous r] {n : ℕ} {a b : List S} : (a,b) ∈ table C E wf q z n ↔
    ∃ v, (C.encode v).length ≤ n ∧ v ≠ [] ∧ output C wf q z v ≠ C.encode v ∧
      a = C.encode v ∧ b = output C wf q z v := by
  classical
  simp only [table, List.mem_map, List.mem_filter, E.mem_words,
    decide_eq_true_eq, Prod.mk.injEq]
  aesop

theorem output_congr {u v : List A} (hq : q u = q v) : output C wf q z u = output C wf q z v := by
  simp only [output, hq, EncodedCanonical.least_congr C wf q hq]

theorem output_nil (hzero : q [] ≠ none) : output C wf q z [] = [] := by
  simp [output, hzero, EncodedCanonical.least_nil]

def Contextual (n : ℕ) : Prop :=
  ∀ a b u v : List A, (C.encode (a++u++b)).length ≤ n →
    (C.encode (a++v++b)).length ≤ n → q u = q v → q (a++u++b) = q (a++v++b)

def ZeroIdeal (n : ℕ) : Prop :=
  ∀ a b u : List A, (C.encode (a++u++b)).length ≤ n → q u = none → q (a++u++b) = none

end CodeTable
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FamilyTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open Relation

namespace DelimiterCode
variable {A B S : Type*}

def alphabet (C : DelimiterCode A S) : Set S :=
  {s | s = C.start ∨ s = C.stop ∨ ∃ a, s ∈ C.body a}

theorem mem_alphabet_of_mem_encode (C : DelimiterCode A S) {s : S} {w : List A}
    (hs : s ∈ C.encode w) : s ∈ C.alphabet := by
  obtain ⟨a, _, ha⟩ := List.mem_flatMap.mp hs
  simp only [block, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨a, h⟩)
  · exact Or.inr (Or.inl h)

theorem disjoint_infix (C : DelimiterCode A S) (D : DelimiterCode B S)
    (hd : Disjoint C.alphabet D.alphabet) {u : List A} {v : List B}
    (hv : v ≠ []) (he : D.encode v <:+: C.encode u) : False := by
  have hn : D.encode v ≠ [] := fun h => hv ((D.encode_eq_nil _).mp h)
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hn
  exact (Set.disjoint_left.mp hd) (C.mem_alphabet_of_mem_encode (he.subset hs))
    (D.mem_alphabet_of_mem_encode hs)

theorem disjoint_overlap (C : DelimiterCode A S) (D : DelimiterCode B S)
    (hd : Disjoint C.alphabet D.alphabet) {u : List A} {v : List B} {p m q : List S}
    (hm : m ≠ []) (he : C.encode u = p++m) (hf : D.encode v = m++q) : False := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hm
  exact (Set.disjoint_left.mp hd)
    (C.mem_alphabet_of_mem_encode (by rw [he]; exact List.mem_append_right _ hs))
    (D.mem_alphabet_of_mem_encode (by rw [hf]; exact List.mem_append_left _ hs))
end DelimiterCode

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_CodeEmbedding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
open Relation

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]
variable (C : DelimiterCode A S) (E : FiniteSearch C) (wf : WellFounded r)
  (q : List A → Option Q) (z : S)

 theorem table_short {n : ℕ} {p : List S × List S} (hp : p ∈ table C E wf q z n) :
    1 < p.1.length := by
  obtain ⟨w,_,hn,_,he,_⟩ := (mem_table C E wf q z).mp hp
  rw [he]
  have := C.length_le_encode w
  have := List.length_pos_iff.mpr hn
  omega

end CodeTable

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContractedNormalForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.SemanticEncoding
noncomputable section
open scoped Classical

structure NormalPresentation (M K : Type*) [Monoid M] [MonoidWithZero K] where
  q : M →* K
  surjective : Function.Surjective q
  normal : M → M
  omega : M
  zero : q omega = 0
  complete : ∀ u v, q u = q v ↔ normal u = normal v
  idempotent : ∀ u, normal (normal u) = normal u
  fixesZero : normal omega = omega

namespace NormalPresentation
variable {M K : Type*} [Monoid M] [MonoidWithZero K] (P : NormalPresentation M K)
variable (k : Type*) [CommRing k]

 theorem q_normal (w : M) : P.q (P.normal w) = P.q w :=
  (P.complete _ _).mpr (P.idempotent w)

 theorem normal_eq_zero_iff (w : M) : P.normal w = P.omega ↔ P.q w = 0 := by
  rw [← P.fixesZero, ← P.complete, P.zero]

def representative (h : K) : M := P.normal (P.surjective h).choose

 theorem representative_q (w : M) : P.representative (P.q w) = P.normal w := by
  apply (P.complete _ _).mp
  exact (P.surjective _).choose_spec

 theorem q_representative (h : K) : P.q (P.representative h) = h :=
  (P.q_normal _).trans (P.surjective h).choose_spec

end NormalPresentation
end
end SimpleFInftyOvergroups.SemanticEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveTables
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding

namespace CodedSearch
variable {A S Q : Type*} [DecidableEq S] [DecidableEq Q]
variable {r : S → S → Prop} [DecidableRel (List.Shortlex r)]
variable (C : DelimiterCode A S)

def lt (u v : List A) : Bool := decide (List.Shortlex r (C.encode u) (C.encode v))

end CodedSearch

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FamilyProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding

namespace CodeTable
variable {A S Q : Type*} {r : S → S → Prop} [Std.Trichotomous r]

theorem table_zero (C : DelimiterCode A S) (E : FiniteSearch C)
    (wf : WellFounded r) (q : List A → Option Q) (z : S) :
    table C E wf q z 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  rintro ⟨u,v⟩ hp
  obtain ⟨w,hw,hn,_,_,_⟩ := (mem_table C E wf q z).mp hp
  exact hn ((C.encode_eq_nil _).mp (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)))
end CodeTable

end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EffectiveFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
noncomputable section
open scoped Classical

namespace FiniteParameter
variable {I X Y : Type*} [Primcodable I] [Primcodable X] [Primcodable Y]
  [DecidableEq I] (f : I → X → Part Y)

def select (l : List I) (p : I × X) : Part Y :=
  l.foldr (fun i rest => if p.1 = i then f i p.2 else rest) Part.none

theorem select_partrec (hf : ∀ i, Partrec (f i)) (l : List I) : Partrec (select f l) := by
  induction l with
  | nil => exact Partrec.none
  | cons i l ih =>
    exact (Partrec.cond (Primrec.eq.comp Primrec.fst (Primrec.const i)).decide.to_comp
      ((hf i).comp Computable.snd) ih).of_eq (by
        intro p
        simp only [select,List.foldr_cons]
        split <;> simp_all)

omit [Primcodable I] [Primcodable X] [Primcodable Y] in
theorem select_mem [Primcodable I] [Primcodable X] [Primcodable Y]
    (l : List I) (p : I × X) (hp : p.1 ∈ l) : select f l p = f p.1 p.2 := by
  induction l with
  | nil => simp at hp
  | cons i l ih =>
    simp only [select,List.foldr_cons]
    split
    next h => simp only [h]
    next h => exact ih ((List.mem_cons.mp hp).resolve_left h)

end FiniteParameter

end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

namespace WordCalculus
variable {M : Type*}
  [Monoid M]
  {m : ℕ}
variable (k : Type*) [CommRing k] {ι : Type*} [Fintype ι] [DecidableEq ι]

@[instance_reducible] def rawMatrixAction : MulAction (Matrix ι ι (MonoidAlgebra k M))ˣ (ι → MonoidAlgebra k M) where
  smul u x := u.val.mulVec x
  one_smul x := Matrix.one_mulVec x
  mul_smul u v x := (Matrix.mulVec_mulVec x u.val v.val).symm

attribute [local instance] rawMatrixAction

end WordCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding
noncomputable section
open scoped Classical
variable {G X P k : Type*}
  [CommRing k]

abbrev Word (P G : Type*) := List (P × G)
abbrev Point (P G X : Type*) := Word P G × X

end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_FiniteNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SimpleFInftyOvergroups.EffectiveNames.Finite
variable {A B P : Type*} {n : ℕ}

def traverse (f : A → Part B) (x : Fin n → A) : Part (Fin n → B) :=
  (List.Vector.mOfFn (fun i => f (x i))).map List.Vector.get

theorem vector_full (f : Fin n → Part B) (g : Fin n → B) (h : ∀ i, g i ∈ f i) :
    List.Vector.ofFn g ∈ List.Vector.mOfFn f := by
  induction n with
  | zero => exact Part.mem_some _
  | succ n ih =>
    simp only [List.Vector.mOfFn]
    refine Part.mem_bind_iff.mpr ⟨g 0, h 0, ?_⟩
    exact Part.mem_bind_iff.mpr ⟨_,ih (fun i => f i.succ) (fun i => g i.succ)
      (fun i => h i.succ), Part.mem_some _⟩

theorem traverse_full (f : A → Part B) (g : A → B) (x : Fin n → A)
    (h : ∀ i, g (x i) ∈ f (x i)) : (fun i => g (x i)) ∈ traverse f x := by
  change _ ∈ (List.Vector.mOfFn (fun i => f (x i))).map List.Vector.get
  convert Part.mem_map List.Vector.get (vector_full (fun i => f (x i)) (fun i => g (x i)) h) using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  exact (List.Vector.get_ofFn (fun i => g (x i)) i).symm

variable [Primcodable A] [Primcodable B] [Primcodable P]

 theorem partrec_traverse {f : P → A → Part B} (hf : Partrec₂ f) :
    Partrec₂ (fun p : P => traverse (n:=n) (f p)) := by
  have hh : ∀ i : Fin n, Partrec (fun p : P × (Fin n → A) => f p.1 (p.2 i)) :=
    fun i => hf.comp Computable.fst (Primrec.fin_app.to_comp.comp Computable.snd (Computable.const i))
  exact (Partrec.vector_mOfFn hh).map (Primrec.vector_get'.to_comp.comp Computable.snd).to₂

 theorem primrec_function {f : P → Fin n → B} (hf : ∀ i, Primrec (fun p => f p i)) :
    Primrec f := by
  exact (Primrec.vector_get'.comp (Primrec.vector_ofFn hf)).of_eq
    (fun p => by funext i; simp)
end SimpleFInftyOvergroups.EffectiveNames.Finite

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PolynomialNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace SimpleFInftyOvergroups.EffectiveNames.Polynomial
open BoundedEncoding
noncomputable section
open scoped Classical

variable {A k : Type*} [CommSemiring k]

abbrev Name (k A : Type*) := List (k × List A)

def value (p : Name k A) : MonoidAlgebra k (FreeMonoid A) :=
  (p.map fun a => MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1).sum

@[simp] theorem value_nil : value ([] : Name k A) = 0 := rfl
@[simp] theorem value_cons (a : k × List A) (p : Name k A) :
    value (a::p) = MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1 + value p := rfl
@[simp] theorem value_append (p q : Name k A) : value (p++q) = value p + value q := by
  simp [value]

def oneName : Name k A := [(1,[])]
@[simp] theorem value_oneName : value (oneName : Name k A) = 1 := by
  simp [oneName,MonoidAlgebra.one_def]

def product (p q : Name k A) : Name k A :=
  p.flatMap fun a => q.map fun b => (a.1*b.1,a.2++b.2)

theorem value_mul_term (a : k × List A) (q : Name k A) :
    value (q.map fun b => (a.1*b.1,a.2++b.2)) =
      MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1 * value q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons,value_cons,ih,mul_add,MonoidAlgebra.single_mul_single]
    rfl

@[simp] theorem value_product (p q : Name k A) : value (product p q) = value p * value q := by
  induction p with
  | nil => simp [product]
  | cons a p ih =>
    simp only [product,List.flatMap_cons] at ih ⊢
    rw [value_append,value_mul_term,ih,value_cons,add_mul]

theorem value_surjective : Function.Surjective (value (k:=k) (A:=A)) := by
  intro p
  induction p using MonoidAlgebra.induction_on with
  | of w => exact ⟨[(1,w.toList)],by simp⟩
  | add p q hp hq =>
    obtain ⟨p,rfl⟩ := hp
    obtain ⟨q,rfl⟩ := hq
    exact ⟨p++q,value_append _ _⟩
  | smul a p hp =>
    obtain ⟨p,rfl⟩ := hp
    refine ⟨p.map (fun b => (a*b.1,b.2)),?_⟩
    induction p with
    | nil => simp
    | cons b p ih => simp [ih,smul_add,MonoidAlgebra.smul_single]

def cost (grade : List A → ℕ) (p : Name k A) : ℕ :=
  (p.map (fun a => grade a.2)).foldr max 0

omit [CommSemiring k] in
theorem cost_le_iff (grade : List A → ℕ) (p : Name k A) (b : ℕ) :
    cost grade p ≤ b ↔ ∀ a ∈ p, grade a.2 ≤ b := by
  induction p with
  | nil => simp [cost]
  | cons a p ih =>
    simp only [cost,List.map_cons,List.foldr_cons,max_le_iff] at ih ⊢
    simp only [List.mem_cons,forall_eq_or_imp]
    exact and_congr_right (fun _ => ih)

omit [CommSemiring k] in
 theorem term_cost_le (grade : List A → ℕ) {a : k × List A} {p : Name k A} (ha : a ∈ p) :
    grade a.2 ≤ cost grade p := (cost_le_iff grade p _).mp le_rfl a ha

variable {m : ℕ}

def collectName (omega : List A) (normal : List A → List A) (p : Name k A) : Name k A :=
  p.flatMap fun a => if normal a.2 = omega then [] else [(a.1,normal a.2)]

variable [Primcodable A] [Primcodable k] [Finite k]

 theorem primrec_product : Primrec₂ (product (k:=k) (A:=A)) := by
  unfold product
  apply Primrec.list_flatMap Primrec.fst
  apply Primrec.list_map (Primrec.snd.comp Primrec.fst)
  exact (((Primrec.dom_finite (fun p : k × k => p.1*p.2)).comp
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd))).pair
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd))).to₂

omit [CommSemiring k] [Finite k] in
 theorem primrec_cost {grade : List A → ℕ} (hg : Primrec grade) : Primrec (cost (k:=k) grade) := by
  unfold cost
  exact Primrec.list_foldr
    (Primrec.list_map Primrec.id (hg.comp (Primrec.snd.comp Primrec.snd)).to₂)
    (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

omit [Primcodable A] [Primcodable k] [Finite k] in
theorem value_eq_iff_arrays (p q : Name k A) :
    value p = value q ↔ Array.value (id : k → k) (id : List A → List A) p =
      Array.value id id q := by
  have h (p : Name k A) : (value p).coeff =
      Finsupp.mapDomain FreeMonoid.ofList (Array.value (id : k → k) id p) := by
    induction p with
    | nil => simp
    | cons a p ih => simp [ih, Finsupp.mapDomain_add]
  rw [← MonoidAlgebra.coeff_inj, h p, h q]
  exact (Finsupp.mapDomain_injective (f := FreeMonoid.ofList)
    (by intro x y h; exact congrArg FreeMonoid.toList h)).eq_iff

def valueKey : MonoidAlgebra k (FreeMonoid A) → ℕ := semanticKey value value_surjective

omit [Finite k] in
 theorem valueKey_injective : Function.Injective (valueKey (k:=k) (A:=A)) :=
  semanticKey_injective value value_surjective

omit [Finite k] in
@[simp] theorem valueKey_value (p : Name k A) : valueKey (value p) = key value p :=
  semanticKey_value value value_surjective p

end
end SimpleFInftyOvergroups.EffectiveNames.Polynomial

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_PolynomialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Polynomial
open BoundedEncoding
noncomputable section
open scoped Classical
variable {A k : Type*} [CommSemiring k]

omit [CommSemiring k] in
@[simp] theorem cost_nil (grade : List A → ℕ) : cost grade ([] : Name k A) = 0 := rfl

omit [CommSemiring k] in
 theorem cost_append (grade : List A → ℕ) (p q : Name k A) :
    cost grade (p++q) = max (cost grade p) (cost grade q) := by
  apply Nat.le_antisymm
  · rw [cost_le_iff]
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (term_cost_le grade ha).trans (Nat.le_max_left _ _)
    · exact (term_cost_le grade ha).trans (Nat.le_max_right _ _)
  · rw [max_le_iff, cost_le_iff, cost_le_iff]
    exact ⟨fun a ha => term_cost_le grade (List.mem_append_left _ ha),
      fun a ha => term_cost_le grade (List.mem_append_right _ ha)⟩

 theorem value_flatten (ps : List (Name k A)) : value ps.flatten = (ps.map value).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

omit [CommSemiring k] in
 theorem cost_flatten_le (grade : List A → ℕ) {ps : List (Name k A)} {b : ℕ}
    (h : ∀ p ∈ ps, cost grade p ≤ b) : cost grade ps.flatten ≤ b := by
  rw [cost_le_iff]
  intro a ha
  obtain ⟨p,hp,ha⟩ := List.mem_flatten.mp ha
  exact (term_cost_le grade ha).trans (h p hp)

 theorem cost_product_le (grade : List A → ℕ)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (p q : Name k A) :
    cost grade (product p q) ≤ cost grade p + cost grade q := by
  rw [cost_le_iff]
  intro x hx
  obtain ⟨a,ha',hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  rw [ha]
  exact Nat.add_le_add (term_cost_le grade ha') (term_cost_le grade hb)

 theorem cost_oneName (grade : List A → ℕ) (h0 : grade [] = 0) :
    cost grade (oneName : Name k A) = 0 := by simp [oneName,cost,h0]

variable {R : Type*} [CommRing R]
def negate (p : Name R A) : Name R A := p.map (fun a => (-a.1,a.2))

@[simp] theorem value_negate (p : Name R A) : value (negate p) = -value p := by
  induction p with
  | nil => simp [negate]
  | cons a p ih =>
    change MonoidAlgebra.single (FreeMonoid.ofList a.2) (-a.1) + value (negate p) =
      -(MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1 + value p)
    rw [MonoidAlgebra.single_neg,ih]
    abel

@[simp] theorem cost_negate (grade : List A → ℕ) (p : Name R A) :
    cost grade (negate p) = cost grade p := by
  simp only [negate,cost,List.map_map,Function.comp_def]

 theorem primrec_negate [Primcodable A] [Primcodable R] [Finite R] :
    Primrec (negate (R:=R) (A:=A)) := by
  exact Primrec.list_map Primrec.id
    (((Primrec.dom_finite (Neg.neg : R → R)).comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)).to₂
end
end SimpleFInftyOvergroups.EffectiveNames.Polynomial

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixNames
open BoundedEncoding
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}
abbrev Column (k A : Type*) (n : ℕ) := Fin n → Polynomial.Name k A
abbrev Name (k A : Type*) (n : ℕ) := Fin n → Column k A n
abbrev Raw (k A : Type*) [CommRing k] := MonoidAlgebra k (FreeMonoid A)

def columnValue (x : Column k A n) : Fin n → Raw k A := fun i => Polynomial.value (x i)
def value (a : Name k A n) : Matrix (Fin n) (Fin n) (Raw k A) := fun i => columnValue (a i)

def maximum (f : Fin n → ℕ) : ℕ := (List.ofFn f).foldr max 0

theorem maximum_le_iff (f : Fin n → ℕ) (b : ℕ) : maximum f ≤ b ↔ ∀ i, f i ≤ b := by
  suffices h : ∀ l : List ℕ, l.foldr max 0 ≤ b ↔ ∀ x ∈ l, x ≤ b by
    simp only [maximum,h,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff]
  intro l
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons,max_le_iff,ih,List.mem_cons,forall_eq_or_imp]

 theorem le_maximum (f : Fin n → ℕ) (i : Fin n) : f i ≤ maximum f :=
  (maximum_le_iff f _).mp le_rfl i

def columnCost (grade : List A → ℕ) (x : Column k A n) := maximum (fun i => Polynomial.cost grade (x i))
def cost (grade : List A → ℕ) (a : Name k A n) := maximum (fun i => columnCost grade (a i))

omit [CommRing k] in
 theorem entry_cost_le (grade : List A → ℕ) (a : Name k A n) (i j : Fin n) :
    Polynomial.cost grade (a i j) ≤ cost grade a :=
  (le_maximum (fun j => Polynomial.cost grade (a i j)) j).trans
    (le_maximum (fun i => columnCost grade (a i)) i)

omit [CommRing k] in
 theorem column_entry_cost_le (grade : List A → ℕ) (x : Column k A n) (i : Fin n) :
    Polynomial.cost grade (x i) ≤ columnCost grade x := le_maximum (fun i => Polynomial.cost grade (x i)) i

def oneName : Name k A n := fun i j => if i=j then Polynomial.oneName else []

def product (a b : Name k A n) : Name k A n :=
  fun i j => (List.ofFn (fun l => Polynomial.product (a i l) (b l j))).flatten

def mulVec (a : Name k A n) (x : Column k A n) : Column k A n :=
  fun i => (List.ofFn (fun j => Polynomial.product (a i j) (x j))).flatten

@[simp] theorem value_oneName : value (oneName : Name k A n) = 1 := by
  funext i j
  by_cases h : i=j <;> simp [value,columnValue,oneName,Matrix.one_apply,h]

@[simp] theorem value_product (a b : Name k A n) : value (product a b) = value a * value b := by
  ext i j
  simp only [value,columnValue,product,Polynomial.value_flatten,List.map_ofFn,
    Polynomial.value_product,Function.comp_def,List.sum_ofFn,Matrix.mul_apply]

@[simp] theorem value_mulVec (a : Name k A n) (x : Column k A n) :
    columnValue (mulVec a x) = (value a).mulVec (columnValue x) := by
  ext i
  simp only [value,columnValue,mulVec,Polynomial.value_flatten,List.map_ofFn,
    Polynomial.value_product,Function.comp_def,List.sum_ofFn,Matrix.mulVec,dotProduct]

 theorem cost_oneName (grade : List A → ℕ) (h0 : grade [] = 0) :
    cost grade (oneName : Name k A n) = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [cost,maximum_le_iff]
  intro i
  rw [columnCost,maximum_le_iff]
  intro j
  by_cases h : i=j <;> simp [oneName,h,Polynomial.cost_oneName grade h0]

 theorem cost_product_le (grade : List A → ℕ)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (a b : Name k A n) :
    cost grade (product a b) ≤ cost grade a + cost grade b := by
  rw [cost,maximum_le_iff]
  intro i
  rw [columnCost,maximum_le_iff]
  intro j
  apply Polynomial.cost_flatten_le
  intro p hp
  obtain ⟨l,rfl⟩ := List.mem_ofFn.mp hp
  exact (Polynomial.cost_product_le grade ha _ _).trans
    (Nat.add_le_add (entry_cost_le _ a i l) (entry_cost_le _ b l j))

 theorem cost_mulVec_le (grade : List A → ℕ)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (a : Name k A n) (x : Column k A n) :
    columnCost grade (mulVec a x) ≤ cost grade a + columnCost grade x := by
  rw [columnCost,maximum_le_iff]
  intro i
  apply Polynomial.cost_flatten_le
  intro p hp
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
  exact (Polynomial.cost_product_le grade ha _ _).trans
    (Nat.add_le_add (entry_cost_le _ a i j) (column_entry_cost_le _ x j))

variable {m : ℕ}

variable [Primcodable A] [Primcodable k] [Finite k]

 theorem primrec_maximum : Primrec (maximum (n:=n)) := by
  unfold maximum
  exact Primrec.list_foldr (Primrec.list_ofFn (fun i => Primrec.fin_app.comp Primrec.id (Primrec.const i)))
    (Primrec.const 0) (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

omit [CommRing k] [Finite k] in
 theorem primrec_columnCost {grade : List A → ℕ} (hg : Primrec grade) :
    Primrec (columnCost (k:=k) (n:=n) grade) :=
  primrec_maximum.comp (Finite.primrec_function fun i =>
    (Polynomial.primrec_cost hg).comp (Primrec.fin_app.comp Primrec.id (Primrec.const i)))

 theorem primrec_product : Primrec₂ (product (k:=k) (A:=A) (n:=n)) := by
  apply Finite.primrec_function
  intro i
  apply Finite.primrec_function
  intro j
  exact Primrec.list_flatten.comp (Primrec.list_ofFn fun l => Polynomial.primrec_product.comp
    (Primrec.fin_app.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const i)) (Primrec.const l))
    (Primrec.fin_app.comp (Primrec.fin_app.comp Primrec.snd (Primrec.const l)) (Primrec.const j)))

 theorem primrec_mulVec : Primrec₂ (mulVec (k:=k) (A:=A) (n:=n)) := by
  apply Finite.primrec_function
  intro i
  exact Primrec.list_flatten.comp (Primrec.list_ofFn fun j => Polynomial.primrec_product.comp
    (Primrec.fin_app.comp (Primrec.fin_app.comp Primrec.fst (Primrec.const i)) (Primrec.const j))
    (Primrec.fin_app.comp Primrec.snd (Primrec.const j)))

def columnKey (x : Fin n → Raw k A) : Fin n → ℕ := fun i => Polynomial.valueKey (x i)
def matrixKey (a : Matrix (Fin n) (Fin n) (Raw k A)) : Fin n → Fin n → ℕ :=
  fun i => columnKey (a i)

omit [Finite k] in
 theorem columnKey_injective : Function.Injective (columnKey (k:=k) (A:=A) (n:=n)) := by
  intro x y h
  funext i
  exact Polynomial.valueKey_injective (congrFun h i)

omit [Finite k] in
 theorem matrixKey_injective : Function.Injective (matrixKey (k:=k) (A:=A) (n:=n)) := by
  intro x y h
  funext i
  exact columnKey_injective (congrFun h i)

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixNames

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_MatrixWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.MatrixWords
open BoundedEncoding MatrixNames
noncomputable section
open scoped Classical
variable {A k : Type*} [CommRing k] {n : ℕ}

abbrev Root (k A : Type*) (n : ℕ) := Fin n × Fin n × Polynomial.Name k A
abbrev Word (k A : Type*) (n : ℕ) := List (Root k A n)
abbrev Point (k A : Type*) (n : ℕ) := Word k A n × Column k A n
abbrev V (k A : Type*) [CommRing k] (n : ℕ) := (Matrix (Fin n) (Fin n) (Raw k A))ˣ

def rootInv (r : Root k A n) : Root k A n := (r.1,r.2.1,Polynomial.negate r.2.2)
def inverse (w : Word k A n) : Word k A n := w.reverse.map rootInv

attribute [local instance] WordCalculus.rawMatrixAction

end
end SimpleFInftyOvergroups.EffectiveNames.MatrixWords

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_RingAssemblyTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups.RingAssembly
open scoped Classical TensorProduct

section Quotient
variable {R : Type*} [Ring R] (r : R → R → Prop)

def differences : Set R := (fun p : R × R => p.1-p.2) '' {p | r p.1 p.2}

 theorem differences_finite (h : {p : R × R | r p.1 p.2}.Finite) :
    (differences r).Finite := h.image _

 theorem ker_ringQuot : TwoSidedIdeal.ker (RingQuot.mkRingHom r) =
    TwoSidedIdeal.span (differences r) := by
  let I := TwoSidedIdeal.span (differences r)
  have respects : ∀ ⦃a b : R⦄, r a b → I.ringCon.mk' a=I.ringCon.mk' b := by
    intro a b hab
    apply I.ringCon.eq.mpr
    apply (I.rel_iff a b).mpr
    exact TwoSidedIdeal.subset_span ⟨(a,b),hab,rfl⟩
  let t : RingQuot r →+* I.ringCon.Quotient := RingQuot.lift ⟨I.ringCon.mk',respects⟩
  apply le_antisymm
  · intro x hx
    have hx' := congrArg t ((TwoSidedIdeal.mem_ker _).mp hx)
    have hq : I.ringCon.mk' x=0 := by
      simpa only [t,RingQuot.lift_mkRingHom_apply,map_zero] using hx'
    have hi := (TwoSidedIdeal.mem_ker I.ringCon.mk').mpr hq
    simpa only [TwoSidedIdeal.ker_ringCon_mk'] using hi
  · apply TwoSidedIdeal.span_le.mpr
    rintro x ⟨⟨a,b⟩,hab,rfl⟩
    apply (TwoSidedIdeal.mem_ker _).mpr
    rw [map_sub,RingQuot.mkRingHom_rel hab,sub_self]
end Quotient

section Corner
variable {R S : Type*} [Ring R] [Ring S]

theorem supportIdempotent (f : R →ₙ+* S) : IsIdempotentElem (f 1) := by
  change f 1*f 1=f 1
  rw [←map_mul,one_mul]

def toCorner (f : R →ₙ+* S) : R →+* (supportIdempotent f).Corner where
  toFun x := ⟨f x,(Subsemigroup.mem_corner_iff (supportIdempotent f)).mpr
    ⟨by rw [←map_mul,one_mul],by rw [←map_mul,mul_one]⟩⟩
  map_one' := rfl
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x y)
  map_mul' x y := Subtype.ext (map_mul f x y)

 theorem toCorner_injective (f : R →ₙ+* S) (hf : Function.Injective f) :
    Function.Injective (toCorner f) := by
  intro x y hxy
  exact hf (congrArg Subtype.val hxy)
end Corner

end SimpleFInftyOvergroups.RingAssembly
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames

namespace SemanticMatrix
open StageConstruction MatrixNames
abbrev Raw (k A : Type*) [CommRing k] := MonoidAlgebra k (FreeMonoid A)

attribute [local instance] WordCalculus.rawMatrixAction

end SemanticMatrix
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ThreeCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding
noncomputable section

namespace DelimiterCode
variable {A S T : Type*}

def map (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) : DelimiterCode A T where
  start := f C.start
  stop := f C.stop
  distinct := fun h => C.distinct (hf h)
  body a := (C.body a).map f
  start_avoids a := by
    simpa only [List.mem_map, hf.eq_iff, exists_eq_right] using C.start_avoids a
  stop_avoids a := by
    simpa only [List.mem_map, hf.eq_iff, exists_eq_right] using C.stop_avoids a
  injective := fun _ _ h => C.injective (List.map_injective_iff.mpr hf h)

@[simp] theorem map_block (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) (a : A) :
    (C.map f hf).block a = (C.block a).map f := by simp [map,block]

@[simp] theorem map_encode (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) (w : List A) :
    (C.map f hf).encode w = (C.encode w).map f := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [encode_cons,map_block,ih,List.map_append]

theorem map_alphabet (C : DelimiterCode A S) (f : S → T) (hf : Function.Injective f) :
    (C.map f hf).alphabet ⊆ Set.range f := by
  intro t ht
  rcases ht with h | h | ⟨a,ha⟩
  · exact ⟨C.start,h.symm⟩
  · exact ⟨C.stop,h.symm⟩
  · obtain ⟨s,_,hs⟩ := List.mem_map.mp ha
    exact ⟨s,hs⟩

end DelimiterCode

end
end SimpleFInftyOvergroups.ContextualEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TwoEnlargements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SourceEnlargement

namespace Saturation
variable {W X Y : Type} [Group W] [MulAction W Y] (t : X → Y)

def carrier : Set Y := {y | ∃ (w : W) (x : X), w • t x = y}

instance action : MulAction W (carrier (W := W) t) where
  smul w y := ⟨w • y.val, by
    obtain ⟨v, x, hx⟩ := y.property
    exact ⟨w * v, x, by rw [mul_smul, hx]⟩⟩
  one_smul y := Subtype.ext (one_smul _ _)
  mul_smul w v y := Subtype.ext (mul_smul _ _ _)

end Saturation

end SourceEnlargement
end

end OAI
end


