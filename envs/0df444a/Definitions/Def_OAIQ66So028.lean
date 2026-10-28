-- Prove2me | Definitions.Def_OAIQ66So028
-- name    : OAIQ66So028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:36:35.058652+00:00
-- url     : https://prove2.me/theorems/a9fbcaa4-bb01-4558-af6f-a362e4d6d85d
-- title:
--   Definitions bundle OAIQ66So028 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 133 declarations of OpenAI's Lean: 62 definitions, 1 inductive type or structure, 2 instances and 68 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.BoundedEncoding.CompilerCalculus.calculus`, `OAI.SimpleFInftyOvergroups.CommonCompiler.FiniteLetter`, `OAI.SimpleFInftyOvergroups.CommonCompiler.Letter`, `OAI.SimpleFInftyOvergroups.CommonCompiler.Mon`, `OAI.SimpleFInftyOvergroups.CommonCompiler.calculus`, `OAI.SimpleFInftyOvergroups.CommonCompiler.clamp`, `OAI.SimpleFInftyOvergroups.CommonCompiler.compilerSemanticsMonoidWithZero`, `OAI.SimpleFInftyOvergroups.CommonCompiler.compilerSemanticsSectorOrder`, `OAI.SimpleFInftyOvergroups.CommonCompiler.evaluation`, `OAI.SimpleFInftyOvergroups.CommonCompiler.includeLetter`, `OAI.SimpleFInftyOvergroups.CommonCompiler.includeWord`, `OAI.SimpleFInftyOvergroups.CommonCompiler.normal`, `OAI.SimpleFInftyOvergroups.CommonCompiler.normalPresentation`, `OAI.SimpleFInftyOvergroups.CommonCompiler.retractLetter`, `OAI.SimpleFInftyOvergroups.CommonCompiler.retractWord`, `OAI.SimpleFInftyOvergroups.CommonCompiler.service`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.Acting`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.Family`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.Keys`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.Points`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.Symbols`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.Syntax`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.code`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.cost`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.family`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableActing`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableKeys`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodablePoints`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableSymbols`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableSyntax`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.normal`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.ops`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.search`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.tables`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.terminalAlphabet`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.terminalMachine`, `OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.test`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.interpretation`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Double.interpret₁`, `OAI.SimpleFInftyOvergroups.EffectiveNames.Enlargement.groupLabel` and 23 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_SteinbergSixThree`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/SteinbergSixThree.lean), [`SimpleOvergroups_CommonCompiler`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/CommonCompiler.lean), [`SimpleOvergroups_CompilerSemantics`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/CompilerSemantics.lean), [`SimpleOvergroups_ContextualCompiler`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/ContextualCompiler.lean), [`SimpleOvergroups_DoubleEffective`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/DoubleEffective.lean), [`SimpleOvergroups_EnlargementEffective`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/EnlargementEffective.lean), [`SimpleOvergroups_EnlargementNames`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/EnlargementNames.lean), [`SimpleOvergroups_SemanticDouble`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SemanticDouble.lean), [`SimpleOvergroups_SemanticEnlargements`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SemanticEnlargements.lean), [`SimpleOvergroups_SourceModel`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SourceModel.lean), [`SimpleOvergroups_TruncatedAlgebra`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/TruncatedAlgebra.lean).
--
--   **Imports.** It imports the bundles `OAIQ66So024`, `OAIQ66So025` and `OAIQ66So026` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So030` and `OAIQ66So031`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So024
import Definitions.Def_OAIQ66So025
import Definitions.Def_OAIQ66So026

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
variable {R : Type*} [Ring R]

noncomputable def descended (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ) :
    NoncommElementary.elementary (R:=R) (n:=Fin 6) →* Group (Fin 6) R :=
  (pi (R:=R) (n:=Fin 6)).liftOfSurjective pi_surjective
    ⟨map φ, fun w hw => binary_kernel_annihilation φ D w hw⟩

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_TruncatedAlgebra
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableLetter _root_.OAI.FiniteAlgebraicEnvelopes.Compiler.Path.instPrimcodableShape _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.BoundedEncoding
noncomputable section
open scoped Classical

namespace CompilerCalculus
open FiniteAlgebraicEnvelopes.Compiler
variable {S Γ Q : Type*}
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  [DecidableEq S] [DecidableEq Γ] [DecidableEq Q]
  [Fintype S] [Fintype Γ] [Fintype Q] [LinearOrder (Control.Sector S Γ Q)]

def calculus
    (decode : ∀ g a, A.output g = some a → g = A.input a)
    {f : List S → Part (List S)} {m : ℕ} (budget : PartialBudget f m)
    (realizes : Word.Realizes A M f) :
    WordCalculus (FreeMonoid (Word.Letter S Γ Q)) m where
  grade w := Word.grade w.toList
  grade_one := rfl
  grade_mul a b := Word.grade_append a.toList b.toList
  omega := FreeMonoid.ofList [.zero]
  grade_omega := rfl
  omega_ne_one := by simp
  normal w := FreeMonoid.ofList (Word.normal A M (fun w => partValue (f w)) w.toList)
  normal_one := by simp
  normal_omega := by simp
  nonincreasing w hw := Word.normal_grade A M budget.totalize _ hw
  idempotent w hw := congrArg FreeMonoid.ofList
    (Word.normal_idempotent A M decode budget.totalize (realizes.computesAt A M budget) _ hw)
  context h a b hu hv := congrArg FreeMonoid.ofList
    (Word.normal_context A M decode budget.totalize (realizes.computesAt A M budget)
      (congrArg FreeMonoid.toList h) a.toList b.toList hu hv)
  absorbs a b := by
    apply congrArg FreeMonoid.ofList
    simpa using Word.normal_contains_omega A M (fun w => partValue (f w)) a.toList b.toList

end CompilerCalculus
end
end SimpleFInftyOvergroups.BoundedEncoding

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_CommonCompiler
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.CommonCompiler
noncomputable section
open FiniteAlgebraicEnvelopes
open Compiler MachineRealization
open scoped Classical Compiler.HeadCodec

variable {T Γ Q : Type*}
abbrev Letter (T Γ Q : Type*) := Compiler.Word.Letter T (Bool × Γ) (ParameterCode.Control Q)
abbrev FiniteLetter (T Γ Q : Type*) (n : ℕ) :=
  Compiler.Word.Letter T (Bool × Γ) (ParameterMachine.State Q n)

abbrev includeLetter (n : ℕ) : FiniteLetter T Γ Q n → Letter T Γ Q :=
  Word.letterMap (ParameterCode.encode n)

theorem includeLetter_injective (n : ℕ) :
    Function.Injective (includeLetter (T:=T) (Γ:=Γ) (Q:=Q) n) :=
  Word.letterMap_injective _ (ParameterCode.encode_injective n)

def retractLetter (n : ℕ) (a : Letter T Γ Q) : FiniteLetter T Γ Q n :=
  if h : ∃ b, includeLetter n b = a then h.choose else .zero

@[simp] theorem retract_include (n : ℕ) (a : FiniteLetter T Γ Q n) :
    retractLetter n (includeLetter n a) = a := by
  have h : ∃ b, includeLetter n b = includeLetter n a := ⟨a,rfl⟩
  rw [retractLetter, dite_eq_left h]
  exact includeLetter_injective n h.choose_spec

theorem grade_include_letter (n : ℕ) (a : FiniteLetter T Γ Q n) :
    Path.letterGrade Word.gradeCell (includeLetter n a) =
      Path.letterGrade Word.gradeCell a := by
  cases a <;> rfl

theorem grade_include (n : ℕ) (w : List (FiniteLetter T Γ Q n)) :
    Word.grade (w.map (includeLetter n)) = Word.grade w := by
  simp only [Word.grade, Path.grade, List.map_map]
  congr 2
  funext a
  exact grade_include_letter n a

theorem grade_retract_letter (n : ℕ) (a : Letter T Γ Q) :
    Path.letterGrade Word.gradeCell (retractLetter n a) ≤
      Path.letterGrade Word.gradeCell a := by
  rw [retractLetter]
  split
  · rename_i h
    exact le_of_eq ((grade_include_letter n h.choose).symm.trans
      (congrArg (Path.letterGrade Word.gradeCell) h.choose_spec))
  · exact Nat.zero_le _

theorem grade_retract (n : ℕ) (w : List (Letter T Γ Q)) :
    Word.grade (w.map (retractLetter n)) ≤ Word.grade w := by
  induction w with
  | nil => exact le_refl 0
  | cons a w ih => exact Nat.add_le_add (grade_retract_letter n a) ih

abbrev includeWord (n : ℕ) : FreeMonoid (FiniteLetter T Γ Q n) →* FreeMonoid (Letter T Γ Q) :=
  FreeMonoid.map (includeLetter n)
abbrev retractWord (n : ℕ) : FreeMonoid (Letter T Γ Q) →* FreeMonoid (FiniteLetter T Γ Q n) :=
  FreeMonoid.map (retractLetter n)

@[simp] theorem retract_include_word (n : ℕ) (w : FreeMonoid (FiniteLetter T Γ Q n)) :
    retractWord n (includeWord n w) = w := by
  apply FreeMonoid.toList.injective
  simp only [includeWord,retractWord,FreeMonoid.toList_map,List.map_map,
    Function.comp_def,retract_include]
  exact List.map_id _

variable [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]

def clamp (n : ℕ) (a : Letter T Γ Q) : Letter T Γ Q :=
  if a ∈ ParameterCode.letters n then a else .zero

omit [Primcodable Q] in
@[simp] theorem include_retract [Primcodable Q] (n : ℕ) (a : Letter T Γ Q) :
    includeLetter n (retractLetter n a) = clamp n a := by
  by_cases h : ∃ b, includeLetter n b = a
  · rw [retractLetter,dite_eq_left h,clamp,ite_eq_left ((ParameterCode.mem_letters_iff n a).mpr h)]
    exact h.choose_spec
  · rw [retractLetter,dite_eq_right h,clamp,ite_eq_right (fun ha => h ((ParameterCode.mem_letters_iff n a).mp ha))]
    rfl

theorem clamp_words (n : ℕ) (w : List (Letter T Γ Q)) :
    (w.map (retractLetter n)).map (includeLetter n) = w.map (clamp n) := by
  simp only [List.map_map,Function.comp_def,include_retract]

variable [Primcodable Γ] [Primcodable T]

omit [Primcodable Γ] [Primcodable T] in
theorem primrec_clamp [Primcodable Γ] [Primcodable T] :
    Primrec₂ (clamp (T:=T) (Γ:=Γ) (Q:=Q)) := by
  exact (Primrec.ite
    (Bootstrap.Selectors.primrec_mem.comp Primrec.snd
      (ParameterCode.primrec_letters.comp Primrec.fst))
    Primrec.snd (Primrec.const (Path.Letter.zero : Letter T Γ Q))).of_eq (by
      intro x
      simp only [clamp]
      split <;> simp_all)

omit [Fintype Q] [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
    [Primcodable Γ] [Primcodable T] in
theorem primrec_letterGrade [Fintype Q] [DecidableEq T] [DecidableEq Γ] [DecidableEq Q]
    [Primcodable Γ] [Primcodable T] :
    Primrec (Path.letterGrade Word.gradeCell : Letter T Γ Q → ℕ) := by
  exact ((Effect.primrec_sumElim
    (Primrec.dom_finite (fun i : Fin 3 => if i = 0 then 0 else 1))
    (Effect.primrec_sumElim (Primrec.dom_finite Word.gradeCell)
      (Effect.primrec_sumElim (Primrec.dom_finite Word.gradeCell) (Primrec.const 1)))).comp
        HeadCodec.primrec_pathCode).of_eq (fun a => by cases a <;> rfl)

theorem primrec_grade : Primrec (Word.grade (S:=T) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q)) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (primrec_letterGrade.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq (by
        intro w
        induction w with
        | nil => rfl
        | cons a w ih => simpa only [id_eq, List.foldr_cons, Word.grade, Path.grade_cons] using
          (congrArg (Path.letterGrade Word.gradeCell a + ·) ih))

variable {S : Type*} (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  (p : S) (B : Simulator.Alphabet T (Bool × Γ))

def service (f : ℕ × List T → Part (List T)) (x : ℕ × List (Letter T Γ Q)) :
    Part (List (Letter T Γ Q)) :=
  ParameterCode.codedNormal A M p B f (x.1, x.2.map (clamp x.1))

theorem partrec_service {f : ℕ × List T → Part (List T)} (hf : Partrec f) :
    Partrec (service A M p B f) := by
  exact (ParameterCode.partrec_codedNormal A M p B hf).comp
    (Primrec.fst.pair (Primrec.list_map Primrec.snd
      (primrec_clamp.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)).to_comp

def calculus (n : ℕ)
    (decode : ∀ g a, B.output g = some a → g = B.input a)
    {f : ℕ × List T → Part (List T)} {m : ℕ}
    (budget : PartialBudget (fun w => f (n,w)) m)
    (realizes : Word.Realizes B (ParameterMachine.machine A M p n) (fun w => f (n,w))) :
    BoundedEncoding.WordCalculus (FreeMonoid (Letter T Γ Q)) m := by
  letI := ParameterCode.finiteOrder (T:=T) (Γ:=Γ) (Q:=Q) n
  let C := BoundedEncoding.CompilerCalculus.calculus B (ParameterMachine.machine A M p n)
    decode budget realizes
  exact C.retract (retractWord n) (includeWord n) (retract_include_word n)
    (fun w => Word.grade w.toList) rfl (fun _ _ => Word.grade_append _ _)
    (fun w => grade_include n w.toList) (fun w => grade_retract n w.toList)

omit [Primcodable Γ] [Primcodable T] in
theorem service_full [Primcodable Γ] [Primcodable T] (n : ℕ)
    (decode : ∀ g a, B.output g = some a → g = B.input a)
    {f : ℕ × List T → Part (List T)} {m : ℕ}
    (budget : PartialBudget (fun w => f (n,w)) m)
    (realizes : Word.Realizes B (ParameterMachine.machine A M p n) (fun w => f (n,w)))
    (w : List (Letter T Γ Q)) (hw : Word.grade w ≤ m) :
    ((calculus A M p B n decode budget realizes).normal (FreeMonoid.ofList w)).toList ∈
      service A M p B f (n,w) := by
  let := ParameterCode.finiteOrder (T:=T) (Γ:=Γ) (Q:=Q) n
  rw [service,← clamp_words,ParameterCode.codedNormal_map,
    Word.partialNormal_eq_some B (ParameterMachine.machine A M p n) budget _
      ((grade_retract n w).trans hw)]
  exact (Part.mem_map_iff _).mpr ⟨_, Part.mem_some _, rfl⟩

end
end SimpleFInftyOvergroups.CommonCompiler

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_CompilerSemantics
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.CommonCompiler
noncomputable section
open FiniteAlgebraicEnvelopes Compiler MachineRealization
open SemanticEncoding
open scoped Classical Compiler.HeadCodec

variable {S T Γ Q : Type*} [Fintype T] [Fintype Γ] [Fintype Q]
  [DecidableEq T] [DecidableEq Γ] [DecidableEq Q] [Primcodable Q]
variable (A : Simulator.Alphabet S Γ) (M : Simulator.Machine Q Γ)
  (p : S) (B : Simulator.Alphabet T (Bool × Γ)) (index : ℕ)

local instance compilerSemanticsSectorOrder :
    LinearOrder (Control.Sector T (Bool × Γ) (ParameterMachine.State Q index)) :=
  ParameterCode.finiteOrder index

abbrev Mon := Word.Presentation B (ParameterMachine.machine A M p index)

local instance compilerSemanticsMonoidWithZero : MonoidWithZero (Mon A M p B index) :=
  Word.monoidWithZero B (ParameterMachine.machine A M p index)

variable (decode : ∀ g a, B.output g = some a → g = B.input a)
  {f : ℕ × List T → Part (List T)}
  (budget : ∀ m, PartialBudget (fun w => f (index,w)) m)
  (realizes : Word.Realizes B (ParameterMachine.machine A M p index) (fun w => f (index,w)))

def evaluation : FreeMonoid (Letter T Γ Q) →* Mon A M p B index :=
  (PresentedMonoid.mk (Word.Rel B (ParameterMachine.machine A M p index))).comp
    (retractWord index)

omit [Fintype T] [Fintype Γ] [Fintype Q] [DecidableEq Q] [Primcodable Q] in
 theorem evaluation_surjective : Function.Surjective (evaluation A M p B index) := by
  intro h
  obtain ⟨w,hw⟩ := PresentedMonoid.surjective_mk h
  refine ⟨includeWord index w, ?_⟩
  simpa only [evaluation, MonoidHom.comp_apply, retract_include_word] using hw

omit [Fintype T] [Fintype Γ] [Fintype Q] [DecidableEq T] [DecidableEq Γ]
  [DecidableEq Q] [Primcodable Q] in
 theorem includeWord_injective : Function.Injective (includeWord (T:=T) (Γ:=Γ) (Q:=Q) index) :=
  Function.LeftInverse.injective (retract_include_word index)

def normal (w : FreeMonoid (Letter T Γ Q)) : FreeMonoid (Letter T Γ Q) :=
  (calculus A M p B index decode (budget 0) realizes).normal w

 theorem evaluation_iff (u v : FreeMonoid (Letter T Γ Q)) :
    evaluation A M p B index u = evaluation A M p B index v ↔
      normal A M p B index decode budget realizes u = normal A M p B index decode budget realizes v := by
  change _ ↔ includeWord index _ = includeWord index _
  rw [(includeWord_injective (T:=T) (Γ:=Γ) (Q:=Q) index).eq_iff]
  change Word.present B (ParameterMachine.machine A M p index) (retractWord index u).toList =
    Word.present B (ParameterMachine.machine A M p index) (retractWord index v).toList ↔ _
  exact Word.present_eq_iff_normal B (ParameterMachine.machine A M p index) decode
    (fun m => (budget m).totalize) (fun m => realizes.computesAt _ _ (budget m)) _ _

 theorem normal_idempotent (w : FreeMonoid (Letter T Γ Q)) :
    normal A M p B index decode budget realizes (normal A M p B index decode budget realizes w) =
      normal A M p B index decode budget realizes w := by
  exact (calculus A M p B index decode (budget (Word.grade w.toList)) realizes).idempotent w le_rfl

def normalPresentation : NormalPresentation (FreeMonoid (Letter T Γ Q)) (Mon A M p B index) where
  q := evaluation A M p B index
  surjective := evaluation_surjective A M p B index
  normal := normal A M p B index decode budget realizes
  omega := FreeMonoid.ofList [.zero]
  zero := by
    change Word.present B (ParameterMachine.machine A M p index)
      [retractLetter index .zero] = Word.present B (ParameterMachine.machine A M p index) [.zero]
    rw [show retractLetter index (.zero : Letter T Γ Q) = .zero from retract_include index .zero]
  complete := evaluation_iff A M p B index decode budget realizes
  idempotent := normal_idempotent A M p B index decode budget realizes
  fixesZero := (calculus A M p B index decode (budget 0) realizes).normal_omega

 include decode budget realizes in
 theorem zero_ne_one : (0 : Mon A M p B index) ≠ 1 := by
  intro h
  let P := normalPresentation A M p B index decode budget realizes
  have he := (P.complete P.omega 1).mp (by rw [P.zero,map_one]; exact h)
  have hone : P.normal 1 = 1 :=
    (calculus A M p B index decode (budget 0) realizes).normal_one
  rw [P.fixesZero,hone] at he
  have he' := congrArg FreeMonoid.toList he
  change [.zero] = ([] : List (Letter T Γ Q)) at he'
  contradiction

 include decode budget realizes in
 theorem nontrivial : Nontrivial (Mon A M p B index) :=
  nontrivial_of_ne _ _ (zero_ne_one A M p B index decode budget realizes)

end
end SimpleFInftyOvergroups.CommonCompiler

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementNames
attribute [-instance] _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.orbitSMul _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding NamedAction
noncomputable section
open scoped Classical
variable {G X P k : Type*} [CommRing k] (N : Operations G X)

variable (e : P → Coeff.Name k)

 theorem rootArray_bound (a : P × G) : ∀ b ∈ rootArray N e a, N.gcost b.2 ≤ N.gcost a.2 := by
  intro b hb
  simp only [rootArray,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl
  · simp [N.cost_one]
  · exact le_rfl

 theorem array_bound (w : Word P G) : ∀ b ∈ array N e w, N.gcost b.2 ≤ gcost N w := by
  induction w with
  | nil => intro b hb; simp only [array,List.foldr_nil,List.mem_singleton] at hb
           simp [hb,N.cost_one]
  | cons a w ih =>
    exact Array.product_bound Coeff.mul N.mul N.gcost N.gcost N.cost_mul
      (rootArray_bound N e a) ih

 theorem pointArray_bound (x : Point P G X) : ∀ b ∈ pointArray N e x, N.xcost b.2 ≤ xcost N x := by
  apply Array.product_bound Coeff.mul N.act N.gcost N.xcost N.cost_act (array_bound N e x.1)
  intro b hb
  simp only [List.mem_singleton] at hb
  simp [hb]

variable {V Y K L : Type*} [Group V] [MulAction V Y] [Nonempty Y] {m : ℕ}
  {C : ActionCalculus V Y K L m} (I : Interpretation N C)
  (he : ∀ p, Coeff.value (e p) * Coeff.value (e p) = Coeff.value (e p))

 theorem group_mem (w : Word P G) :
    groupValue N e I he w ∈ (C.enlargement (D k)).group.ball (gcost N w) := by
  induction w with
  | nil => exact (C.enlargement (D k)).one_mem _
  | cons a w ih =>
    apply (C.enlargement (D k)).mul_mem _ ih
    have hh := C.unitMap_mem (D k) (Coeff.value (e a.1)) (he a.1) (I.group a.2).mem
    simpa only [I.group_cost,rootValue] using hh

 theorem point_mem (x : Point P G X) :
    pointValue N e I he x ∈ (C.enlargement (D k)).point.ball (xcost N x) := by
  apply (C.enlargement (D k)).smul_mem (group_mem N e I he x.1)
  have hh := C.basis_mem (D k) (I.point x.2).mem
  simpa only [I.point_cost] using hh

end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_EnlargementEffective
attribute [-instance] _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.orbitSMul _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Enlargement
open BoundedEncoding NamedAction
open BinaryPrefixOperators.Arithmetic
noncomputable section
open scoped Classical
variable {G X P k : Type*} [CommRing k] (N : Operations G X)
  (e : P → Coeff.Name k)
variable [Primcodable k]

variable {V Y K L : Type*} [Group V] [MulAction V Y] [Nonempty Y] {m : ℕ}
  (C : ActionCalculus V Y K L m) [Primcodable K] [Primcodable L]

variable {C} (I : Interpretation N C)
  (he : ∀ p, Coeff.value (e p) * Coeff.value (e p) = Coeff.value (e p))

def groupLabel (w : Word P G) : (calculus (k:=k) C).GLabel :=
  ⟨groupValue N e I he w,gcost N w,group_mem N e I he w⟩
def pointLabel (x : Point P G X) : (calculus (k:=k) C).XLabel :=
  ⟨pointValue N e I he x,xcost N x,point_mem N e I he x⟩

def interpretation : Interpretation (operations (P:=P) N) (calculus (k:=k) C) where
  group := groupLabel N e I he
  point := pointLabel N e I he
  group_cost w := rfl
  point_cost x := rfl
  one := WithBound.ext' (groupValue_nil N e I he) rfl
  mul a b := WithBound.ext' (groupValue_append N e I he a b) (gcost_append N a b)
  inv w := WithBound.ext' (groupValue_inverse N e I he w) (gcost_inverse N w)
  act g x := WithBound.ext' (pointValue_act N e I he g x)
    (by change gcost N (g++x.1) + N.xcost x.2 = gcost N g + xcost N x
        simp [xcost,Nat.add_assoc])

variable [Primcodable G] [Primcodable X]

omit [Primcodable G] [Primcodable X] in
 theorem partialGroupKey_full (f : G → Part K) (w : Word P G) {d : ℕ}
    (hw : gcost N w ≤ d) (hf : ∀ g, N.gcost g ≤ d → I.gkey g ∈ f g) :
    (interpretation N e I he).gkey w ∈ partialGroupKey N e f w := by
  have h (u : Word P G) (hu : gcost N u ≤ d) :=
    Array.collectedKey_full Coeff.value Lists.value_surjective f
      (fun g => (I.group g).val) C.group.key (array N e u)
      (fun a ha => hf a.2 ((array_bound N e u a ha).trans hu))
  have h' (u : Word P G) (hu : gcost N u ≤ d) :
      arrayKey (C.group.algebraCollect (D k) (groupValue N e I he u).val) ∈
        Array.collectedKey Coeff.value f (array N e u) := by
    have hh := h u hu
    have hv := congrArg MonoidAlgebra.coeff (value_array N e I he u)
    change Array.value Coeff.value (fun g => (I.group g).val) (array N e u) = _ at hv
    rw [hv] at hh
    exact hh
  change (arrayKey (C.group.algebraCollect (D k) (groupValue N e I he w).val),
    arrayKey (C.group.algebraCollect (D k) (groupValue N e I he w).inv)) ∈ _
  exact Part.mem_bind_iff.mpr ⟨_,h' w hw,Part.mem_map _ (by
    have hh := h' (inverse N w) (by simpa using hw)
    simpa only [groupValue_inverse, ← Units.inv_eq_val_inv] using hh)⟩

omit [Primcodable G] [Primcodable X] in
 theorem partialPointKey_full (f : X → Part L) (x : Point P G X) {d : ℕ}
    (hx : xcost N x ≤ d) (hf : ∀ y, N.xcost y ≤ d → I.xkey y ∈ f y) :
    (interpretation N e I he).xkey x ∈ partialPointKey N e f x := by
  have h := Array.collectedKey_full Coeff.value Lists.value_surjective f
    (fun y => (I.point y).val) C.point.key (pointArray N e x)
    (fun a ha => hf a.2 ((pointArray_bound N e x a ha).trans hx))
  rw [value_pointArray N e I he] at h
  exact h

variable [Primcodable P] [Finite P] [Finite k]

 theorem computable_array_eq {J : Type*} [Primcodable J] : ComputablePred
    (fun p : Array.Name (Coeff.Name k) J × Array.Name (Coeff.Name k) J =>
      Array.value Coeff.value id p.1 = Array.value Coeff.value id p.2) := by
  apply Array.computable_value_eq Coeff.value id [] (·++·) Primrec.list_append
    (show ComputablePred (fun p : J × J => p.1 = p.2) from Primrec.eq.computablePred)
    Lists.computable_value_eq
  · exact Lists.value_nil
  · exact Lists.value_append

omit [Primcodable X] [Finite P] in
 theorem primrec_inverse (hi : Primrec N.inv) : Primrec (inverse (P:=P) N) :=
  Primrec.list_map Primrec.list_reverse
    ((Primrec.fst.comp Primrec.snd).pair (hi.comp (Primrec.snd.comp Primrec.snd))).to₂

omit [Finite P] in
 theorem primrec_plan (hi : Primrec N.inv) : Primrec₂ ((operations (P:=P) N).plan) :=
  (operations N).primrec_plan Primrec.list_append (primrec_inverse N hi) (primrec_act N)

omit [Primcodable X] in
 theorem primrec_rootArray : Primrec (rootArray N e) := by
  have hc : Primrec (Coeff.complement (k:=k)) :=
    Primrec.list_append.comp (Primrec.const Coeff.one) Lists.primrec_negate
  have he : Primrec e := Primrec.dom_finite e
  exact Primrec.list_cons.comp
    ((hc.comp (he.comp Primrec.fst)).pair (Primrec.const N.one))
    (Primrec.list_cons.comp ((he.comp Primrec.fst).pair Primrec.snd) (Primrec.const []))

omit [Primcodable X] in
 theorem primrec_array (hm : Primrec₂ N.mul) : Primrec (array N e) :=
  Primrec.list_foldr Primrec.id (Primrec.const [(Coeff.one,N.one)])
    ((Array.primrec_product Lists.primrec_product hm).comp
      ((primrec_rootArray N e).comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

 theorem primrec_pointArray (hm : Primrec₂ N.mul) (hx : Primrec₂ N.act) :
    Primrec (pointArray N e) :=
  (Array.primrec_product Lists.primrec_product hx).comp
    ((primrec_array N e hm).comp Primrec.fst)
    (Primrec.list_cons.comp ((Primrec.const Coeff.one).pair Primrec.snd) (Primrec.const []))

omit [Primcodable X] [Finite P] in
 theorem primrec_gcost (hc : Primrec N.gcost) : Primrec (gcost (P:=P) N) := by
  have hs : Primrec (fun l : List ℕ => l.sum) :=
    (Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun _ => rfl)
  exact hs.comp (Primrec.list_map Primrec.id (hc.comp (Primrec.snd.comp Primrec.snd)).to₂)

omit [Finite P] in
 theorem primrec_xcost (hg : Primrec N.gcost) (hx : Primrec N.xcost) :
    Primrec (xcost (P:=P) N) :=
  Primrec.nat_add.comp ((primrec_gcost N hg).comp Primrec.fst) (hx.comp Primrec.snd)

variable {Param : Type*} [Primcodable Param]
variable {fg : Param → G → Part K} {fx : Param → X → Part L}

omit [Primcodable X] in
 theorem partrec_partialGroupKey (hm : Primrec₂ N.mul) (hi : Primrec N.inv)
    (hf : Partrec₂ fg) : Partrec₂ (fun p : Param => partialGroupKey N e (fg p)) := by
  have hp : Partrec (fun p : Param × Word P G =>
      Array.collectedKey Coeff.value (fg p.1) (array N e p.2)) :=
    (Array.partrec_collectedKey Coeff.value computable_array_eq hf).comp Computable.fst
      ((primrec_array N e hm).to_comp.comp Computable.snd)
  apply hp.bind
  have hq : Partrec (fun p : (Param × Word P G) × ℕ =>
      Array.collectedKey Coeff.value (fg p.1.1) (array N e (inverse N p.1.2))) :=
    (Array.partrec_collectedKey Coeff.value computable_array_eq hf).comp (Computable.fst.comp Computable.fst)
      ((primrec_array N e hm).to_comp.comp ((primrec_inverse N hi).to_comp.comp
        (Computable.snd.comp Computable.fst)))
  exact (hq.map ((Computable.snd.comp Computable.fst).pair Computable.snd).to₂).to₂

 theorem partrec_partialPointKey (hm : Primrec₂ N.mul) (hx : Primrec₂ N.act)
    (hf : Partrec₂ fx) : Partrec₂ (fun p : Param => partialPointKey N e (fx p)) :=
  (Array.partrec_collectedKey Coeff.value computable_array_eq hf).comp Computable.fst
    ((primrec_pointArray N e hm hx).to_comp.comp Computable.snd)


end
end SimpleFInftyOvergroups.EffectiveNames.Enlargement

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_DoubleEffective
attribute [-instance] _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.orbitSMul _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Double
open BoundedEncoding NamedAction
noncomputable section
open scoped Classical

variable {A k₀ k₁ k₂ P₁ P₂ : Type*}
  [CommRing k₀] [CommRing k₁] [CommRing k₂]
  [Primcodable A] [Primcodable k₀] [Primcodable k₁] [Primcodable k₂]
  [Finite k₀] [Finite k₁] [Finite k₂]
  [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂]
  {n : ℕ}

variable (e₁ : P₁ → Enlargement.Coeff.Name k₁) (e₂ : P₂ → Enlargement.Coeff.Name k₂)
variable (grade : List A → ℕ) (omega : List A) (f : List A → Part (List A))

variable {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
attribute [local instance] WordCalculus.rawMatrixAction

variable (he₁ : ∀ p, Enlargement.Coeff.value (e₁ p) * Enlargement.Coeff.value (e₁ p) =
    Enlargement.Coeff.value (e₁ p))
  (he₂ : ∀ p, Enlargement.Coeff.value (e₂ p) * Enlargement.Coeff.value (e₂ p) =
    Enlargement.Coeff.value (e₂ p))

abbrev interpret₁ := Enlargement.interpretation (base (MatrixWords.grade C)) e₁
  (MatrixWords.interpretation (k:=k₀) (n:=n) C) he₁

abbrev interpretation := Enlargement.interpretation (first (MatrixWords.grade C)) e₂
  (interpret₁ (k₀:=k₀) (n:=n) e₁ C he₁) he₂

omit [Finite k₁] [Finite k₂] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂] in
 theorem partialGroupKey_full {d : ℕ} (w : G₂ P₁ P₂ k₀ A n)
    (hw : (operations (MatrixWords.grade C)).gcost w ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d →
      (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation e₁ e₂ C he₁ he₂).gkey w ∈
      partialGroupKey e₁ e₂ (MatrixWords.grade C) C.omega.toList f w := by
  apply Enlargement.partialGroupKey_full _ _ _ _ _ _ hw
  intro g hg
  apply Enlargement.partialGroupKey_full _ _ _ _ _ _ hg
  intro h hh
  exact MatrixWords.partialGroupKey_full C f h hh hf

omit [Finite k₁] [Finite k₂] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂] in
 theorem partialPointKey_full {d : ℕ} (x : X₂ P₁ P₂ k₀ A n)
    (hx : (operations (MatrixWords.grade C)).xcost x ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d →
      (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation e₁ e₂ C he₁ he₂).xkey x ∈
      partialPointKey e₁ e₂ (MatrixWords.grade C) C.omega.toList f x := by
  apply Enlargement.partialPointKey_full _ _ _ _ _ _ hx
  intro y hy
  apply Enlargement.partialPointKey_full _ _ _ _ _ _ hy
  intro z hz
  exact MatrixWords.partialPointKey_full C f z hz hf

omit [Finite k₁] [Finite k₂] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂] in
 theorem test_full {d : ℕ} (w : List (Letter (G₂ P₁ P₂ k₀ A n) (X₂ P₁ P₂ k₀ A n)))
    (hw : (operations (MatrixWords.grade C)).wordCost w ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d →
      (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (operations (MatrixWords.grade C)).totalTest
      (interpretation e₁ e₂ C he₁ he₂).gkey (interpretation e₁ e₂ C he₁ he₂).xkey w ∈
      test e₁ e₂ (MatrixWords.grade C) C.omega.toList f w := by
  exact Operations.test_full _ _ _ _ _
    (fun g hg => partialGroupKey_full e₁ e₂ f C he₁ he₂ g hg hf)
    (fun x hx => partialPointKey_full e₁ e₂ f C he₁ he₂ x hx hf) w hw


omit [Finite k₀] in
 theorem primrec_act_base : Primrec₂ ((base (k₀:=k₀) (n:=n) grade).act) :=
  (Primrec.list_append.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    (Primrec.snd.comp Primrec.snd)
omit [Finite P₁] in
 theorem primrec_inv_first : Primrec ((first (P₁:=P₁) (k₀:=k₀) (n:=n) grade).inv) :=
  Enlargement.primrec_inverse _ (primrec_inv_base grade)
attribute [local instance] OAI.SimpleFInftyOvergroups.EffectiveNames.Double.instPrimcodableG₂
attribute [local instance] OAI.SimpleFInftyOvergroups.EffectiveNames.Double.instPrimcodableX₂
omit [Finite P₁] [Finite P₂] in
 theorem primrec_plan : Primrec₂ ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).plan) :=
  Enlargement.primrec_plan _ (primrec_inv_first grade)

variable {Param : Type*} [Primcodable Param] {F : Param → List A → Part (List A)}

 theorem partrec_partialGroupKey (hF : Partrec₂ F) :
    Partrec₂ (fun p : Param => partialGroupKey (k₀:=k₀) (n:=n) e₁ e₂ grade omega (F p)) :=
  Enlargement.partrec_partialGroupKey _ e₂ Primrec.list_append (primrec_inv_first grade)
    (Enlargement.partrec_partialGroupKey _ e₁ Primrec.list_append (primrec_inv_base grade)
      (MatrixWords.partrec_partialGroupKey omega hF))

 theorem partrec_partialPointKey (hF : Partrec₂ F) :
    Partrec₂ (fun p : Param => partialPointKey (k₀:=k₀) (n:=n) e₁ e₂ grade omega (F p)) :=
  Enlargement.partrec_partialPointKey _ e₂ Primrec.list_append (Enlargement.primrec_act _)
    (Enlargement.partrec_partialPointKey _ e₁ Primrec.list_append (primrec_act_base grade)
      (MatrixWords.partrec_partialPointKey omega hF))

 theorem partrec_test (hF : Partrec₂ F) :
    Partrec₂ (fun p : Param => test (k₀:=k₀) (n:=n) e₁ e₂ grade omega (F p)) :=
  Operations.partrec_test _ (primrec_plan grade).to_comp
    (partrec_partialGroupKey e₁ e₂ grade omega hF) (partrec_partialPointKey e₁ e₂ grade omega hF)

omit [Finite P₁] [Finite P₂] in
 theorem primrec_gcost (hg : Primrec grade) :
    Primrec ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).gcost) :=
  Enlargement.primrec_gcost _ (Enlargement.primrec_gcost _ (MatrixWords.primrec_gcost hg))

omit [Finite P₁] [Finite P₂] in
 theorem primrec_xcost (hg : Primrec grade) :
    Primrec ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).xcost) :=
  Enlargement.primrec_xcost _ (Enlargement.primrec_gcost _ (MatrixWords.primrec_gcost hg))
    (Enlargement.primrec_xcost _ (MatrixWords.primrec_gcost hg) (MatrixWords.primrec_xcost hg))

omit [Finite P₁] [Finite P₂] in
 theorem primrec_cost (hg : Primrec grade) :
    Primrec ((operations (P₁:=P₁) (P₂:=P₂) (k₀:=k₀) (n:=n) grade).letterCost) :=
  (operations grade).primrec_letterCost (primrec_gcost grade hg) (primrec_xcost grade hg)
end
end SimpleFInftyOvergroups.EffectiveNames.Double

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_ContextualCompiler
attribute [-instance] _root_.OAI.SourceEnlargement.Double.action₁ _root_.OAI.SourceEnlargement.Double.action₂ _root_.OAI.SourceEnlargement.Double.orbitAction _root_.OAI.SourceEnlargement.Double.orbitSMul _root_.OAI.SourceEnlargement.Double.smul₁ _root_.OAI.SourceEnlargement.Double.smul₂ _root_.OAI.SourceEnlargement.enlargedAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.ContextualEncoding.Source
noncomputable section
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open BoundedEncoding NamedAction
open scoped Classical Compiler.HeadCodec

abbrev terminalAlphabet {Γ : Type*} (A : Alphabet (Sigma ⊕ Unit) Γ) :=
  UniversalMachine.restrict (ParameterMachine.alphabet A)
abbrev terminalMachine {Γ Q : Type*} [DecidableEq Γ] (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ) (n : ℕ) :=
  ParameterMachine.machine A M (.inr ()) n

structure Family where
  Γ : Type
  Q : Type
  [finiteΓ : Fintype Γ]
  [finiteQ : Fintype Q]
  [decΓ : DecidableEq Γ]
  [decQ : DecidableEq Q]
  [codeΓ : Primcodable Γ]
  [codeQ : Primcodable Q]
  A : Alphabet (Sigma ⊕ Unit) Γ
  M : Machine Q Γ
  decode : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a
  realizes : ∀ n, Word.Realizes (terminalAlphabet A) (terminalMachine A M n) (raw n)

attribute [instance] Family.finiteΓ Family.finiteQ Family.decΓ Family.decQ Family.codeΓ Family.codeQ

local instance instDecidableRelSigmaRel_r1307bb_1 : DecidableRel rel := fun _ _ => inferInstanceAs (Decidable (_ < _))
theorem exists_family : Nonempty Family := by
  obtain ⟨Γ,Q,hΓ,hQ,dΓ,A,M,hd,hr⟩ := UniversalMachine.exists_parameter_machine partrec_raw
  let : Fintype Γ := hΓ
  let : Fintype Q := hQ
  let : DecidableEq Γ := dΓ
  let : Primcodable Γ := Effect.finitePrimcodable Γ
  let : Primcodable Q := Effect.finitePrimcodable Q
  exact ⟨⟨Γ,Q,A,M,UniversalMachine.restrict_decode (ParameterMachine.alphabet A)
    (ParameterMachine.output_decode A hd),hr⟩⟩

def family : Family := exists_family.some

variable {G : Type*} [Group G] {k : ℕ} (s : Fin k → G)
variable {Γ Q P₁ P₂ : Type} [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]
  [Primcodable Γ] [Primcodable Q] [Primcodable P₁] [Primcodable P₂] [Finite P₁] [Finite P₂]
variable (A : Alphabet (Sigma ⊕ Unit) Γ) (M : Machine Q Γ)

abbrev Syntax := CommonCompiler.Letter Sigma Γ Q
abbrev Acting := EffectiveNames.Double.G₂ P₁ P₂ (ZMod 2) (Syntax (Γ:=Γ) (Q:=Q)) 7
abbrev Points := EffectiveNames.Double.X₂ P₁ P₂ (ZMod 2) (Syntax (Γ:=Γ) (Q:=Q)) 7
local instance instPrimcodableSyntax : Primcodable (Syntax (Γ:=Γ) (Q:=Q)) := inferInstance
attribute [local instance] OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableZModOfNatNat_solutions
attribute [local instance] OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instPrimcodableZModOfNatNat_solutions_1
local instance instPrimcodableActing : Primcodable (Acting (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂)) := inferInstance
local instance instPrimcodablePoints : Primcodable (Points (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂)) := inferInstance

abbrev ops := EffectiveNames.Double.operations (P₁:=P₁) (P₂:=P₂) (k₀:=ZMod 2) (n:=7)
  (Word.grade (S:=Sigma) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q))

abbrev Symbols (k : ℕ) : Fin 3 → Type _
  | 0 => Fin k × Bool
  | 1 => ProductFamily.Letter (Syntax (Γ:=Γ) (Q:=Q))
  | 2 => NamedAction.Letter (Acting (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂))
      (Points (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂))

abbrev Keys (k : ℕ) : Fin 3 → Type _
  | 0 => List (Fin k × Bool)
  | 1 => ProductFamily.Key (Syntax (Γ:=Γ) (Q:=Q))
  | 2 => List ℕ × (ℕ × ℕ) × List ℕ

local instance instPrimcodableSymbols (i : Fin 3) : Primcodable (Symbols (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) k i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance
local instance instPrimcodableKeys (i : Fin 3) : Primcodable (Keys (Γ:=Γ) (Q:=Q) k i) :=
  match i with
  | 0 => inferInstance
  | 1 => inferInstance
  | 2 => inferInstance

def cost : (i : Fin 3) → Symbols (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) k i → ℕ
  | 0 => fun _ => 0
  | 1 => ProductFamily.cost (Path.letterGrade Word.gradeCell)
  | 2 => (ops (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂)).letterCost

def code (i : Fin 3) := ThreeCodes.code i (cost (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i)
def search (i : Fin 3) := ThreeCodes.search i (cost (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i)

omit [Finite P₁] [Finite P₂] in
theorem primrec_cost (i : Fin 3) : Primrec (cost (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i) := by
  fin_cases i
  · exact Primrec.const 0
  · exact ProductFamily.primrec_cost (A:=Syntax (Γ:=Γ) (Q:=Q))
      (CommonCompiler.primrec_letterGrade (T:=Sigma) (Γ:=Γ) (Q:=Q))
  · exact EffectiveNames.Double.primrec_cost (P₁:=P₁) (P₂:=P₂) (k₀:=ZMod 2) (n:=7)
      (Word.grade (S:=Sigma) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q))
      (CommonCompiler.primrec_grade (T:=Sigma) (Γ:=Γ) (Q:=Q))

variable (e₁ : P₁ → EffectiveNames.Enlargement.Coeff.Name (ZMod 2))
  (e₂ : P₂ → EffectiveNames.Enlargement.Coeff.Name (ZMod 3))

def normal (n : ℕ) (w : List (Syntax (Γ:=Γ) (Q:=Q))) : Part (List (Syntax (Γ:=Γ) (Q:=Q))) :=
  CommonCompiler.service A M (.inr ()) (terminalAlphabet A) (fun x => raw x.1 x.2) (n,w)

theorem partrec_normal : Partrec₂ (normal A M) :=
  CommonCompiler.partrec_service A M (.inr ()) (terminalAlphabet A) partrec_raw

def test : (i : Fin 3) → ℕ → List (Symbols (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) k i) →
    Part (Option (Keys (Γ:=Γ) (Q:=Q) k i))
  | 0 => fun _ => GroupFamily.test s
  | 1 => fun n => ProductFamily.test [.zero] (normal A M n)
  | 2 => fun n => EffectiveNames.Double.test e₁ e₂ Word.grade [.zero] (normal A M n)

def tables (n : ℕ) : ℕ → Part (List (List Sigma × List Sigma)) :=
  FamilyProgram.compute (r:=rel) (code (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k)) search
    none (fun i => test s A M e₁ e₂ i n)

theorem partrec_test (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))
    (i : Fin 3) : Partrec₂ (test s A M e₁ e₂ i) := by
  fin_cases i
  · exact (GroupFamily.partrec_test s h).comp Computable.snd
  · exact ProductFamily.partrec_test (A:=Syntax (Γ:=Γ) (Q:=Q)) [.zero] (partrec_normal A M)
  · exact EffectiveNames.Double.partrec_test (P₁:=P₁) (P₂:=P₂) (k₀:=ZMod 2) (n:=7)
      e₁ e₂ (Word.grade (S:=Sigma) (Γ:=Bool × Γ) (Q:=ParameterCode.Control Q)) [.zero]
      (partrec_normal A M)

theorem partrec_tables (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    Partrec₂ (tables s A M e₁ e₂) :=
  FamilyProgram.partrec_compute _ _ _
    (fun i => ThreeCodes.primrec_words i _ (primrec_cost i))
    (fun i => ThreeCodes.primrec_encode i _ (primrec_cost i)) primrec_shortlex
    (partrec_test s A M e₁ e₂ h)

theorem exists_fixed_point (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    ∃ n, raw n = tableNormal (tables s A M e₁ e₂ n) := by
  have hh := partrec_tableNormal_parameter (partrec_tables s A M e₁ e₂ h)
  have hc : Partrec₂ (fun c : Nat.Partrec.Code => tableNormal (tables s A M e₁ e₂ (Encodable.encode c))) :=
    hh.comp (Computable.encode.comp Computable.fst) Computable.snd
  obtain ⟨c,hc⟩ := WordProgramming.fixed_point hc
  exact ⟨Encodable.encode c, (raw_encode c).trans hc⟩

variable (decode : ∀ g a, (terminalAlphabet A).output g = some a → g = (terminalAlphabet A).input a)
  (realizes : ∀ index, Word.Realizes (terminalAlphabet A) (terminalMachine A M index) (raw index))
  (he₁ : ∀ p, EffectiveNames.Enlargement.Coeff.value (e₁ p) *
    EffectiveNames.Enlargement.Coeff.value (e₁ p) = EffectiveNames.Enlargement.Coeff.value (e₁ p))
  (he₂ : ∀ p, EffectiveNames.Enlargement.Coeff.value (e₂ p) *
    EffectiveNames.Enlargement.Coeff.value (e₂ p) = EffectiveNames.Enlargement.Coeff.value (e₂ p))

include decode realizes he₁ he₂

omit [Finite P₁] [Finite P₂] in
theorem certificate (index n : ℕ) (budget : PartialBudget (raw index) (3 * (n / 10)))
    (i : Fin 3) : TestCertificate (code (Γ:=Γ) (Q:=Q) (P₁:=P₁) (P₂:=P₂) (k:=k) i)
      (test s A M e₁ e₂ i index) n := by
  let C := CommonCompiler.calculus A M (.inr ()) (terminalAlphabet A) index decode
    (f:=fun x => raw x.1 x.2) budget (realizes index)
  have hf (u : List (Syntax (Γ:=Γ) (Q:=Q)))
      (hu : C.grade (FreeMonoid.ofList u) ≤ n / 10) :
      (C.normal (FreeMonoid.ofList u)).toList ∈ normal A M index u := by
    apply CommonCompiler.service_full A M (.inr ()) (terminalAlphabet A) index
      decode budget (realizes index) u
    exact hu.trans (by omega)
  fin_cases i
  · exact GroupFamily.certificate s _ n
  · exact ProductFamily.certificate C _ (Path.letterGrade Word.gradeCell)
      (ProductFamily.grade_cost C _ (fun _ => rfl))
      (ThreeCodes.cost_padding _ _) (by omega) hf
  · exact ActionFamily.certificate
      (EffectiveNames.Double.interpretation (k₀:=ZMod 2) (n:=7) e₁ e₂ C he₁ he₂)
      _ (ThreeCodes.cost_padding _ _) le_rfl _
      (fun w hw => EffectiveNames.Double.test_full e₁ e₂ _ C he₁ he₂ w hw hf)

attribute [local instance] OAI.SimpleFInftyOvergroups.ContextualEncoding.Source.instTrichotomousSigmaRel
omit [Finite P₁] [Finite P₂] in
theorem all_budgets (index : ℕ)
    (fixed : raw index = tableNormal (tables s A M e₁ e₂ index)) :
    ∀ n, GoodTable (r:=rel) (tables s A M e₁ e₂ index) n ∧ PartialBudget (raw index) n := by
  apply FamilyProgram.bootstrap _ _ _ _ wf_rel (raw index) fixed
    (fun i => ThreeCodes.zero_avoids i _) (fun i j h => ThreeCodes.disjoint h _ _)
  intro n hn budget
  have hc := certificate s A M e₁ e₂ decode realizes he₁ he₂ index n budget
  exact ⟨fun i => (hc i).total, fun i => (hc i).nonzero,
    fun i => (hc i).contextual, fun i => (hc i).ideal⟩

theorem exists_total_fixed_point
    (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1)) :
    ∃ index, raw index = tableNormal (tables s A M e₁ e₂ index) ∧
      ∀ n, GoodTable (r:=rel) (tables s A M e₁ e₂ index) n ∧ PartialBudget (raw index) n := by
  obtain ⟨index, hi⟩ := exists_fixed_point s A M e₁ e₂ h
  exact ⟨index,hi,all_budgets s A M e₁ e₂ decode realizes he₁ he₂ index hi⟩

end
end SimpleFInftyOvergroups.ContextualEncoding.Source

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticEnlargements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction SourceEnlargement

namespace IdempotentNames
abbrev Index (k : Type) [CommRing k] := BinaryPrefixOperators.idempotents k
instance instFintypeElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite {k : Type} [CommRing k] [Finite k] : Fintype (Index k) :=
  (BinaryPrefixOperators.idempotents_finite k).fintype
instance instPrimcodableElemSubtypeEndSpaceMemSubalgebraAlgebraIndexOfFinite {k : Type} [CommRing k] [Finite k] : Primcodable (Index k) :=
  FiniteAlgebraicEnvelopes.Effect.finitePrimcodable _

variable {k : Type} [CommRing k]
def name (p : Index k) : Enlargement.Coeff.Name k :=
  (BinaryPrefixOperators.Arithmetic.Lists.value_surjective p.val).choose
@[simp] theorem value_name (p : Index k) : Enlargement.Coeff.value (name p) = p.val :=
  (BinaryPrefixOperators.Arithmetic.Lists.value_surjective p.val).choose_spec
 theorem idempotent (p : Index k) :
    Enlargement.Coeff.value (name p) * Enlargement.Coeff.value (name p) =
      Enlargement.Coeff.value (name p) := by
  simpa only [value_name] using BinaryPrefixOperators.idempotents_are_idempotent k p.property
end IdempotentNames

namespace SemanticEnlargement
variable {G X V Y K L k : Type} [Group V] [MulAction V Y] [Nonempty Y]
  [CommRing k] [Primcodable k] [Primcodable K] [Primcodable L]
  {m : ℕ} (N : Operations G X) (C : ActionCalculus V Y K L m)
  (I : Interpretation N C)

local instance restrictedSMul : SMul (enlargedGroup k V) (enlargedSet k Y) :=
  (SourceEnlargement.enlargedAction k V Y).toSMul

abbrev Word := Enlargement.Word (IdempotentNames.Index k) G
abbrev Point := Enlargement.Point (IdempotentNames.Index k) G X

def calculus : ActionCalculus (enlargedGroup k V) (enlargedSet k Y) (ℕ × ℕ) ℕ m where
  group :=
    { ball := fun b w => (Enlargement.calculus (k:=k) C).group.ball b w.val
      mono := fun _ _ h _ hw => (Enlargement.calculus (k:=k) C).group.mono h hw
      key := fun w => (Enlargement.calculus (k:=k) C).group.key w.val }
  point := (Enlargement.calculus (k:=k) C).point
  one_mem := (Enlargement.calculus (k:=k) C).one_mem
  inv_mem := (Enlargement.calculus (k:=k) C).inv_mem
  mul_mem := (Enlargement.calculus (k:=k) C).mul_mem
  smul_mem := (Enlargement.calculus (k:=k) C).smul_mem
  inv_congr := (Enlargement.calculus (k:=k) C).inv_congr
  mul_congr := (Enlargement.calculus (k:=k) C).mul_congr
  smul_congr := (Enlargement.calculus (k:=k) C).smul_congr

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
 theorem group_mem (w : Word (k:=k) (G:=G)) :
    Enlargement.groupValue N (IdempotentNames.name (k:=k)) I IdempotentNames.idempotent w ∈ enlargedGroup k V := by
  induction w with
  | nil => exact (enlargedGroup k V).one_mem
  | cons a w ih =>
    apply (enlargedGroup k V).mul_mem _ ih
    change SourceEnlargement.unitMap _ _ _ ∈ _
    simp only [IdempotentNames.value_name]
    exact Subgroup.subset_closure ⟨a.1, (I.group a.2).val, rfl⟩

def groupValue (w : Word (k:=k) (G:=G)) : enlargedGroup k V :=
  ⟨Enlargement.groupValue N IdempotentNames.name I IdempotentNames.idempotent w,group_mem N C I w⟩
def pointValue (x : Point (k:=k) (G:=G) (X:=X)) : enlargedSet k Y :=
  Enlargement.pointValue N IdempotentNames.name I IdempotentNames.idempotent x

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_nil : groupValue N C I ([] : Word (k:=k) (G:=G)) = 1 := rfl
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_append (u v : Word (k:=k) (G:=G)) :
    groupValue N C I (u++v) = groupValue N C I u * groupValue N C I v := by
  apply Subtype.ext
  exact Enlargement.groupValue_append _ _ _ _ _ _
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_inverse (u : Word (k:=k) (G:=G)) :
    groupValue N C I (Enlargement.inverse N u) = (groupValue N C I u)⁻¹ := by
  apply Subtype.ext
  exact Enlargement.groupValue_inverse _ _ _ _ _
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem groupValue_singleton (p : IdempotentNames.Index k) (g : G) :
    groupValue N C I [(p,g)] = SourceEnlargement.j k p (I.group g).val := by
  apply Subtype.ext
  simp [groupValue,
    Enlargement.groupValue, Enlargement.rootValue, SourceEnlargement.j, SourceEnlargement.map]
  rfl

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem pointValue_act (g : Word (k:=k) (G:=G)) (x : Point (k:=k) (G:=G) (X:=X)) :
    pointValue N C I (g++x.1,x.2) = groupValue N C I g • pointValue N C I x :=
  Enlargement.pointValue_act _ _ _ _ _ _
omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
@[simp] theorem pointValue_basis (x : X) :
    pointValue N C I (([] : Word (k:=k) (G:=G)),x) = pointEmbedding k (I.point x).val := by
  simp only [pointValue, Enlargement.pointValue, Enlargement.groupValue_nil, one_smul,
    pointEmbedding]

def interpretation : Interpretation (Enlargement.operations (P:=IdempotentNames.Index k) N)
    (calculus (k:=k) C) where
  group w := ⟨groupValue N C I w,Enlargement.gcost N w,Enlargement.group_mem N IdempotentNames.name I IdempotentNames.idempotent w⟩
  point x := ⟨pointValue N C I x, Enlargement.xcost N x,
    Enlargement.point_mem N IdempotentNames.name I IdempotentNames.idempotent x⟩
  group_cost _ := rfl
  point_cost _ := rfl
  one := WithBound.ext' (groupValue_nil N C I) rfl
  mul u v := WithBound.ext' (groupValue_append N C I u v) (Enlargement.gcost_append N u v)
  inv u := WithBound.ext' (groupValue_inverse N C I u) (Enlargement.gcost_inverse N u)
  act g x := WithBound.ext' (pointValue_act N C I g x)
    (by change Enlargement.xcost N (g++x.1,x.2) = Enlargement.gcost N g + Enlargement.xcost N x
        simp [Enlargement.xcost,Nat.add_assoc])

 theorem groupKey_injective (hg : Function.Injective C.group.key) :
    Function.Injective (calculus (k:=k) C).group.key := by
  intro u v h
  apply Subtype.ext
  apply Units.ext
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.mapDomain_injective hg
  exact congrArg Prod.fst (Enlargement.pairedKey_injective h)

end SemanticEnlargement
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticDouble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction SourceEnlargement
namespace SemanticDouble

variable {G X V Y K L : Type} [Group V] [MulAction V Y] [Nonempty Y]
  [Primcodable K] [Primcodable L] {m : ℕ}
  (N : Operations G X) (C : ActionCalculus V Y K L m) (I : Interpretation N C)

abbrev P₁ := IdempotentNames.Index (ZMod 2)
abbrev P₂ := IdempotentNames.Index (ZMod 3)
abbrev N₁ := Enlargement.operations (P:=P₁) N
abbrev N₂ := Enlargement.operations (P:=P₂) (N₁ N)
attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticDouble.instPrimcodableZModOfNatNat_solutions
attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticDouble.instPrimcodableZModOfNatNat_solutions_1
abbrev C₁ := SemanticEnlargement.calculus (k:=ZMod 2) C
abbrev I₁ := SemanticEnlargement.interpretation (k:=ZMod 2) N C I
abbrev C₂ := SemanticEnlargement.calculus (k:=ZMod 3) (C₁ C)
abbrev I₂ := SemanticEnlargement.interpretation (k:=ZMod 3) (N₁ N) (C₁ C) (I₁ N C I)

abbrev GroupName := Enlargement.Word P₂ (Enlargement.Word P₁ G)
abbrev PointName := Enlargement.Point P₂ (Enlargement.Word P₁ G) (Enlargement.Point P₁ G X)

end SemanticDouble
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.SourceModel
noncomputable section
open scoped Classical FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open ContextualEncoding SemanticEncoding EffectiveNames

abbrev family := ContextualEncoding.Source.family

end
end SimpleFInftyOvergroups.SourceModel

end OAI
end


