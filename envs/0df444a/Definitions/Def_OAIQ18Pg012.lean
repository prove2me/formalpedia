-- Prove2me | Definitions.Def_OAIQ18Pg012
-- name    : OAIQ18Pg012
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T16:07:47.140994+00:00
-- url     : https://prove2.me/theorems/541f1316-d979-49eb-8ccc-9d619492bace
-- title:
--   Definitions bundle OAIQ18Pg012 of the split of OpenAI, An infinite finitely presented periodic group
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SourceBurnside.thm_main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented periodic group*, OpenAI Math Release, September 23, 2026, result family 247, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 127 declarations of OpenAI's Lean: 21 definitions, 2 instances and 104 theorems. The definitions and types are `OAI.SourceBurnside.FiniteTable.Codec.reachCon`, `OAI.SourceBurnside.FiniteTable.Rigid.Template.region`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.ChunkVanish`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.LetterVanish`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.Token`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.embeddingHom`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.letters`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.normal`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.positiveSpan`, `OAI.SourceBurnside.SourceMachine.MachineHierarchy.substitutionWords`, `OAI.SourceBurnside.Stability.ExtensionRootLift.hom`, `OAI.SourceBurnside.Stability.ExtensionRootLift.lift`, `OAI.SourceBurnside.Stability.RationalExtension.cochain`, `OAI.SourceBurnside.Stability.RationalExtension.cocycle`, `OAI.SourceBurnside.Stability.RationalExtension.finiteOrderLift`, `OAI.SourceBurnside.Stability.RationalExtension.modelEquiv`, `OAI.SourceBurnside.Stability.RationalExtension.modelHom`, `OAI.SourceBurnside.Stability.SingletonFrameEdge.seed`, `OAI.SourceBurnside.Stability.UnorderedStabilizer.projection`, `OAI.SourceBurnside.Stability.UnorderedStabilizer.quotientMap`, `OAI.SourceBurnside.Stability.UnorderedStabilizer.strip`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/PeriodicGroups, in whole or in part: `PeriodicGroups_Algebra_HierarchyGrowth`, `PeriodicGroups_Algebra_MatrixTests`, `PeriodicGroups_Algebra_WordAlgebra`, `PeriodicGroups_Frames_ElementaryFrames`, `PeriodicGroups_Homology_FiniteNormalHomology`, `PeriodicGroups_Homology_LocallyFiniteActions`, `PeriodicGroups_Homology_RelativeHomology`, `PeriodicGroups_Rules_GeometricRelations`, `PeriodicGroups_Rules_PrefixRewriting`, `PeriodicGroups_Rules_TableEncoding`, `PeriodicGroups_Rules_TemplateHierarchy`, `PeriodicGroups_Rules_Transactions`, `PeriodicGroups_Steinberg_CoefficientQuotients`, `PeriodicGroups_Steinberg_DiagonalActions`, `PeriodicGroups_Steinberg_PresentationModel`, `PeriodicGroups_Steinberg_RankActions`.
--
--   **Imports.** It imports the published bundle `Def_PeriodicGroup`; the bundles `OAIQ18Pg009` and `OAIQ18Pg010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ18Pg014`; the proofs of `OAI.SourceBurnside.ConcreteSource.matrix_periodic`, `OAI.SourceBurnside.ConcreteSource.steinberg_infinite` and `OAI.SourceBurnside.SourceMachine.MachineHierarchy.matrixNilKernel`.
-- source:
--   OpenAI, An infinite finitely presented periodic group, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 247; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-infinite-finitely-presented-periodic-group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/PeriodicGroups at commit adc7f12

import Mathlib
import Definitions.Def_PeriodicGroup
import Definitions.Def_OAIQ18Pg009
import Definitions.Def_OAIQ18Pg010

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_RelativeHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SourceBurnside.Stability
noncomputable section
open Classical
namespace RationalExtension
open RationalBar
variable {X G : Type} [Group X] [Group G] (S : RationalExtension X G)

lemma factor_mul (g h : G) :
    S.inl (Multiplicative.ofAdd (S.factor g h))*S.chosenSection (g*h)=S.chosenSection g*S.chosenSection h := by
  have he := congrArg Subtype.val (S.kernelEquiv.apply_symm_apply
    ⟨S.chosenSection g*S.chosenSection h*(S.chosenSection (g*h))⁻¹,by
      simp only [MonoidHom.mem_ker,map_mul,map_inv,projection_section,mul_inv_cancel]⟩)
  change S.inl (Multiplicative.ofAdd (S.factor g h)) = _ at he
  rw [he,inv_mul_cancel_right]

lemma factor_identity (g h k : G) :
    S.factor g h+S.factor (g*h) k=S.factor h k+S.factor g (h*k) := by
  apply (Multiplicative.ofAdd).injective
  apply S.inl_injective
  apply mul_right_cancel (b := S.chosenSection (g*h*k))
  simp only [ofAdd_add,map_mul]
  rw [mul_assoc,S.factor_mul (g*h) k,←mul_assoc,S.factor_mul g h]
  rw [mul_assoc _ _ (S.chosenSection (g*h*k)),mul_assoc g h k,S.factor_mul g (h*k)]
  have hc := (S.inl_central (Multiplicative.ofAdd (S.factor h k))).comm (S.chosenSection g)
  calc
    S.chosenSection g*S.chosenSection h*S.chosenSection k = S.chosenSection g*(S.inl (Multiplicative.ofAdd (S.factor h k))*S.chosenSection (h*k)) := by rw [S.factor_mul,mul_assoc]
    _ = S.inl (Multiplicative.ofAdd (S.factor h k))*(S.chosenSection g*S.chosenSection (h*k)) := by rw [←mul_assoc,←hc.eq,mul_assoc]

lemma factor_one : S.inl (Multiplicative.ofAdd (S.factor 1 1))=S.chosenSection 1 := by
  apply mul_right_cancel (b := S.chosenSection 1)
  simpa only [one_mul] using S.factor_mul 1 1

def cochain : C2 G →ₗ[ℚ] ℚ := Finsupp.linearCombination ℚ (fun p : G×G => S.factor p.1 p.2)
lemma cochain_single (g h : G) (a : ℚ) : S.cochain (Finsupp.single (g,h) a)=a*S.factor g h := by
  simp [cochain]

def cocycle : Cocycles G := ⟨S.cochain,by
  rw [cocycle_iff]
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro a
  obtain ⟨g,h,k⟩ := p
  change S.cochain (groupHomology.d₃₂ (T G) (Finsupp.single (g,h,k) a))=0
  rw [groupHomology.d₃₂_single]
  change S.cochain (Finsupp.single (h,k) a-Finsupp.single (g*h,k) a+
    Finsupp.single (g,h*k) a-Finsupp.single (g,h) a)=0
  simp only [map_add,map_sub,cochain_single]
  have he := S.factor_identity g h k
  linear_combination -a*he⟩

lemma cocycle_value (g h : G) : value S.cocycle g h=S.factor g h := by
  change S.cochain (Finsupp.single (g,h) 1)=_
  rw [cochain_single,one_mul]

def modelHom : Extension S.cocycle →* X where
  toFun x := S.inl (Multiplicative.ofAdd x.1)*S.chosenSection x.2
  map_one' := by
    change S.inl (Multiplicative.ofAdd (-value S.cocycle 1 1))*S.chosenSection 1=1
    rw [cocycle_value,ofAdd_neg,map_inv,factor_one,inv_mul_cancel]
  map_mul' x y := by
    change S.inl (Multiplicative.ofAdd (x.1+y.1+value S.cocycle x.2 y.2))*S.chosenSection (x.2*y.2)=
      (S.inl (Multiplicative.ofAdd x.1)*S.chosenSection x.2)*(S.inl (Multiplicative.ofAdd y.1)*S.chosenSection y.2)
    rw [cocycle_value]
    simp only [ofAdd_add,map_mul,mul_assoc]
    rw [S.factor_mul]
    have hc := (S.inl_central (Multiplicative.ofAdd y.1)).comm (S.chosenSection x.2)
    rw [←mul_assoc (S.inl (Multiplicative.ofAdd y.1)),hc.eq,mul_assoc]

lemma modelHom_inclusion (q : QGroup) : S.modelHom (inclusion S.cocycle q)=S.inl q := by
  change S.inl (Multiplicative.ofAdd (q.toAdd-value S.cocycle 1 1))*S.chosenSection 1=S.inl q
  rw [cocycle_value,sub_eq_add_neg,ofAdd_add,ofAdd_neg,map_mul,map_inv,factor_one]
  simp only [mul_assoc,inv_mul_cancel,mul_one,ofAdd_toAdd]
lemma modelHom_projection (x : Extension S.cocycle) : S.rightHom (S.modelHom x)=projection S.cocycle x := by
  change S.rightHom (S.inl (Multiplicative.ofAdd x.1)*S.chosenSection x.2)=x.2
  rw [map_mul,S.toGroupExtension.rightHom_inl,projection_section,one_mul]

def modelEquiv : (extension S.cocycle).toGroupExtension.Equiv S.toGroupExtension :=
  GroupExtension.Equiv.ofMonoidHom S.modelHom
    (by ext q; exact S.modelHom_inclusion q)
    (by ext x; exact S.modelHom_projection x)

end RationalExtension
end
end SourceBurnside.Stability

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TableEncoding
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instDecidableCellCut _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma reach_symm {v w : List (Cell q)} (h : Reach S d v w) : Reach S d w v := by
  induction h with
  | refl => exact .refl
  | tail h e ih => exact (Relation.ReflTransGen.single (step_symm e)).trans ih

lemma step_length {v w : List (Cell q)} (h : Step S d v w) : v.length=w.length := by
  rcases h with ⟨p,s,a,b,rfl,rfl,hh⟩
  simp only [List.length_append,(replacement_lengths S d a b hh).1]

lemma reach_length {v w : List (Cell q)} (h : Reach S d v w) : v.length=w.length := by
  induction h with
  | refl => rfl
  | tail h e ih => exact ih.trans (step_length e)

end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax

lemma zero_encode {h : ℕ} (hh : 4≤h) (S : Schedule (2^h)) (d : ℕ) (v : List (Cell (2^h))) :
    zero (by omega) S d (v.map encode) ↔ Zero S d v := by
  cases v with
  | nil => simp [zero,Zero]
  | cons a v =>
    cases v with
    | nil => simp [zero,Zero,unaryZero_encode hh]
    | cons b v =>
      cases v <;> simp [zero,Zero,binaryZero_encode hh]

end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_Transactions
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

namespace Region
variable (R : Region q d) (S : Schedule q)

theorem literal_success (b : Bool) (hb : R.task.zeroTask=true → b=false)
    (hc : ∀ j, (R.plan S).Holds j) :
    Reach S d (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,b⟩))
      (R.realize S ⟨.success,0,b⟩) :=
  R.realize_reach S (((R.plan S).success_iff b).mpr hc) hb
end Region

end SourceBurnside.FiniteTable

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_PrefixRewriting
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest _root_.OAI.SourceBurnside.FiniteTable.instTransCellGeomRel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable

open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

omit [NeZero q] in
lemma scan_palette (w : List (Cell q)) (c : Cell q) (hc : c.isPalette)
    (hchain : StructuralChain (c::w)) (hlast : EndsStop (c::w)) :
    ∃ pal z s, c::w=pal++z::s ∧ pal≠[] ∧ (∀a∈pal,a.isPalette) ∧ z.pos=.stop := by
  induction w generalizing c with
  | nil =>
    obtain ⟨x,hx⟩ := hc
    have hz := hlast c (by simp)
    rw [hx] at hz
    cases hz
  | cons b w ih =>
    obtain ⟨hcb,hbw⟩ := List.isChain_cons_cons.mp hchain
    obtain ⟨x,hx⟩ := hc
    change c.skeleton.pos=.palette x at hx
    cases hp : b.pos with
    | palette y =>
      obtain ⟨pal,z,s,he,hpn,hpall,hz⟩ := ih b ⟨y,hp⟩ hbw (endsStop_cons_tail hlast)
      refine ⟨c::pal,z,s,by simp only [List.cons_append,he],List.cons_ne_nil _ _,?_,hz⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact ⟨x,hx⟩
      · exact hpall a ha
    | core p =>
      change b.skeleton.pos=.core p at hp
      simp only [Skeleton.Structural,hx,hp] at hcb
    | stop =>
      refine ⟨[c],b,w,rfl,by simp,?_,hp⟩
      intro a ha
      have he := List.mem_singleton.mp ha
      subst a
      exact ⟨x,hx⟩

lemma scan_block (w : List (Cell q)) (c : Cell q) (hc : c.pos=.core (0 : Fin q))
    (hchain : StructuralChain (c::w)) (hlast : EndsStop (c::w)) :
    ∃ B : StructuralBlock q, ∃ s, c::w=B.word++s := by
  obtain ⟨cores,b,s,he,hcpos,hb⟩ := scan_core w c 0 hc hchain hlast
  have hchain' : StructuralChain (b::s) := (List.isChain_append.mp (he ▸ hchain)).2.1
  have hlast' : EndsStop (b::s) := endsStop_suffix cores _ (he ▸ hlast)
  obtain ⟨pal,z,t,hpal,hpn,hpp,hzp⟩ := scan_palette s b hb hchain' hlast'
  let B : StructuralBlock q := ⟨cores,by simpa using hcpos,pal,hpn,hpp,z,hzp⟩
  exact ⟨B,t,by simpa [B,StructuralBlock.word,hpal,List.append_assoc] using he⟩

theorem structural_decompose (w : List (Cell q)) (hc : StructuralChain w)
    (hs : StartsCore w) (hl : EndsStop w) :
    ∃ bs : List (StructuralBlock q), w=bs.flatMap StructuralBlock.word := by
  generalize hn : w.length=n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    cases w with
    | nil => exact ⟨[],rfl⟩
    | cons c w =>
      obtain ⟨B,s,he⟩ := scan_block w c (hs c (by simp)) hc hl
      have hsc : StructuralChain (B.word++s) := he ▸ hc
      have hlen : s.length<n := by
        have hh := congrArg List.length he
        have hp := List.length_pos_iff.mpr B.word_nonempty
        simp only [List.length_append] at hh
        omega
      obtain ⟨bs,hbs⟩ := ih s.length hlen s (List.isChain_append.mp hsc).2.1
        (B.starts_after hsc) (endsStop_suffix B.word s (he ▸ hl)) rfl
      exact ⟨B::bs,by simpa only [List.flatMap_cons,←hbs] using he⟩

end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_GeometricRelations
attribute [-instance] _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawReplacement _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Codec.decideRawZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsLeft _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcceptsRight _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAcquireTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideAdmissible _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideBinaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCellPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerAdvanceTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerCreateTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCheckerPair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideCore _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDataTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideDuplicateColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideEndpoint _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFirst _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideFormat _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHead _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideHeadFree _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideInternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLast _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLastOK _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideLeftExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideMissingColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalette _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePalettePair _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decidePassedOwnColor _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReadRightTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideReplacement _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideRightExternal _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSemanticZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideStructural _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideSwapTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnary _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUnaryZero _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoLeftTest _root_.OAI.SourceBurnside.FiniteTable.Recognizer.decideUndoRightTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w
namespace SourceBurnside.FiniteTable
section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

theorem Survives.complete_normalize {w : List (Cell q)} (hw : Survives S d w)
    (hd : d≤q) (hs : Syntax S d w) (hfirst : StartsCore w) (hlast : EndsStop w) :
    ∃ u : List (Fin d → ZMod 2), Reach S d w (encodeWord u) := by
  obtain ⟨v,hv,hidle⟩ := hw.transactions_idle hs
  have hshape := reach_shape hv
  have hvc : StructuralChain v := (hw.of_reach hv).chain.imp (fun _ _ hp => hp.1.1)
  obtain ⟨bs,hbs⟩ := structural_decompose v hvc
    (startsCore_shape hshape hfirst) (endsStop_shape hshape hlast)
  refine ⟨bs.map (fun B => B.bits hd),hv.trans ?_⟩
  rw [hbs]
  exact idle_blocks_normalize hd bs (hbs ▸ (hw.of_reach hv)) (hbs ▸ hidle)

lemma Survives.syntax_of_exterior {w : List (Cell q)} (hw : Survives S d w)
    (hl : ∀a∈w.head?,a.skeleton.leftExternal)
    (hr : ∀a∈w.getLast?,a.skeleton.rightExternal) : Syntax S d w := by
  refine ⟨⟨?_,?_⟩,hw.chain.imp (fun _ _ h => h.2),fun a ha => hw.format ha⟩
  · intro a ha
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    exact (hw.format hc).1
  · have hp : (w.map (fun a : Cell q => some a.skeleton)).IsChain Skeleton.Link := by
      rw [List.isChain_map]
      exact hw.chain.imp (fun _ _ h => h.1)
    have hlast : ∀a∈(w.map (fun a : Cell q => some a.skeleton)).getLast?,
        ∀b∈([none] : List (Option (Skeleton q 10))).head?,Skeleton.Link a b := by
      simpa [List.getLast?_map,Skeleton.Link] using hr
    have htail : ((w.map (fun a : Cell q => some a.skeleton))++[none]).IsChain Skeleton.Link :=
      List.isChain_append.mpr ⟨hp,by simp,hlast⟩
    rw [List.isChain_cons]
    refine ⟨?_,by simpa [List.map_map,Function.comp_def] using htail⟩
    cases w with
    | nil => simp [Skeleton.Link]
    | cons a w => simpa [Skeleton.Link] using hl a (by simp)

theorem Survives.cut_interval_normalize {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w++[b])) (ha : a.Cut) (hb : b.Cut) (hd : d≤q) :
    ∃ u : List (Fin d → ZMod 2), Reach S d (a::w) (encodeWord u) := by
  have hw' : Survives S d (a::w) := hw.infix ⟨[],[b],by simp⟩
  have hedge := hw.before_cut_end hb
  have hsyntax := hw'.syntax_of_exterior
    (by simpa using Cell.cut_leftExternal ha (hw'.format (by simp))) hedge.2
  exact hw'.complete_normalize hd hsyntax (by simpa [StartsCore] using ha.1) hedge.1
end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

lemma firstCoreCount_reach {v w : List (Cell q)} (hr : Reach S d v w) :
    firstCoreCount v=firstCoreCount w := by
  rw [firstCoreCount_shape,firstCoreCount_shape,reach_shape hr]

end

section
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q] {S : Schedule q}

theorem Survives.token_normalization {a b : Cell q} {w : List (Cell q)}
    (hw : Survives S d (a::w++[b])) (ha : a.Cut) (hb : b.Cut)
    (hn : ∀c∈w,¬c.Cut) (hd : d≤q) :
    ∃ u : List (Fin d → ZMod 2), 1≤u.length ∧ u.length≤10 ∧
      (a::w).length=(2*q+1)*u.length ∧ Reach S d (a::w) (encodeWord u) := by
  obtain ⟨u,hr⟩ := hw.cut_interval_normalize ha hb hd
  have hl : (a::w).length=(2*q+1)*u.length := by
    simpa using reach_length hr
  have hu : 1≤u.length := by
    by_contra h
    have hz : u.length=0 := by omega
    simp [hz] at hl
  have hw' : Survives S d (a::w) := hw.infix ⟨[],[b],by simp⟩
  have hc := hw'.beginning_count_bound hn
  rw [firstCoreCount_reach hr,firstCoreCount_encode] at hc
  exact ⟨u,hu,hc,hl,hr⟩
end

open LocalSyntax LocalSyntax.Skeleton
namespace Rigid
variable {q d n : ℕ} [NeZero q]

lemma canonicalBlock_get (bits : Fin d → ZMod 2) (i : Fin (width q)) :
    (canonicalBlock (q:=q) bits)[i.val]'(by simpa [width] using i.isLt)=
      canonicalCell bits (position i) := by
  have hi := i.isLt
  unfold width at hi
  by_cases hc : i.val<q
  · simp [canonicalBlock,position,hc]
  · by_cases hp : i.val<2*q
    · have hr : i.val-q<q := by omega
      simp [canonicalBlock,List.getElem_append,position,hc,hp,hr]
    · have he : i.val=2*q := by omega
      simp [canonicalBlock,List.getElem_append,position,he,show ¬2*q<q by omega,show ¬2*q-q<q by omega]

lemma canonicalBlock_ofFn (bits : Fin d → ZMod 2) :
    canonicalBlock (q:=q) bits=List.ofFn (fun i : Fin (width q) =>
      canonicalCell bits (position i)) := by
  apply List.ext_getElem
  · simp [width]
  · intro i hi hj
    simpa using canonicalBlock_get bits ⟨i,by simpa [width] using hi⟩

lemma encoded_ofFn (u : Fin n → Fin d → ZMod 2) :
    List.ofFn (encoded (q:=q) u)=encodeWord (List.ofFn u) := by
  rw [List.ofFn_mul]
  simp only [encodeWord,List.flatMap_def,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext b
  simp only [Function.comp_def]
  rw [canonicalBlock_ofFn]
  apply congrArg List.ofFn
  funext p
  exact encoded_cell u b p

end Rigid
end SourceBurnside.FiniteTable

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Rules_TemplateHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Rigid

namespace Template
variable (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → ZMod 2)
    (cert : Fin q → ZMod 2)

lemma adjacent (i j : Fin ((task.arity.val+1)*width q)) (hij : i.val+1=j.val) :
    Structural (cell task u cert i).skeleton (cell task u cert j).skeleton ∧
    Internal (cell task u cert i).skeleton (cell task u cert j).skeleton := by
  constructor
  · have hs : (List.ofFn (encoded (q:=q) (u false))).IsChain Pair := by
      rw [encoded_ofFn]
      exact encodeWord_pair_chain _
    have hh := List.isChain_ofFn.mp hs i.val (by rw [hij];exact j.isLt)
    have hh' : Pair (encoded (u false) i) (encoded (u false) j) := by
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      exact Fin.ext hij.symm
    exact hh'.1.1
  · refine ⟨rfl,rfl,?_,?_,?_⟩
    · exact adjacent_blocks i j hij
    · rw [first_iff]
      omega
    · rw [last_iff]
      have := j.isLt
      omega

def region : Region q d where
  size := (task.arity.val+1)*width q
  positive := Nat.mul_pos (by omega) width_pos
  task := task
  cell := cell task u cert
  task_eq := fun _ => rfl
  first_iff := first_iff task u cert
  last_iff := last_iff task u cert
  adjacent := adjacent task u cert
  payload_format := payload_format task u cert

end Template
end Rigid
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable
open LocalSyntax LocalSyntax.Skeleton
variable {q d : ℕ} [NeZero q]
namespace Region
variable (R : Region q d) (S : Schedule q)
lemma acquire (s : Bool) (hs : R.task.zeroTask=true → s=false) :
    Reach S d (R.idleWord s)
      (R.realize S (HeadTour.atClause (R.plan S).first ⟨.acquisition,0,s⟩)) :=
  reach_symm ((Relation.ReflTransGen.single (R.unfinish S s hs)).trans
    (R.release S R.last s hs))

theorem literal_change (s : Bool) (hz : R.task.zeroTask=false)
    (hc : ∀j,(R.plan S).Holds j) : Reach S d (R.idleWord s) (R.idleWord (!s)) := by
  have hs : R.task.zeroTask=true → s=false := by simp [hz]
  have ht : R.task.zeroTask=true → (!s)=false := by simp [hz]
  exact (R.acquire S s hs).trans ((R.literal_success S s hs hc).trans
    ((Relation.ReflTransGen.single (R.edge_realize_step S (.flip s hz) hs)).trans
      ((reach_symm (R.literal_success S (!s) ht hc)).trans (reach_symm (R.acquire S (!s) ht)))))

theorem literal_zero (hz : R.task.zeroTask=true) (hc : ∀j,(R.plan S).Holds j) :
    ∃ p a t, Reach S d (R.idleWord false) (p++[a]++t) ∧ Zero S d [a] := by
  have hs : R.SideOK S ⟨.success,0,false⟩ := by intro; rfl
  let state : HeadTour.FullState (S.count R.task).val R.size := ⟨.success,0,false⟩
  have hv : Reach S d (R.idleWord false) (R.realize S state) :=
    (R.acquire S false (by intro;rfl)).trans (R.literal_success S false (by intro;rfl) hc)
  refine ⟨(R.realize S state).take (R.position S state).val,
    R.realizeCell S state (R.position S state),
    (R.realize S state).drop ((R.position S state).val+1),?_,?_⟩
  · convert hv using 1
    all_goals try with_reducible_and_instances rfl
    exact (ofFn_split_one (R.realizeCell S state) (R.position S state)).symm
  · exact Or.inl ⟨_,rfl,Or.inr (Or.inl (R.realize_semanticZero S state (Or.inr ⟨rfl,hz⟩)))⟩
end Region

namespace Rigid.Template
variable (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → ZMod 2)
    (cert : Fin q → ZMod 2)

lemma idle_word (s : Bool) :
    (region task u cert).idleWord s=encodeWord (List.ofFn (u s)) := by
  rw [←encoded_ofFn]
  apply congrArg List.ofFn
  funext i
  exact idle_cell task u cert s i

lemma locate (b : Fin (task.arity.val+1)) (p : Fin q) :
    (region task u cert).locate b p=core b p := by
  symm
  apply (region task u cert).locate_unique b p (core b p)
  · change (block (core b p)).val=b.val
    rw [core,block_cell]
  · change position (coord (core b p))=.core p
    rw [core,coord_cell,position_core_iff]

lemma slot (s : Bool) (b : Fin (task.arity.val+1)) (p : Fin q) :
    (region task u cert).slot s b p = if hp : p.val<d then u s b ⟨p.val,hp⟩ else 0 := by
  unfold Region.slot
  rw [locate]
  change (cell task u cert (core b p)).data s = _
  have hp : position (coord (core b p))=.core p := by rw [core,coord_cell,position_core_iff]
  simp only [cell,hp]
  rw [core,block_cell]

lemma certificate (p : Fin q) : (region task u cert).certificate p=cert p := by
  change ((region task u cert).cell ((region task u cert).locate (0 : Fin (task.arity.val+1)) p)).certificate=cert p
  rw [locate task u cert (0 : Fin (task.arity.val+1)) p]
  change (cell task u cert (core 0 p)).certificate = _
  have hp : position (coord (core (n:=task.arity.val+1) 0 p))=.core p := by
    rw [core,coord_cell,position_core_iff]
  simp only [cell,hp]
  rw [core,block_cell]
  simp

theorem replacement (S : Schedule q) (s : Bool) (hz : task.zeroTask=false)
    (hc : ∀j,((region task u cert).plan S).Holds j) :
    Reach S d (encodeWord (List.ofFn (u s))) (encodeWord (List.ofFn (u (!s)))) := by
  simpa only [idle_word] using (region task u cert).literal_change S s hz hc

theorem zero (S : Schedule q) (hz : task.zeroTask=true)
    (hc : ∀j,((region task u cert).plan S).Holds j) :
    ∃ p a t, Reach S d (encodeWord (List.ofFn (u false))) (p++[a]++t) ∧ Zero S d [a] := by
  simpa only [idle_word] using (region task u cert).literal_zero S hz hc

end Rigid.Template
end SourceBurnside.FiniteTable

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ}
lemma replacement_symm (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) (a b : List (Raw h)) :
    replacement hh S d a b ↔ replacement hh S d b a := by
  unfold replacement
  cases ha : decodeWord hh a <;> cases hb : decodeWord hh b <;>
    simp only [FiniteTable.replacement_symm]
lemma step_symm {hh : 0<h} {S : Schedule (2^h)} {v w : List (Raw h)}
    (he : Step hh S d v w) : Step hh S d w v := by
  obtain ⟨p,s,a,b,rfl,rfl,he⟩ := he
  exact ⟨p,s,b,a,rfl,rfl,(replacement_symm hh S d a b).mp he⟩
end SourceBurnside.FiniteTable.Codec

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable
variable {q d h D : ℕ} [NeZero q]
lemma physical_template (task : Task) (u : Bool → Fin (task.arity.val+1) → Fin d → Bool) (cert : Fin q → Bool) :
    physicalBits (Rigid.Template.region task (fun s b => scalars (u s b)) (fun p => Addressable.bit (cert p)))=
      Layout.assemble (templateData task u) cert := by
  funext a
  cases a with
  | certificate p =>
    simp only [physicalBits,Region.read,Rigid.Template.certificate,Layout.assemble]
    exact Addressable.unbit_bit _
  | data s b p =>
    simp only [physicalBits,Region.read,Rigid.Template.region]
    change Addressable.unbit (if hb : b.val<task.arity.val+1 then
      (Rigid.Template.region task (fun s b => scalars (u s b)) (fun p => Addressable.bit (cert p))).slot s ⟨b.val,hb⟩ p else 0)=_
    by_cases hb : b.val<task.arity.val+1
    · erw [dite_eq_left hb,Rigid.Template.slot]
      by_cases hp : p.val<d
      · simp [hp,Layout.assemble,templateData,hb,scalars]
        rfl
      · simp [hp,Layout.assemble,templateData,hb,Addressable.unbit]
    · simp [hb,Layout.assemble,templateData,Addressable.unbit]
lemma template_certificate (a : List Bool) (fit : RawFit.Fits β g D h a.length)
    (hd : 0<10000*(D*h)) (task : Task)
    (u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h)) (cert : Fin (2^h) → Bool)
    (hc : ∀i, ((layout h a.length D fit).clauseAt localCircuit.circuit localCircuit.output
      (sourceInitial a fit hd task) blankBits acceptBits i).Holds (Layout.assemble (templateData task u) cert)) :
    ∀i, ((Rigid.Template.region task (fun s b => scalars (u s b)) (fun p => Addressable.bit (cert p))).plan
      (sourceSchedule a fit hd)).Holds i := by
  apply (physical_clauses_iff _ _ _ _ _ _ _).mpr
  rw [physical_template]
  exact hc

end
end SourceBurnside.SourceMachine

namespace SourceBurnside.SourceMachine
noncomputable section
open Addressable LocalSyntax FiniteTable

namespace MachineHierarchy
variable {D : ℕ} {hD : 2≤D} (A : MachineHierarchy D hD)

theorem simulate {h : ℕ} (hh : A.threshold≤h) (task : Task)
    (u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h))
    (he : Codec.entry (A.height_pos (A.next_large hh)) (A.schedule (D*h) (A.next_large hh))
      (10000*(D*(D*h))) task.zeroTask (List.ofFn (u false))
      (if task.zeroTask then [] else List.ofFn (u true))=true) :
    (task.zeroTask=false → Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h))
      (embedding h D (List.ofFn (u false))) (embedding h D (List.ofFn (u true)))) ∧
    (task.zeroTask=true → ∃p z r, Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h))
      (embedding h D (List.ofFn (u false))) (p++z++r) ∧
      Codec.zero (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) z) := by
  have heq := A.certifies h hh task (templateData (q:=2^h) task u)
  dsimp only at heq
  rw [candidate_template task u (A.fits h hh).2.2.2.1 _ false,
    candidate_template task u (A.fits h hh).2.2.2.1 _ true] at heq
  obtain ⟨cert,hc⟩ := heq.mpr he
  have hr := template_certificate A.code (A.fits h hh) (A.data_pos hh) task u cert hc
  have h4 : 4≤h := A.threshold_four.trans hh
  constructor
  · intro hz
    have hs := Rigid.Template.replacement task (fun s b => scalars (u s b))
      (fun p => Addressable.bit (cert p)) _ false hz hr
    simpa only [embedding,schedule,List.map_ofFn,Function.comp_def,Bool.not_false] using Codec.reach_encode h4 hs
  · intro hz
    obtain ⟨p,a,r,hs,hz⟩ := Rigid.Template.zero task (fun s b => scalars (u s b))
      (fun p => Addressable.bit (cert p)) _ hz hr
    refine ⟨p.map Codec.encode,[Codec.encode a],r.map Codec.encode,?_,?_⟩
    · simpa only [embedding,schedule,List.map_ofFn,Function.comp_def,List.map_append,List.map_cons,List.map_nil] using
        Codec.reach_encode h4 hs
    · exact (Codec.zero_encode h4 _ _ [a]).mpr hz
end MachineHierarchy
end
end SourceBurnside.SourceMachine

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_WordAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.FiniteTable.Codec
open LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma step_context {v w : List (Raw h)} (he : Step hh S d v w) (p s : List (Raw h)) :
    Step hh S d (p++v++s) (p++w++s) := by
  obtain ⟨a,b,c,e,rfl,rfl,he⟩ := he
  exact ⟨p++a,b++s,c,e,by simp [List.append_assoc],by simp [List.append_assoc],he⟩
lemma reach_context {v w : List (Raw h)} (he : Reach hh S d v w) (p s : List (Raw h)) :
    Reach hh S d (p++v++s) (p++w++s) := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact ih.tail (step_context e p s)
lemma reach_symm {v w : List (Raw h)} (he : Reach hh S d v w) : Reach hh S d w v := by
  induction he with
  | refl => exact .refl
  | tail h e ih => exact (Relation.ReflTransGen.single (step_symm e)).trans ih

def reachCon (hh : 0<h) (S : Schedule (2^h)) (d : ℕ) : Con (FreeMonoid (Raw h)) where
  r v w := Reach hh S d v.toList w.toList
  iseqv := ⟨fun _ => .refl,fun h => reach_symm h,fun h k => h.trans k⟩
  mul' := by
    intro a b c e hab hce
    change Reach hh S d (a.toList++c.toList) (b.toList++e.toList)
    have h₁ : Reach hh S d (a.toList++c.toList) (b.toList++c.toList) := by
      simpa using reach_context hab [] c.toList
    have h₂ : Reach hh S d (b.toList++c.toList) (b.toList++e.toList) := by
      simpa using reach_context hce b.toList []
    exact h₁.trans h₂
lemma reach_iff_table {v w : List (Raw h)} :
    Reach hh S d v w ↔ (algebraTable hh S d).Reach (FreeMonoid.ofList v) (FreeMonoid.ofList w) := by
  constructor
  · intro hr
    induction hr with
    | refl => exact (conGen (algebraTable hh S d).rep).refl _
    | tail h e ih =>
      obtain ⟨p,s,a,b,rfl,rfl,he⟩ := e
      apply (conGen (algebraTable hh S d).rep).trans ih
      exact (conGen (algebraTable hh S d).rep).mul
        ((conGen (algebraTable hh S d).rep).mul ((conGen (algebraTable hh S d).rep).refl (FreeMonoid.ofList p))
          (ConGen.Rel.of (FreeMonoid.ofList a) (FreeMonoid.ofList b) he))
        ((conGen (algebraTable hh S d).rep).refl (FreeMonoid.ofList s))
  · intro h
    have hle : conGen (algebraTable hh S d).rep ≤ reachCon hh S d := by
      apply Con.conGen_le.mpr
      intro a b he
      exact Relation.ReflTransGen.single ⟨[],[],a.toList,b.toList,by simp,by simp,he⟩
    exact hle h
end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_HierarchyGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.FiniteTable
noncomputable section
open Classical LocalSyntax Cuts
variable {q : ℕ} [NeZero q] {S : Schedule q} {d : ℕ}

lemma token_normal_form {t : List (Cell q)} (ht : Token S d t) (hd : d≤q) :
    ∃u : List (Fin d → ZMod 2), 1≤u.length ∧ u.length≤10 ∧
      t.length=(2*q+1)*u.length ∧ Reach S d t (encodeWord u) := by
  obtain ⟨⟨a,w,rfl,ha,hn⟩,b,hb,hw⟩ := ht
  exact hw.token_normalization ha hb hn hd
end
end SourceBurnside.FiniteTable
namespace SourceBurnside.FiniteTable.Codec
noncomputable section
open Classical LocalSyntax
variable {h d : ℕ} {hh : 0<h} {S : Schedule (2^h)}
lemma rawToken_normalize (h4 : 4 ≤ h) {D : ℕ} (hd : 10000*(D*h) ≤ 2^h)
    {t : List (Raw h)} (ht : rawToken hh S (10000*(D*h)) t) :
    ∃u : List (Raw (D*h)),1 ≤ u.length ∧ u.length ≤ 10 ∧
      t.length=(2*(2^h)+1)*u.length ∧ Reach hh S (10000*(D*h)) t (SourceMachine.embedding h D u) := by
  obtain ⟨v,hv,rfl⟩ := ht
  obtain ⟨u,hn,hk,hlen,hr⟩ := token_normal_form hv hd
  refine ⟨u.map SourceMachine.bits,by simpa,by simpa,by simpa,?_⟩
  have hh := reach_encode h4 hr
  simpa [SourceMachine.embedding,List.map_map,Function.comp_def] using hh

end
end SourceBurnside.FiniteTable.Codec

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Algebra_MatrixTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
lemma simulate_replacement {h : ℕ} (hh : A.threshold ≤ h) {v w : List (Codec.Raw (D*h))}
    (he : Codec.replacement (A.height_pos (A.next_large hh))
      (A.schedule (D*h) (A.next_large hh)) (10000*(D*(D*h))) v w) :
    Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) (embedding h D v) (embedding h D w) := by
  obtain ⟨hlen,hn,hk⟩ := Codec.replacement_lengths (A.threshold_four.trans (A.next_large hh)) _ _ v w he
  let task : Task := ⟨⟨v.length-1,by omega⟩,false⟩
  have htask : task.arity.val+1=v.length := by dsimp [task];omega
  let u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h) := fun s i =>
    if s then w[i.val]'(by have := i.isLt;omega) else v[i.val]'(by have := i.isLt;omega)
  have hv : List.ofFn (u false)=v := by
    apply List.ext_getElem (by simpa [List.length_ofFn] using htask)
    intro i hi hj
    simp only [List.getElem_ofFn,u,Bool.false_eq_true,ite_false]
  have hw : List.ofFn (u true)=w := by
    apply List.ext_getElem (by simpa [List.length_ofFn] using htask.trans hlen)
    intro i hi hj
    simp only [List.getElem_ofFn,u,ite_true]
  have HH := A.simulate hh task u (by
    change Codec.entry _ _ _ false (List.ofFn (u false)) (List.ofFn (u true))=true
    rw [hv,hw]
    exact (Codec.entry_replacement _ _ _ _ _).mpr he)
  simpa only [hv,hw] using HH.1 rfl
lemma simulate_zero {h : ℕ} (hh : A.threshold ≤ h) {v : List (Codec.Raw (D*h))}
    (he : Codec.zero (A.height_pos (A.next_large hh))
      (A.schedule (D*h) (A.next_large hh)) (10000*(D*(D*h))) v) :
    ∃p z s, Codec.Reach (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) (embedding h D v) (p++z++s) ∧
      Codec.zero (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) z := by
  obtain ⟨hn,hk⟩ := Codec.zero_lengths _ _ _ v he
  let task : Task := ⟨⟨v.length-1,by omega⟩,true⟩
  have htask : task.arity.val+1=v.length := by dsimp [task];omega
  let u : Bool → Fin (task.arity.val+1) → Codec.Raw (D*h) := fun _ i => v[i.val]'(by have := i.isLt;omega)
  have hv : List.ofFn (u false)=v := by
    apply List.ext_getElem (by simpa [List.length_ofFn] using htask)
    intro i hi hj
    simp only [List.getElem_ofFn,u]
  have HH := A.simulate hh task u (by
    change Codec.entry _ _ _ true (List.ofFn (u false)) []=true
    rw [hv]
    exact (Codec.entry_zero _ _ _ _ _).mpr ⟨rfl,he⟩)
  simpa only [hv] using HH.2 rfl

def substitutionWords (h : ℕ) : FreeMonoid (Codec.Raw (D*h)) →* FreeMonoid (Codec.Raw h) where
  toFun := fun w => FreeMonoid.ofList (embedding h D w.toList)
  map_one' := by simp [embedding,encodeWord]
  map_mul' := by intro v w;simp [embedding,encodeWord,List.flatMap_append]

def embeddingHom (K : Type*) [CommRing K] {h : ℕ} (hh : A.threshold ≤ h) :
    A.Algebra K (D*h) (A.next_large hh) →ₐ[K] A.Algebra K h hh :=
  WordAlgebra.Table.substitution _ _ (substitutionWords (D:=D) h)
    (by
      intro a b hab
      apply (A.table h hh).word_reach
      exact Codec.reach_iff_table.mp (A.simulate_replacement hh hab))
    (by
      intro a ha
      obtain ⟨p,z,s,hr,hz⟩ := A.simulate_zero hh ha
      apply (A.table h hh).word_eq_zero_of_vanishes
      exact ⟨FreeMonoid.ofList p,FreeMonoid.ofList z,FreeMonoid.ofList s,hz,Codec.reach_iff_table.mp hr⟩)
end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_PresentationModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h)
abbrev Token := {t : List (Codec.Raw h) // Codec.rawToken (A.height_pos hh) (A.schedule h hh) (10000*(D*h)) t}
instance token_finite : Finite (A.Token hh) := (Codec.finite_rawTokens (hh:=A.height_pos hh) (S:=A.schedule h hh) (d:=10000*(D*h))).to_subtype
instance token_fintype : Fintype (A.Token hh) := Fintype.ofFinite _
def normal (t : A.Token hh) : List (Codec.Raw (D*h)) :=
  Classical.choose (Codec.rawToken_normalize (A.threshold_four.trans hh) (A.fits h hh).2.2.2.1 t.property)
def letters (K : Type*) [CommRing K] : Codec.Raw h → A.Algebra K h hh :=
  Codec.letter (A.height_pos hh) (A.schedule h hh) (10000*(D*h))
end
end SourceBurnside.SourceMachine.MachineHierarchy
namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type*) [CommRing K]

def LetterVanish (d : ℕ) : Prop :=
  ∀(ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ d →
    ∀W : Codec.Raw h → Matrix ι ι K, ∃N,∀n,N ≤ n → MatrixTests.letterSum W (A.letters hh K) n=0
def ChunkVanish (d b : ℕ) : Prop :=
  ∀(ι Γ : Type) [Fintype ι] [DecidableEq ι] [Fintype Γ], Fintype.card ι ≤ d →
    ∀(label : Γ → List (Codec.Raw h)),(∀c,label c≠[]) → (∀c,(label c).length ≤ b) →
    ∀W : Γ → Matrix ι ι K,∃N,∀n,N ≤ n → MatrixTests.chunkSum label W (A.letters hh K) n=0
end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.SourceMachine.MachineHierarchy
noncomputable section
open Classical FiniteTable
open scoped BigOperators
variable {D : ℕ} {hD : 2 ≤ D} (A : MachineHierarchy D hD)
variable {h : ℕ} (hh : A.threshold ≤ h) (K : Type) [CommRing K]

def positiveSpan : Submodule K (A.Algebra K h hh) :=
  Submodule.span K (Set.range (fun w : {w : List (Codec.Raw h) // w≠[]}=>
    DirectCancellation.eval (A.letters hh K) w.val))
end
end SourceBurnside.SourceMachine.MachineHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_DiagonalActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SourceBurnside.Stability.SteinbergAction
noncomputable section
open Classical Steinberg MatrixGenerators
variable {n : ℕ} {R : Type*} [Ring R]

lemma scale_inv (u : Fin n → Rˣ) : (scale u)⁻¹ = scale (fun i => (u i)⁻¹) := by
  ext g
  rfl

end
end SourceBurnside.Stability.SteinbergAction

end
section
namespace SourceBurnside.Stability.MatrixK1
noncomputable section
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

variable [Algebra (ZMod 2) R]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
include ε hI

variable [Fintype κ] [DecidableEq κ]

lemma coset_representative (e : ι ↪ κ) (hι : 5≤Fintype.card ι) (g : (Matrix κ κ R)ˣ) :
    ∃h : (Matrix ι ι R)ˣ, g * embed e h ∈ E := by
  obtain ⟨x,rfl⟩ := SmallPresentation.evaluate_surjective ε hI g
  obtain ⟨y,hy⟩ := (SmallPresentation.K1equivalence (R := R) e hι).surjective
    (SmallPresentation.toK1 x)⁻¹
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective SmallPresentation.elementaryGroup y
  refine ⟨SmallPresentation.evaluate z,?_⟩
  rw [←SmallPresentation.evaluate_inclusion_apply,←map_mul,evaluate_mem_iff ε hI]
  apply (QuotientGroup.eq_one_iff _).mp
  change SmallPresentation.toK1 (x * SmallPresentation.inclusion e z) = 1
  rw [map_mul]
  change SmallPresentation.toK1 x * SmallPresentation.K1map e (SmallPresentation.toK1 z) = 1
  change SmallPresentation.toK1 x * (SmallPresentation.K1equivalence (R := R) e hι)
    (SmallPresentation.toK1 z) = 1
  change (SmallPresentation.K1equivalence (R := R) e hι) (SmallPresentation.toK1 z) = _ at hy
  rw [hy,mul_inv_cancel]

end
end SourceBurnside.Stability.MatrixK1

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Frames_ElementaryFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.MatrixK1
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators
variable {R ι κ : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

variable [Algebra (ZMod 2) R]

variable [Fintype κ] [DecidableEq κ]

variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)

include ε hI in

lemma ordered_transitive (hι : 5≤Fintype.card ι)
    (v : κ → ColumnFrames.Vertex (ι := ι ⊕ κ) ε)
    (hv : LinearIndependent (ZMod 2) (ColumnFrames.rho ε ∘ v)) :
    ∃U : E (R := R) (ι := ι ⊕ κ), ∀j,
      U.val • ColumnFrames.standard ε (Sum.inr j) = v j := by
  obtain ⟨U,hU⟩ := ColumnFrames.complete ε hI (Function.Embedding.inr (α := ι)) v hv
  obtain ⟨A,hA⟩ := coset_representative ε hI (Function.Embedding.inl (β := κ)) hι U
  refine ⟨⟨U*embed (Function.Embedding.inl (β := κ)) A,hA⟩,fun j => ?_⟩
  change (U*embed (Function.Embedding.inl (β := κ)) A) • _ = _
  rw [embed_sumInl,mul_smul]
  have he : blockInclusion (κ := κ) A • ColumnFrames.standard (ι := ι ⊕ κ) ε (Sum.inr j) = ColumnFrames.standard (ι := ι ⊕ κ) ε (Sum.inr j) :=
    by
      apply Subtype.ext
      change (blockInclusion (κ := κ) A •
        (Pi.single (Sum.inr j) 1 : ι ⊕ κ → R)) = Pi.single (Sum.inr j) 1
      exact block_smul_right A j
  rw [he]
  exact hU j

end SourceBurnside.Stability.MatrixK1

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_LocallyFiniteActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.UnorderedStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical MatrixGenerators MatrixK1
open scoped Pointwise
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5 ≤ Fintype.card ι)

include hI hι in
lemma topBlock_mem (U : K (ι := ι) (κ := κ) ε) : topBlock ε U ∈ E := by
  apply (block_mem_iff (κ := κ) ε hI hι _).mp
  have hf : (fixedPart ε U).val ∈ E := E.mul_mem U.val.property
    (by exact permutation_mem _)
  rw [rightFixer_decomposition] at hf
  exact (E.mul_mem_cancel_right (rectangle_mem _)).mp hf

def projection : K (ι := ι) (κ := κ) ε →* E (R := R) (ι := ι) :=
  (projectionGL ε).codRestrict E (topBlock_mem ε hI hι)

def quotientMap : K (ι := ι) (κ := κ) ε →* E (R := R) (ι := ι) × Equiv.Perm κ :=
  (projection ε hI hι).prod (perm ε)

lemma section_topBlock (A : E (R := R) (ι := ι)) (p : Equiv.Perm κ) :
    topBlock ε (sectionElement ε A p) = A.val := by
  apply Units.ext
  ext i j
  rw [topBlock_entry]
  change (blockInclusion A.val * permRight p).val (Sum.inl i) (Sum.inl j) = _
  rw [Units.val_mul,permRight_eq,mul_permutation]
  rfl

lemma quotientMap_surjective : Function.Surjective (quotientMap (κ := κ) ε hI hι) := by
  rintro ⟨A,p⟩
  refine ⟨sectionElement ε A p,?_⟩
  apply Prod.ext
  · exact Subtype.ext (section_topBlock ε A p)
  · exact section_perm ε A p

lemma kernel_shape (U : (quotientMap (κ := κ) ε hI hι).ker) :
    U.val.val.val.val = Matrix.fromBlocks 1 0
      (U.val.val.val.val.submatrix Sum.inr Sum.inl) 1 := by
  have h := MonoidHom.mem_ker.mp U.property
  have ha : topBlock ε U.val = 1 := congrArg (fun x : E (R := R) (ι := ι) × Equiv.Perm κ => x.1.val) h
  have hp : perm ε U.val = 1 := congrArg Prod.snd h
  rw [shape ε U.val,ha,hp,map_one]
  rfl

def strip : (quotientMap (κ := κ) ε hI hι).ker →* Multiplicative (Matrix κ ι R) where
  toFun U := Multiplicative.ofAdd (U.val.val.val.val.submatrix Sum.inr Sum.inl)
  map_one' := by
    apply (Multiplicative.toAdd : Multiplicative (Matrix κ ι R) ≃ Matrix κ ι R).injective
    ext i j
    simp
  map_mul' U V := by
    apply (Multiplicative.toAdd : Multiplicative (Matrix κ ι R) ≃ Matrix κ ι R).injective
    ext i j
    change (U.val.val.val.val * V.val.val.val.val) (Sum.inr i) (Sum.inl j) = _
    rw [kernel_shape ε hI hι U,kernel_shape ε hI hι V,Matrix.fromBlocks_multiply]
    simp

lemma strip_injective : Function.Injective (strip (κ := κ) ε hI hι) := by
  intro U V h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [kernel_shape ε hI hι U,kernel_shape ε hI hι V]
  exact congrArg (fun B => Matrix.fromBlocks (1 : Matrix ι ι R) 0 B (1 : Matrix κ κ R))
    (congrArg Multiplicative.toAdd h)

lemma kernel_locallyFinite : LocallyFinite (quotientMap (κ := κ) ε hI hι).ker :=
  LocallyFinite.of_injective _ (strip_injective ε hI hι) (LocallyFinite.vector2 _)

end SourceBurnside.Stability.UnorderedStabilizer

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Homology_FiniteNormalHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
namespace FrameStabilizer
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)]

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5 ≤ Fintype.card ι)

attribute [local instance] OAI.SourceBurnside.Stability.FrameStabilizer.instMulActionSubtypeUnitsMatrixSumMemSubgroupGIndex
include hI hι in
lemma transitive (x : index (ι := ι) (κ := κ) ε) :
    ∃g : G (R := R) (ι := ι) (κ := κ), g • base (ι := ι) (κ := κ) ε = x := by
  let : Fintype x.val := Fintype.ofFinset x.val (fun _ => Iff.rfl)
  let e : κ ≃ x.val := Fintype.equivOfCardEq (by simpa using x.property.1.symm)
  let v : κ → V (ι := ι) (κ := κ) ε := fun j => (e j).val
  have hi : LinearIndependent (ZMod 2) (rho ε ∘ v) :=
    x.property.2.comp e e.injective
  obtain ⟨g,hg⟩ := MatrixK1.ordered_transitive ε hI hι v hi
  refine ⟨g,Subtype.ext ?_⟩
  apply Finset.coe_injective
  rw [Frames.indexAction_val,Finset.coe_image,base_coe,←Set.range_comp]
  change Set.range (fun j : κ => g • right ε j) = (x.val : Set (V (ι := ι) (κ := κ) ε))
  have he : (fun j : κ => g • right ε j) = v := funext hg
  rw [he]
  ext w
  constructor
  · rintro ⟨j,rfl⟩; exact (e j).property
  · intro hw
    use e.symm ⟨w,hw⟩
    change (e (e.symm ⟨w,hw⟩)).val = w
    rw [e.apply_symm_apply]

end FrameStabilizer
end SourceBurnside.Stability

namespace SourceBurnside.Stability.FrameStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)]

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5≤Fintype.card ι)

include hI hι in
lemma characterK_homology_isZero (hκ : 2≤Fintype.card κ) (n : ℕ) :
    IsZero (groupHomology (scalarRep (characterK (ι := ι) (κ := κ) ε)) n) := by
  let q := UnorderedStabilizer.quotientMap (κ := κ) ε hI hι
  let χ : E (R := R) (ι := ι) × Equiv.Perm κ →* ℚˣ :=
    (characterP (ι := ι) ε).comp (MonoidHom.snd _ _)
  have he : characterK (ι := ι) (κ := κ) ε = χ.comp q := (characterP_comp ε).symm
  rw [he]
  have : Nontrivial κ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i,j,hij⟩ := exists_pair_ne κ
  have hz := SignHomology.product_isZero χ (Equiv.swap i j) (characterP_swap ε i j hij) n
  have := RelativeCoinvariants.surjective_map_isIso q
    (UnorderedStabilizer.quotientMap_surjective ε hI hι)
    (UnorderedStabilizer.kernel_locallyFinite ε hI hι) (scalarRep χ) n
  exact hz.of_iso (asIso (groupHomology.map q (𝟙 (Rep.res q (scalarRep χ))) n))

attribute [local instance] OAI.SourceBurnside.Stability.FrameStabilizer.instMulActionSubtypeUnitsMatrixSumMemSubgroupGIndex_1
include hI hι in
lemma characterS_homology_isZero (hκ : 2≤Fintype.card κ) (n : ℕ) :
    IsZero (groupHomology (scalarRep (characterS (ι := ι) (κ := κ) ε)) n) := by
  let e := stabilizerEquiv (ι := ι) (κ := κ) ε
  let j := groupHomology.mapIso (A := scalarRep (characterS ε)) (B := scalarRep (characterK ε))
    e (LinearEquiv.refl ℚ ℚ) (fun s => by
      apply LinearMap.ext
      intro a
      change (characterS ε s).val * a = (characterS ε (e.symm (e s))).val * a
      rw [e.symm_apply_apply]) n
  exact (characterK_homology_isZero ε hI hι hκ n).of_iso j

include hI hι in
lemma chains_homology_isZero (hκ : 2≤Fintype.card κ) (n : ℕ) :
    IsZero (groupHomology (A (ι := ι) (κ := κ) ε) n) := by
  let x := base (ι := ι) (κ := κ) ε
  let S := MulAction.stabilizer (G (R := R) (ι := ι) (κ := κ)) x
  let χ := characterS (ι := ι) (κ := κ) ε
  let f := MonomialInduction.induced x (A ε) (b ε) χ
    (MonomialInduction.character_spec x (A ε) (b ε) (monomial ε))
  have := MonomialInduction.induced_isIso x (A ε) (b ε) χ
    (MonomialInduction.character_spec x (A ε) (b ε) (monomial ε))
    (transitive ε hI hι) (monomial ε)
  have := ShapiroMap.map_isIso S (scalarRep χ) n
  let j := asIso (groupHomology.map S.subtype (ShapiroMap.unit S (scalarRep χ)) n)
  have hz : IsZero (groupHomology (Rep.ind S.subtype (scalarRep χ)) n) :=
    (characterS_homology_isZero ε hI hι hκ n).of_iso j.symm
  exact hz.of_iso (((groupHomology.functor ℚ (G (R := R) (ι := ι) (κ := κ)) n).mapIso (asIso f)).symm)

end SourceBurnside.Stability.FrameStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory CategoryTheory.Limits MatrixK1
namespace H2FrameEdge
variable {R Ω : Type} [Ring R] [Algebra (ZMod 2) R] [Fintype Ω] [DecidableEq Ω]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
variable [LinearOrder (ColumnFrames.Vertex (ι := Ω) ε)]

include hI in
lemma chains_acyclic (hΩ : 13≤Fintype.card Ω) (k : ℕ) (hk : 2≤k) (hk' : k≤4) (n : ℕ) :
    IsZero (groupHomology (chains (Ω := Ω) ε k) n) := by
  have hkn : k≤Fintype.card Ω := by omega
  let L := Fin (Fintype.card Ω-k)
  let K := Fin k
  let e : L ⊕ K ≃ Ω := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum,Fintype.card_fin,L,K]
    omega)
  let : LinearOrder (ColumnFrames.Vertex (ι := L ⊕ K) ε) := linearOrderOfSTO WellOrderingRel
  have hl : 5≤Fintype.card L := by simp only [L,Fintype.card_fin]; omega
  have hz := FrameStabilizer.chains_homology_isZero (ι := L) (κ := K) ε hI hl
    (by simpa only [K,Fintype.card_fin] using hk) n
  have hz' : IsZero (groupHomology (Frames.chainRep (E (R := R) (ι := L ⊕ K))
      (ρ := ColumnFrames.rho ε) (ColumnRelabel.independent_action ε) k) n) := by
    simpa only [FrameStabilizer.A,FrameStabilizer.rho,K,Fintype.card_fin] using hz
  exact hz'.of_iso (ColumnRelabel.homologyIso ε e k n).symm

include hI in
lemma augmentation_isIso (hΩ : 13≤Fintype.card Ω) :
    IsIso (groupHomology.map (B := Rep.trivial ℚ (E (R := R) (ι := Ω)) ℚ)
      (MonoidHom.id (E (R := R) (ι := Ω))) (augmentation ε) 2) := by
  let C := Frames.repComplex (E (R := R) (ι := Ω)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε)
  have hrank : 10<Module.finrank (ZMod 2) (Ω → ZMod 2) := by simpa using (show 10<Fintype.card Ω by omega)
  have hepi : Epi (C.d 1 0) := by
    rw [Frames.repComplex_d]
    exact Frames.differentialRep_epi _ _ _ (ColumnFrames.rho_spanning ε) hrank
  have hex : ∀i : Fin 3, (C.sc' (i.val+2) (i.val+1) i.val).Exact :=
    fun i => Frames.repComplex_exact _ _ _ (ColumnFrames.rho_spanning ε) hrank i.val (by omega)
  have hacyc : ∀i : Fin 3, ∀q, IsZero (groupHomology (C.X (i.val+2)) q) :=
    fun i q => chains_acyclic ε hI hΩ (i.val+2) (by omega) (by omega) q
  have hi := HomologyEdge.isIso_H2_augmentation C hepi hex hacyc
  have : IsIso (groupHomology.map (B := chains (Ω := Ω) ε 0) (MonoidHom.id _) (Frames.differentialRep
      (E (R := R) (ι := Ω)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε) 0) 2) := by
    simpa only [C,Frames.repComplex_d] using! hi
  have : IsIso (groupHomology.map (B := Rep.trivial ℚ (E (R := R) (ι := Ω)) ℚ)
      (MonoidHom.id _) (Frames.degreeZeroIso (E (R := R) (ι := Ω)) (ColumnFrames.rho ε)
        (ColumnRelabel.independent_action ε)).hom 2) := by
    change IsIso ((groupHomology.functor (k := ℚ) (G := E (R := R) (ι := Ω)) 2).map _)
    infer_instance
  rw [augmentation,groupHomology.map_id_comp]
  infer_instance

end H2FrameEdge
end SourceBurnside.Stability

namespace SourceBurnside.Stability.UnorderedStabilizer
open Classical MatrixGenerators MatrixK1 CategoryTheory
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

lemma complementary_val (A : E (R := R) (ι := ι)) :
    (complementary (ι := ι) (κ := κ) ε A).val.val = blockInclusion A.val := by
  change blockInclusion A.val * permRight 1 = _
  simp

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5≤Fintype.card ι)

lemma projection_complementary : (projection (κ := κ) ε hI hι).comp (complementary ε) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro A
  exact Subtype.ext (section_topBlock ε A 1)

lemma projection_surjective : Function.Surjective (projection (κ := κ) ε hI hι) := by
  intro A
  exact ⟨complementary ε A,congrArg (fun f : E (R := R) (ι := ι) →* E => f A)
    (projection_complementary ε hI hι)⟩

variable [Subsingleton κ]

lemma projection_kernel_eq : (projection (κ := κ) ε hI hι).ker = (quotientMap ε hI hι).ker := by
  ext s
  rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
  change projection ε hI hι s=1 ↔ (projection ε hI hι s,perm ε s) = (1,1)
  simp only [Prod.mk.injEq,Subsingleton.elim (perm ε s) 1,and_true]

lemma projection_locallyFinite : LocallyFinite (projection (κ := κ) ε hI hι).ker := by
  rw [projection_kernel_eq]
  exact kernel_locallyFinite ε hI hι

include hI hι in
lemma complementary_homology_isIso (n : ℕ) :
    IsIso (RationalHomology.map (complementary (ι := ι) (κ := κ) ε) n) := by
  let i := RationalHomology.map (complementary (ι := ι) (κ := κ) ε) n
  let p := RationalHomology.map (projection (κ := κ) ε hI hι) n
  have : IsIso p := RationalHomology.surjective_isIso (projection ε hI hι)
    (projection_surjective ε hI hι) (projection_locallyFinite ε hI hι) n
  have he : i ≫ p = 𝟙 _ := by
    rw [←RationalHomology.map_comp,projection_complementary,RationalHomology.map_id]
  have hi : i = inv p := by
    rw [←Category.comp_id i,←IsIso.hom_inv_id p,←Category.assoc,he,Category.id_comp]
  change IsIso i
  rw [hi]
  infer_instance

end SourceBurnside.Stability.UnorderedStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory MatrixGenerators MatrixK1 Representation

namespace SingletonFrameEdge
variable {R ι : Type} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ Fin 1) ε)]
local notation "G" => E (R := R) (ι := ι ⊕ Fin 1)
local notation "x₀" => FrameStabilizer.base (ι := ι) (κ := Fin 1) ε
local notation "S" => MulAction.stabilizer G x₀
local notation "A" => FrameStabilizer.A (ι := ι) (κ := Fin 1) ε
local notation "b" => FrameStabilizer.b (ι := ι) (κ := Fin 1) ε

attribute [local instance] OAI.SourceBurnside.Stability.SingletonFrameEdge.instMulActionSubtypeUnitsMatrixSumFinOfNatNatMemSubgroupEIndex
lemma fixed (s : S) : (A).ρ s.val (b x₀) = b x₀ := by
  apply Subtype.ext
  change Frames.labelMap (s.val • ·) (b x₀).val = (b x₀).val
  rw [Frames.frameBasis_val]
  apply Frames.labelMap_basis_fixed
  intro v hv
  rw [base_singleton] at hv
  have he : v = FrameStabilizer.right (ι := ι) ε (0 : Fin 1) := Finset.mem_singleton.mp hv
  subst v
  let k := FrameStabilizer.stabilizerEquiv (ι := ι) (κ := Fin 1) ε s
  have h := UnorderedStabilizer.perm_spec ε k (0 : Fin 1)
  rw [Subsingleton.elim (UnorderedStabilizer.perm ε k 0) 0] at h
  simpa only [k,FrameStabilizer.stabilizerEquiv,MulEquiv.subgroupCongr_apply,
    FrameStabilizer.right,Subgroup.smul_def] using! h

abbrev seed := MonomialTrivial.seed x₀ A b (fixed (ι := ι) ε)

lemma blockHom_val (g : E (R := R) (ι := ι)) : (blockHom (ι := ι) ε g).val = blockInclusion g.val :=
  UnorderedStabilizer.complementary_val ε g

lemma seed_augmentation (a : ℚ) :
    (H2FrameEdge.augmentation (Ω := ι ⊕ Fin 1) ε).hom ((seed (ι := ι) ε).hom a) = a := by
  change Frames.basis.repr (Frames.boundary _ (a • (b x₀).val)) ∅ = a
  rw [map_smul,Frames.frameBasis_val,base_singleton,Frames.basis_singleton,Frames.boundary_vertex]
  rw [←Frames.basis_empty,map_smul,Module.Basis.repr_self]
  simp

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 12≤Fintype.card ι)

include hI hι in
lemma lift_homology_isIso (n : ℕ) : IsIso (RationalHomology.map (lift (ι := ι) ε) n) := by
  have hComplement := UnorderedStabilizer.complementary_homology_isIso (κ := Fin 1) ε hI (by omega : 5≤Fintype.card ι) n
  have hRelabel := RationalHomology.equiv_isIso (FrameStabilizer.stabilizerEquiv (ι := ι) (κ := Fin 1) ε).symm n
  erw [lift,RationalHomology.map_comp]
  exact IsIso.comp_isIso' hComplement hRelabel

include hI hι in
lemma seed_homology_isIso (n : ℕ) : IsIso (groupHomology.map (B := A) (S).subtype (seed (ι := ι) ε) n) :=
  MonomialTrivial.seed_homology_isIso x₀ A b (fixed (ι := ι) ε)
    (FrameStabilizer.transitive ε hI (by omega)) (FrameStabilizer.monomial ε) n

lemma composite (n : ℕ) : RationalHomology.map (blockHom (ι := ι) ε) n =
    RationalHomology.map (lift (ι := ι) ε) n ≫ groupHomology.map (B := A) (S).subtype (seed (ι := ι) ε) n ≫
      groupHomology.map (B := Rep.trivial ℚ G ℚ) (MonoidHom.id G) (H2FrameEdge.augmentation (Ω := ι ⊕ Fin 1) ε) n := by
  exact trivial_map_factorization (lift (ι := ι) ε) (S).subtype A (seed (ι := ι) ε)
    (H2FrameEdge.augmentation (Ω := ι ⊕ Fin 1) ε) (seed_augmentation ε) n

include hI hι in
lemma block_h2_isIso : IsIso (RationalHomology.map (blockHom (ι := ι) ε) 2) := by
  have hLift := lift_homology_isIso ε hI hι 2
  have hSeed := seed_homology_isIso ε hI hι 2
  have hAugmentation := H2FrameEdge.augmentation_isIso (Ω := ι ⊕ Fin 1) ε hI (by simpa using hι)
  rw [composite]
  exact IsIso.comp_isIso' hLift (IsIso.comp_isIso' hSeed hAugmentation)

end SingletonFrameEdge
end SourceBurnside.Stability

end

end OAI
end

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_RankActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SourceBurnside.Stability.ElementaryRanks
open Classical CategoryTheory MatrixGenerators MatrixK1
variable {R : Type} [Ring R]

lemma representation_surjective (n : ℕ) : Function.Surjective (representation (R := R) (n := n)) := by
  rintro ⟨g,hg⟩
  change g∈E at hg
  rw [←representation_range (R := R) n] at hg
  obtain ⟨u,rfl⟩ := hg
  exact ⟨u,rfl⟩

lemma rep_kernel {n : ℕ} : (representation (R := R) (n := n)).ker = Elementary.representation.ker := by
  ext u
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

variable [Algebra (ZMod 2) R] (ε : R →ₐ[ZMod 2] ZMod 2)

lemma next_root {n : ℕ} (p : Root n) (a : R) : next ε n (root p a) =
    root ⟨Fin.castSucc p.row,Fin.castSucc p.col,(Fin.castSucc_injective n).ne p.ne⟩ a := by
  let : LinearOrder (ColumnFrames.Vertex (ι := Fin n ⊕ Fin 1) ε) := linearOrderOfSTO WellOrderingRel
  apply Subtype.ext
  change relabel finSumFinEquiv (SingletonFrameEdge.blockHom ε (root p a)).val = _
  rw [SingletonFrameEdge.blockHom_val,root_val,blockInclusion_elementary,relabel_elementary,root_val]
  congr 1

lemma next_representation {n : ℕ} : (next ε n).comp representation =
    (representation (R := R)).comp (Steinberg.coordinateMap Fin.castSucc (Fin.castSucc_injective n)) := by
  apply Steinberg.hom_ext
  intro p a
  simpa only [MonoidHom.comp_apply,Steinberg.coordinateMap_x,root,Root.map] using next_root ε p a

lemma next_h2_isIso (hI : MatrixNilKernel ε.toRingHom) (n : ℕ) (hn : 12≤n) :
    IsIso (RationalHomology.map (next ε n) 2) := by
  let : LinearOrder (ColumnFrames.Vertex (ι := Fin n ⊕ Fin 1) ε) := linearOrderOfSTO WellOrderingRel
  have := SingletonFrameEdge.block_h2_isIso (ι := Fin n) ε hI (by simpa using hn)
  have := RationalHomology.equiv_isIso (ColumnRelabel.elementaryEquiv
    (R := R) (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n+1))) 2
  rw [next,RationalHomology.map_comp]
  infer_instance

end SourceBurnside.Stability.ElementaryRanks

namespace SourceBurnside.Stability

open Classical
namespace RationalExtension
variable {X G : Type} [Group X] [Group G] (S : RationalExtension X G)

def finiteOrderLift (g : G) (hg : IsOfFinOrder g) : X :=
  letI : Finite (Subgroup.zpowers g) := hg.finite_zpowers
  S.liftFinite (Subgroup.zpowers g) ⟨g,Subgroup.mem_zpowers g⟩

lemma finiteOrderLift_projection (g : G) (hg : IsOfFinOrder g) : S.rightHom (S.finiteOrderLift g hg)=g := by
  let : Finite (Subgroup.zpowers g) := hg.finite_zpowers
  exact S.rightHom_liftFinite (Subgroup.zpowers g) _
lemma finiteOrderLift_torsion (g : G) (hg : IsOfFinOrder g) : IsOfFinOrder (S.finiteOrderLift g hg) := by
  let : Finite (Subgroup.zpowers g) := hg.finite_zpowers
  exact S.liftFinite_finite_order (Subgroup.zpowers g) _
end RationalExtension
namespace ExtensionRootLift
open ElementaryRanks
variable {R : Type} [Ring R] [Algebra (ZMod 2) R]
variable {n : ℕ}

lemma x_sq (p : Root n) (a : R) : (Steinberg.x p a)^2=1 := by
  rw [pow_two,←Steinberg.x_add,add_self_zero,Steinberg.x_zero]
lemma root_sq (p : Root n) (a : R) : (root p a)^2=1 := by
  rw [root,←map_pow,x_sq,map_one]
lemma root_torsion (p : Root n) (a : R) : IsOfFinOrder (root p a) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,root_sq p a⟩
omit [Algebra (ZMod 2) R] in
lemma root_add (p : Root n) (a b : R) : root p (a+b)=root p a*root p b := by
  simp only [root,Steinberg.x_add,map_mul]
omit [Algebra (ZMod 2) R] in
lemma root_commute (p q : Root n) (h1 : p.col≠q.row) (h2 : p.row≠q.col) (a b : R) :
    Commute (root p a) (root q b) := (Steinberg.x_commute p q h1 h2 a b).map representation
omit [Algebra (ZMod 2) R] in
lemma root_same_commute (p : Root n) (a b : R) : Commute (root p a) (root p b) := by
  show root p a*root p b=root p b*root p a
  rw [←root_add,←root_add,add_comm]
omit [Algebra (ZMod 2) R] in
lemma root_mul (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    bracket (root ⟨i,j,hij⟩ a) (root ⟨j,k,hjk⟩ b) = root ⟨i,k,hik⟩ (a*b) := by
  simpa only [root,map_bracket] using congrArg representation (Steinberg.x_mul i j k hij hjk hik a b)

lemma consecutive_finite (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    Finite (Subgroup.closure ({root ⟨i,j,hij⟩ a,root ⟨j,k,hjk⟩ b} : Set (Group (R := R) n))) := by
  apply FiniteRootPairs.finite_pair _ _ (root_sq _ _) (root_sq _ _)
  have hi : (root ⟨i,j,hij⟩ a)⁻¹=root ⟨i,j,hij⟩ a :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using root_sq ⟨i,j,hij⟩ a)
  have hj : (root ⟨j,k,hjk⟩ b)⁻¹=root ⟨j,k,hjk⟩ b :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using root_sq ⟨j,k,hjk⟩ b)
  have he : (root ⟨i,j,hij⟩ a*root ⟨j,k,hjk⟩ b)^2=root ⟨i,k,hik⟩ (a*b) := by
    simpa only [bracket,hi,hj,pow_two,mul_assoc] using root_mul i j k hij hjk hik a b
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨4,by decide,?_⟩
  rw [show 4=2*2 by decide,pow_mul,he,root_sq]

lemma unique_over {X G : Type} [Group X] [Group G] (S : RationalExtension X G)
    (f g : Steinberg n R →* X) (h : S.rightHom.comp f=S.rightHom.comp g) : f=g := by
  apply Steinberg.hom_ext
  intro p a
  apply S.torsion_lift_unique
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by rw [←map_pow,x_sq,map_one]⟩
  · exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,by rw [←map_pow,x_sq,map_one]⟩
  · exact DFunLike.congr_fun h (Steinberg.x p a)

variable {X : Type} [Group X] (S : RationalExtension X (Group (R := R) n))

def lift (p : Root n) (a : R) : X := S.finiteOrderLift (root p a) (root_torsion p a)
lemma projection_lift (p : Root n) (a : R) : S.rightHom (lift S p a)=root p a :=
  S.finiteOrderLift_projection _ _
lemma lift_torsion (p : Root n) (a : R) : IsOfFinOrder (lift S p a) :=
  S.finiteOrderLift_torsion _ _
lemma lift_eq_finite (H : Subgroup (Group (R := R) n)) [Finite H] (p : Root n) (a : R)
    (h : root p a∈H) : lift S p a=S.liftFinite H ⟨root p a,h⟩ :=
  S.torsion_lift_unique (lift_torsion S p a) (S.liftFinite_finite_order H _)
    ((projection_lift S p a).trans (S.rightHom_liftFinite H ⟨root p a,h⟩).symm)

lemma lift_add (p : Root n) (a b : R) : lift S p (a+b)=lift S p a*lift S p b := by
  let H := Subgroup.closure ({root p a,root p b} : Set (Group (R := R) n))
  let : Finite H := FiniteRootPairs.finite_pair_commute _ _ (root_sq _ _) (root_sq _ _) (root_same_commute p a b)
  have ha : root p a∈H := Subgroup.subset_closure (by simp)
  have hb : root p b∈H := Subgroup.subset_closure (by simp)
  have hab : root p (a+b)∈H := root_add p a b ▸ H.mul_mem ha hb
  rw [lift_eq_finite S H p a ha,lift_eq_finite S H p b hb,lift_eq_finite S H p (a+b) hab,←map_mul]
  congr 1
  exact Subtype.ext (root_add p a b)

lemma lift_commute (p q : Root n) (h1 : p.col≠q.row) (h2 : p.row≠q.col) (a b : R) :
    Commute (lift S p a) (lift S q b) := by
  let H := Subgroup.closure ({root p a,root q b} : Set (Group (R := R) n))
  let : Finite H := FiniteRootPairs.finite_pair_commute _ _ (root_sq _ _) (root_sq _ _) (root_commute p q h1 h2 a b)
  have ha : root p a∈H := Subgroup.subset_closure (by simp)
  have hb : root q b∈H := Subgroup.subset_closure (by simp)
  rw [lift_eq_finite S H p a ha,lift_eq_finite S H q b hb]
  apply Commute.map
  exact Subtype.ext (root_commute p q h1 h2 a b).eq

lemma lift_mul (i j k : Fin n) (hij : i≠j) (hjk : j≠k) (hik : i≠k) (a b : R) :
    bracket (lift S ⟨i,j,hij⟩ a) (lift S ⟨j,k,hjk⟩ b) = lift S ⟨i,k,hik⟩ (a*b) := by
  let H := Subgroup.closure ({root ⟨i,j,hij⟩ a,root ⟨j,k,hjk⟩ b} : Set (Group (R := R) n))
  let : Finite H := consecutive_finite i j k hij hjk hik a b
  have ha : root ⟨i,j,hij⟩ a∈H := Subgroup.subset_closure (by simp)
  have hb : root ⟨j,k,hjk⟩ b∈H := Subgroup.subset_closure (by simp)
  let A : H := ⟨root ⟨i,j,hij⟩ a,ha⟩
  let B : H := ⟨root ⟨j,k,hjk⟩ b,hb⟩
  have he : S.liftFinite H (bracket A B)=lift S ⟨i,k,hik⟩ (a*b) :=
    S.torsion_lift_unique (S.liftFinite_finite_order H _) (lift_torsion S _ _)
      (by rw [S.rightHom_liftFinite,projection_lift]; exact root_mul i j k hij hjk hik a b)
  rw [←he,map_bracket,lift_eq_finite S H _ a ha,lift_eq_finite S H _ b hb]

def hom : Steinberg n R →* X := Steinberg.lift (lift S) (lift_add S) (lift_commute S) (lift_mul S)
@[simp] lemma hom_x (p : Root n) (a : R) : hom S (Steinberg.x p a)=lift S p a := Steinberg.lift_x ..
lemma hom_projection : S.rightHom.comp (hom S)=representation := by
  apply Steinberg.hom_ext
  intro p a
  change S.rightHom (hom S (Steinberg.x p a))=root p a
  rw [hom_x,projection_lift]

end ExtensionRootLift
end SourceBurnside.Stability

namespace SourceBurnside.Stability.SteinbergAction
section
open Classical Steinberg MatrixGenerators Kernel

variable {n : ℕ} {R : Type*} [Ring R]

lemma scale_strip (u : Fin n → Rˣ) (H L : Finset (Fin n)) (hd : Disjoint H L)
    {g : Steinberg n R} (hg : g∈Strip H L hd) : scale u g∈Strip H L hd := by
  have hh : Strip H L hd ≤ (Strip H L hd).comap (scale u).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨p,a,rfl⟩
    change scale u (x (rectPosition H L hd p) a) ∈ Strip H L hd
    rw [scale_x]
    exact Subgroup.subset_closure ⟨p,_,rfl⟩
  exact hh hg

lemma scale_preserves_strip (u : Fin n → Rˣ) (H L : Finset (Fin n)) (hd : Disjoint H L) :
    scale u∈preservers (Strip H L hd) := by
  intro g
  constructor
  · intro hg
    have hh := scale_strip (fun i => (u i)⁻¹) H L hd hg
    rw [←scale_inv] at hh
    change (scale u).symm (scale u g)∈Strip H L hd at hh
    simpa only [MulEquiv.symm_apply_apply] using hh
  · exact scale_strip u H L hd

lemma conj_preserves_column (t : Fin n) (p : Root n) (hpt : p.row≠t) (hct : p.col≠t) (a : R) :
    MulAut.conj (x p a)∈preservers (columnStrip t) := by
  have hh := away_le_column_normalizer (R := R) t
    (Subgroup.subset_closure ⟨p,a,hpt,hct,rfl⟩)
  intro g
  exact (Subgroup.mem_normalizer_iff.mp hh g).symm

lemma fixes_strip (f : MulAut (Steinberg n R))
    (hf : ∀g, Elementary.representation (f g) = Elementary.representation g)
    (H L : Finset (Fin n)) (hd : Disjoint H L) (hp : f∈preservers (Strip H L hd))
    {g : Steinberg n R} (hg : g∈Strip H L hd) : f g=g := by
  apply mul_inv_eq_one.mp
  apply strip_faithful H L hd ((Strip H L hd).mul_mem ((hp g).mpr hg) ((Strip H L hd).inv_mem hg))
  simp only [map_mul,map_inv,hf,mul_inv_cancel]

lemma identity_of_fixes_strips (t : Fin n) (f : MulAut (Steinberg n R))
    (hc : ∀g∈columnStrip t, f g=g) (hr : ∀g∈rowStrip t, f g=g) : f=1 := by
  have hh : f.toMonoidHom = MonoidHom.id _ := by
    apply Steinberg.hom_ext
    intro p a
    change f (x p a) = x p a
    by_cases hpt : p.row=t
    · have hp : p=⟨t,p.col,hpt ▸ p.ne⟩ := by cases p; cases hpt; rfl
      rw [hp]
      exact hr _ (row_root_mem t p.col (hpt ▸ p.ne) a)
    · by_cases hct : p.col=t
      · have hp : p=⟨p.row,t,hct ▸ p.ne⟩ := by cases p; cases hct; rfl
        rw [hp]
        exact hc _ (column_root_mem t p.row (hct ▸ p.ne) a)
      · have he := x_mul p.row t p.col hpt (Ne.symm hct) p.ne a (1:R)
        rw [mul_one] at he
        rw [←he]
        change f.toMonoidHom (bracket _ _) = bracket _ _
        rw [map_bracket]
        change bracket (f (x ⟨p.row,t,hpt⟩ a)) (f (x ⟨t,p.col,Ne.symm hct⟩ 1)) = _
        rw [hc _ (column_root_mem t p.row hpt a),hr _ (row_root_mem t p.col (Ne.symm hct) 1)]
  ext g
  exact DFunLike.congr_fun hh g

end

section
open Classical Steinberg MatrixGenerators Kernel
variable {n : ℕ} {R : Type*} [Ring R]

lemma supported_column (S : Finset (Fin n)) (t : Fin n) (ht : t∉S) :
    SmallPresentation.supported (R := R) S ≤ (preservers (columnStrip t)).comap wordAction := by
  apply (Subgroup.closure_le _).mpr
  rintro w ⟨g,hg,rfl⟩
  change generatorAction g∈preservers (columnStrip t)
  cases g with
  | root i j h a =>
    have hi : i∈S := hg (by simp [SmallPresentation.Generator.support])
    have hj : j∈S := hg (by simp [SmallPresentation.Generator.support])
    exact conj_preserves_column t ⟨i,j,h⟩ (fun he => ht (he ▸ hi)) (fun he => ht (he ▸ hj)) a
  | diag i u => exact scale_preserves_strip _ _ _ _

end

open Classical Steinberg MatrixGenerators

end SourceBurnside.Stability.SteinbergAction

end

end OAI
end


