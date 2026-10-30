-- Prove2me | Definitions.Def_OAIQ116Ta013
-- name    : OAIQ116Ta013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:59:56.351241+00:00
-- url     : https://prove2.me/theorems/a6624045-b910-40e0-8090-500f41cd62d1
-- title:
--   Definitions bundle OAIQ116Ta013 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 2 definitions, 3 instances and 2 theorems. The definitions and types are `OAI.Tachikawa.mappedCoresolutionCochainIso`, `OAI.Tachikawa.mappedCoresolutionCochainXIso`.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: [`Tachikawa_Coresolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Coresolution.lean), [`Tachikawa_Symmetry`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Symmetry.lean), [`Tachikawa_Triangular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/Tachikawa/Triangular.lean).
--
--   **Imports.** It imports the bundles `OAIQ116Ta017` and `OAIQ116Ta007` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.Tachikawa.SourceField.sourceDelta_bijective`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ116Ta017
import Definitions.Def_OAIQ116Ta007

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Symmetry
attribute [-instance] _root_.OAI.Tachikawa.Construction.instModuleEX _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.TrivialInduction.inducedProjective _root_.OAI.Tachikawa.TrivialInduction.instAdditiveModuleCatTrivialExtensionFunctor _root_.OAI.Tachikawa.TrivialInduction.instIsScalarTowerTrivialExtensionObj _root_.OAI.Tachikawa.TrivialInduction.instModuleTrivialExtensionObj _root_.OAI.Tachikawa.TrivialInduction.instProjectiveTrivialExtensionObjForallFin _root_.OAI.Tachikawa.TrivialInflation.instIsScalarTowerTrivialExtension _root_.OAI.Tachikawa.TrivialInflation.instModuleTrivialExtension _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa



variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

namespace TrivialExtension

instance instInjectiveOfFiniteDimensional [FiniteDimensional k R] : Module.Injective (TrivialExtension k R) (TrivialExtension k R) :=
  symmetrizingForm.injective

end TrivialExtension
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
attribute [-instance] _root_.OAI.Tachikawa.LeftCoinduced.coextend_additive _root_.OAI.Tachikawa.LeftCoinduced.coextend_preservesInjective _root_.OAI.Tachikawa.OuterTensor.restrictionPreservesHomology _root_.OAI.Tachikawa.TotalDualPairing.instTensorSignsNatUp_solutions _root_.OAI.Tachikawa.TotalMap.sourceHasCoproduct _root_.OAI.Tachikawa.downIntTensorSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
  {Y : C} (P : InjectiveResolution Y)

def mappedCoresolutionCochainXIso (j : ℤ) :
    (mappedCoresolution F P).cochainComplex.X j ≅ F.obj (P.cochainComplex.X j) := by
  by_cases h : 0 ≤ j
  · let n := j.toNat
    have hn : (n : ℤ) = j := by dsimp [n]; omega
    exact (mappedCoresolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm
  · exact (CochainComplex.isZero_of_isStrictlyGE (mappedCoresolution F P).cochainComplex 0 j).isoZero ≪≫
      (F.map_isZero (CochainComplex.isZero_of_isStrictlyGE P.cochainComplex 0 j)).isoZero.symm

lemma mappedCoresolutionCochainXIso_nonneg (j : ℤ) (n : ℕ) (hn : (n : ℤ) = j) :
    mappedCoresolutionCochainXIso F P j =
      (mappedCoresolution F P).cochainComplexXIso j n hn ≪≫
      (F.mapIso (P.cochainComplexXIso j n hn)).symm := by
  have hj : 0 ≤ j := by omega
  simp only [mappedCoresolutionCochainXIso,dite_eq_left hj]
  have : j.toNat = n := by omega
  subst n
  rfl

lemma mappedCoresolutionCochainXIso_comm (i j : ℤ) :
    (mappedCoresolution F P).cochainComplex.d i j ≫ (mappedCoresolutionCochainXIso F P j).hom =
      (mappedCoresolutionCochainXIso F P i).hom ≫ F.map (P.cochainComplex.d i j) := by
  by_cases hi : 0 ≤ i
  · by_cases hj : 0 ≤ j
    · obtain ⟨a,rfl⟩ := Int.eq_ofNat_of_zero_le hi
      obtain ⟨b,rfl⟩ := Int.eq_ofNat_of_zero_le hj
      rw [mappedCoresolutionCochainXIso_nonneg F P _ a rfl,
        mappedCoresolutionCochainXIso_nonneg F P _ b rfl,
        InjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl,
        InjectiveResolution.cochainComplex_d _ _ _ a b rfl rfl]
      dsimp only [mappedCoresolution]
      simp only [Iso.trans_hom,Iso.symm_hom,Functor.mapIso_inv,Functor.map_comp,
        Category.assoc,Iso.inv_hom_id_assoc]
      rw [← F.map_comp_assoc,Iso.inv_hom_id,F.map_id,Category.id_comp]
      rfl
    · exact (F.map_isZero (CochainComplex.isZero_of_isStrictlyGE P.cochainComplex 0 j)).eq_of_tgt _ _
  · exact (CochainComplex.isZero_of_isStrictlyGE (mappedCoresolution F P).cochainComplex 0 i).eq_of_src _ _

def mappedCoresolutionCochainIso : (mappedCoresolution F P).cochainComplex ≅
    (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex :=
  HomologicalComplex.Hom.isoOfComponents (mappedCoresolutionCochainXIso F P)
    (fun i j _ => (mappedCoresolutionCochainXIso_comm F P i j).symm)

open CochainComplex CochainComplex.HomComplex
end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Triangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

instance instSMulCommClassProdOff (F : ModuleCat (Enveloping.Alg k R R)) : SMulCommClass k (R × R) (Off F) where
  smul_comm c a x := smul_comm c a.2 (show Enveloping.Obj F from x)
instance instSMulCommClassMulOppositeProdOff (F : ModuleCat (Enveloping.Alg k R R)) : SMulCommClass k (R × R)ᵐᵒᵖ (Off F) where
  smul_comm c a x := smul_comm c (MulOpposite.op a.unop.1) (show Enveloping.Obj F from x)

end Tachikawa.Triangular



end

end OAI
end


