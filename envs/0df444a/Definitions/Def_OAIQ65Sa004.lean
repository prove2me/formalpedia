-- Prove2me | Definitions.Def_OAIQ65Sa004
-- name    : OAIQ65Sa004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:33:16.530643+00:00
-- url     : https://prove2.me/theorems/3487de9a-f29f-454b-8d98-3dce47df195d
-- title:
--   Definitions bundle OAIQ65Sa004 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 578 declarations of OpenAI's Lean: 169 definitions, 42 instances and 367 theorems. The definitions and types are `OAI.BarFinitePower.doublePowerComparison`, `OAI.BarFinitePower.doubleRowComparison`, `OAI.BarFinitePower.firstDoubleRowHomologyIso`, `OAI.BarFinitePower.firstRowHomologyIso`, `OAI.BarFinitePower.powerOneIso`, `OAI.BarFinitePower.powerTwoIso`, `OAI.BarFinitePower.singlePowerComparison`, `OAI.BarFinitePower.singleProject`, `OAI.BarFinitePower.singleRowComparison`, `OAI.BarFinitePower.triplePowerComparison`, `OAI.BarFinitePower.tripleProject`, `OAI.BarHomology.rowIso`, `OAI.BarHomology.zeroRowIso`, `OAI.CoefficientNerve.constIso`, `OAI.CoefficientNerve.constant`, `OAI.CoefficientNerve.constantComplexIso`, `OAI.CoefficientNerve.constantSimplicialIso`, `OAI.CoefficientNerve.rowIso`, `OAI.CommMonoidOpposite.homologyIso`, `OAI.ComponentCoproduct.homologyIsColimit`, `OAI.ComponentStable.H`, `OAI.ComponentStable.binaryD`, `OAI.ComponentStable.inclusion`, `OAI.ComponentStable.object`, `OAI.ComponentStable.pullD`, `OAI.ComponentStable.toStable`, `OAI.ComponentStable.unionCocone`, `OAI.ComponentTranslation.homologyDiagram`, `OAI.ConnectedProduct.redInclusion`, `OAI.ConnectedProduct.redProjection`, `OAI.ConstantSplit.inclusionIso`, `OAI.ConstantSplit.redMap`, `OAI.DoubleCoordinates.words`, `OAI.E2Leading.descendedLead`, `OAI.EilenbergZilber.equiv`, `OAI.EilenbergZilber.homologyIso`, `OAI.EilenbergZilber.twoIso`, `OAI.FilteredEdge.Data.boundaryCycle`, `OAI.FilteredEdge.Data.boundaryMap`, `OAI.FilteredEdge.Data.current` and 129 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Homology_BinaryPullback`, `SimpleAmenable_Homology_ComponentStable`, `SimpleAmenable_Homology_ConcreteHomology`, `SimpleAmenable_Homology_ConeHomology`, `SimpleAmenable_Homology_DoubleCoordinates`, `SimpleAmenable_Homology_E2Descend`, `SimpleAmenable_Homology_ExactShapeHomology`, `SimpleAmenable_Homology_Face200`, `SimpleAmenable_Homology_Face410`, `SimpleAmenable_Homology_FilteredEdgeReturn`, `SimpleAmenable_Homology_GroupoidComponentHomology`, `SimpleAmenable_Homology_MarkedBlockDifferentials`, `SimpleAmenable_Homology_MarkedGradedFinite`, `SimpleAmenable_Homology_MarkedLowHomology`, `SimpleAmenable_Homology_MarkedPrimitiveFaces`, `SimpleAmenable_Homology_MarkedSigns`, `SimpleAmenable_Homology_PiH1Coproduct`, `SimpleAmenable_Homology_PiSSet`, `SimpleAmenable_Homology_PowerEquivalence`, `SimpleAmenable_Homology_ProductChains`, `SimpleAmenable_Homology_ProductNatural`, `SimpleAmenable_Homology_ReducedNatural`, `SimpleAmenable_Homology_ReducedTensorFinite`, `SimpleAmenable_Homology_ReducedTensorTwo`, `SimpleAmenable_Homology_RegularBlock`, `SimpleAmenable_Homology_RegularCoefficientDouble`, `SimpleAmenable_Homology_RegularLiftFaces`, `SimpleAmenable_Homology_RegularTotalDifferential`, `SimpleAmenable_Homology_RegularTotalFiniteDifferentials`, `SimpleAmenable_Homology_TotalComparison`, `SimpleAmenable_Homology_TotalFiniteness`, `SimpleAmenable_Homology_TotalProjection`, `SimpleAmenable_Simplicial_BarComponents`, `SimpleAmenable_Simplicial_BarContractible`, `SimpleAmenable_Simplicial_BarRowFiniteness`, `SimpleAmenable_Simplicial_CoefficientNaturality`, `SimpleAmenable_Simplicial_ConstantCoefficient`, `SimpleAmenable_Simplicial_DiagonalComparison`, `SimpleAmenable_Simplicial_DiagramResolutionNatural`, `SimpleAmenable_Simplicial_EilenbergZilber`, `SimpleAmenable_Simplicial_FinitePowerGeneral`, `SimpleAmenable_Simplicial_FirstBarComponentsFinite`, `SimpleAmenable_Simplicial_GroupNerveCoordinates`, `SimpleAmenable_Simplicial_Id`, `SimpleAmenable_Simplicial_InducedMonoidal`, `SimpleAmenable_Simplicial_IntervalBinary`, `SimpleAmenable_Simplicial_IntervalEdge`, `SimpleAmenable_Simplicial_IntervalEquivalence`, `SimpleAmenable_Simplicial_IntervalEssSurj`, `SimpleAmenable_Simplicial_IntervalFunctor`, `SimpleAmenable_Simplicial_IntervalTensor`, `SimpleAmenable_Simplicial_IteratedBarMaps`, `SimpleAmenable_Simplicial_LowerBarComposition`, `SimpleAmenable_Simplicial_MonoidalCongruence`, `SimpleAmenable_Simplicial_NerveProduct`, `SimpleAmenable_Simplicial_NestedPosReindex`, `SimpleAmenable_Simplicial_PiFiber`, `SimpleAmenable_Simplicial_PositionalInclusionMonoidal`, `SimpleAmenable_Simplicial_PowerDiagonal`, `SimpleAmenable_Simplicial_RegularBlockFaces`, `SimpleAmenable_Simplicial_RestrictedFunctorial`, `SimpleAmenable_Simplicial_RestrictedMonoidal`, `SimpleAmenable_Simplicial_RestrictedMonoidalTranspose`, `SimpleAmenable_Simplicial_SimplicialH0`, `SimpleAmenable_Simplicial_StageRefinementMonoidal`, `SimpleAmenable_Simplicial_TripleBarMaps`, `SimpleAmenable_Simplicial_TripleComposition`, `SimpleAmenable_Simplicial_TripleReindex`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa000` and `OAIQ65Sa001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa007`, `OAIQ65Sa008`, `OAIQ65Sa009`, `OAIQ65Sa013` and `OAIQ65Sa014`; the statements `OAI_SimpleAmenable_polygonFullGroup_finiteTestReiter`, `OAI_SimpleAmenable_polygon_central_cover` and `OAI_SimpleAmenable_source_aligned_disjoint_eventually`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa000
import Definitions.Def_OAIQ65Sa001

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConcreteHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits HomologicalComplex
namespace ConcreteHomology

universe u
variable {R : Type u} [CommRing R]
variable (K L : CC (R:=R)) (n : ℕ)

instance instAdditiveShortComplexModuleCatSFunctor : (sFunctor (R:=R)).Additive where
  map_add {X Y} f g := by
    exact ShortComplex.leftHomologyMap'_add X.moduleCatLeftHomologyData Y.moduleCatLeftHomologyData

end ConcreteHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConeHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.TotalFunctor.comparisonF_isIso _root_.OAI.TotalFunctor.comparison_isIso _root_.OAI.TotalHomotopy.singleIn_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalCone

universe u
variable {R : Type u} [CommRing R]
variable {K L : HomologicalComplex₂ (ModuleCat.{u} R) c c} (φ : K ⟶ L)
lemma total_zero {K L : HomologicalComplex₂ (ModuleCat.{u} R) c c} : total.map (0 : K ⟶ L) c=0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro p q hpq
  simp only [ιTotal_map,HomologicalComplex.zero_f,zero_comp,comp_zero]
noncomputable def h : Homotopy (f φ ≫ inr φ) 0 := by
  let t := TotalHomotopy.total (homotopyCofiber.inrCompHomotopy φ (fun j => ⟨j+1,rfl⟩))
  exact {
    hom := t.hom
    zero := t.zero
    comm n := by
      simpa only [total.map_comp,total_zero] using t.comm n }
noncomputable def comparison : homotopyCofiber (f φ) ⟶ (B φ).total c :=
  homotopyCofiber.desc (f φ) (inr φ) (h φ)
@[reassoc] lemma right_comparison (n : ℕ) :
    homotopyCofiber.inrX (f φ) n ≫ (comparison φ).f n=(inr φ).f n :=
  homotopyCofiber.inrX_desc_f _ _ _ _
@[reassoc] lemma left_comparison (p q n : ℕ) (hpq : p+q=n) :
    K.ιTotal c p q n hpq ≫ homotopyCofiber.inlX (f φ) n (n+1) rfl ≫ (comparison φ).f (n+1)=
      (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫
        (B φ).ιTotal c (p+1) q (n+1) (by dsimp;omega) := by
  have hn : c.Rel (n+1) n := rfl
  have hp : c.Rel (p+1) p := rfl
  change K.ιTotal c p q n hpq ≫ homotopyCofiber.inlX (f φ) n (n+1) hn ≫
    (comparison φ).f (n+1) = (homotopyCofiber.inlX φ p (p+1) hp).f q ≫
      (B φ).ιTotal c (p+1) q (n+1) _
  dsimp only [comparison]
  rw [homotopyCofiber.inlX_desc_f]
  change K.ιTotal c p q n hpq ≫
    TotalHomotopy.hom (homotopyCofiber.inrCompHomotopy φ (fun j => ⟨j+1,rfl⟩)) n (n+1)=_
  rw [TotalHomotopy.hom_diag,TotalHomotopy.ι_step,homotopyCofiber.inrCompHomotopy_hom]

noncomputable def inverseFZero : ((B φ).total c).X 0 ⟶ (homotopyCofiber (f φ)).X 0 :=
  (B φ).totalDesc (fun p q hpq => (homotopyCofiber.sndX φ p).f q ≫
    L.ιTotal c p q 0 hpq ≫ homotopyCofiber.inrX (f φ) 0)
noncomputable def inverseFSucc (n : ℕ) : ((B φ).total c).X (n+1) ⟶ (homotopyCofiber (f φ)).X (n+1) :=
  (B φ).totalDesc (fun p q hpq =>
    (if hp : p=0 then 0 else
      (homotopyCofiber.fstX φ p (p-1) (by change p-1+1=p;omega)).f q ≫
        K.ιTotal c (p-1) q n (by dsimp at hpq ⊢;omega) ≫
          homotopyCofiber.inlX (f φ) n (n+1) rfl) +
    (homotopyCofiber.sndX φ p).f q ≫ L.ιTotal c p q (n+1) hpq ≫
      homotopyCofiber.inrX (f φ) (n+1))
noncomputable def inverseF : ∀ n, ((B φ).total c).X n ⟶ (homotopyCofiber (f φ)).X n
  | 0 => inverseFZero φ
  | n+1 => inverseFSucc φ n
@[reassoc] lemma zero_inverse (q n : ℕ) (hq : q=n) :
    (B φ).ιTotal c 0 q n (by dsimp;omega) ≫ inverseF φ n =
      (homotopyCofiber.sndX φ 0).f q ≫ L.ιTotal c 0 q n (by dsimp;omega) ≫
        homotopyCofiber.inrX (f φ) n := by
  cases n with
  | zero => simp only [inverseF,inverseFZero,ι_totalDesc]
  | succ n =>
    simp only [inverseF,inverseFSucc,ι_totalDesc,dite_true,zero_add]
@[reassoc] lemma succ_inverse (p q n : ℕ) (hpq : p+q=n) :
    (B φ).ιTotal c (p+1) q (n+1) (by dsimp;omega) ≫ inverseF φ (n+1)=
      (homotopyCofiber.fstX φ (p+1) p rfl).f q ≫ K.ιTotal c p q n hpq ≫
        homotopyCofiber.inlX (f φ) n (n+1) rfl +
      (homotopyCofiber.sndX φ (p+1)).f q ≫ L.ιTotal c (p+1) q (n+1) (by dsimp;omega) ≫
        homotopyCofiber.inrX (f φ) (n+1) := by
  simp only [inverseF,inverseFSucc,ι_totalDesc,dite_eq_right (Nat.succ_ne_zero p),Nat.add_one_sub_one]
@[reassoc] lemma inr_snd (p q : ℕ) :
    (homotopyCofiber.inrX φ p).f q ≫ (homotopyCofiber.sndX φ p).f q = 𝟙 _ := by
  rw [←HomologicalComplex.comp_f,homotopyCofiber.inrX_sndX,HomologicalComplex.id_f]
@[reassoc] lemma inr_fst (p q : ℕ) :
    (homotopyCofiber.inrX φ (p+1)).f q ≫ (homotopyCofiber.fstX φ (p+1) p rfl).f q = 0 := by
  exact congrArg (fun morphism => morphism.f q) (homotopyCofiber.inrX_fstX φ (p+1) p rfl)
@[reassoc] lemma inl_snd (p q : ℕ) :
    (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫ (homotopyCofiber.sndX φ (p+1)).f q = 0 := by
  exact congrArg (fun morphism => morphism.f q) (homotopyCofiber.inlX_sndX φ p (p+1) rfl)
@[reassoc] lemma inl_fst (p q : ℕ) :
    (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫ (homotopyCofiber.fstX φ (p+1) p rfl).f q = 𝟙 _ := by
  exact congrArg (fun morphism => morphism.f q) (homotopyCofiber.inlX_fstX φ p (p+1) rfl)
lemma decomp (p q : ℕ) :
    (homotopyCofiber.fstX φ (p+1) p rfl).f q ≫ (homotopyCofiber.inlX φ p (p+1) rfl).f q +
      (homotopyCofiber.sndX φ (p+1)).f q ≫ (homotopyCofiber.inrX φ (p+1)).f q = 𝟙 _ := by
  have hrel : c.Rel (p+1) p := rfl
  have hh : homotopyCofiber.fstX φ (p+1) p hrel ≫ homotopyCofiber.inlX φ p (p+1) hrel +
      homotopyCofiber.sndX φ (p+1) ≫ homotopyCofiber.inrX φ (p+1) = 𝟙 _ := by
    apply homotopyCofiber.ext_from_X φ p (p+1) hrel <;> simp
  exact congrArg (fun h => h.f q) hh
lemma decomp_zero (q : ℕ) :
    (homotopyCofiber.sndX φ 0).f q ≫ (homotopyCofiber.inrX φ 0).f q = 𝟙 _ := by
  rw [←HomologicalComplex.comp_f,homotopyCofiber.sndX_inrX _ _ (by simp [c]),HomologicalComplex.id_f]
@[reassoc] lemma right_inverse (n : ℕ) :
    (inr φ).f n ≫ inverseF φ n = homotopyCofiber.inrX (f φ) n := by
  apply total.hom_ext
  intro p q hpq
  rw [ιTotal_map_assoc]
  change (homotopyCofiber.inrX φ p).f q ≫ (B φ).ιTotal c p q n hpq ≫ inverseF φ n = _
  cases p with
  | zero =>
    rw [zero_inverse φ q n (by simpa using hpq),inr_snd_assoc]
  | succ p =>
    obtain ⟨n,rfl⟩ : ∃ n',n=n'+1 := ⟨p+q,by dsimp at hpq;omega⟩
    rw [succ_inverse φ p q n (by dsimp at hpq;omega),Preadditive.comp_add,
      inr_fst_assoc,zero_comp,inr_snd_assoc,zero_add]
@[reassoc] lemma left_inverse (p q n : ℕ) (hpq : p+q=n) :
    (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫
      (B φ).ιTotal c (p+1) q (n+1) (by dsimp;omega) ≫ inverseF φ (n+1) =
        K.ιTotal c p q n hpq ≫ homotopyCofiber.inlX (f φ) n (n+1) rfl := by
  rw [succ_inverse,Preadditive.comp_add,inl_fst_assoc,inl_snd_assoc,zero_comp,add_zero]
lemma comparison_inverse (n : ℕ) : (comparison φ).f n ≫ inverseF φ n=𝟙 _ := by
  cases n with
  | zero =>
    apply homotopyCofiber.ext_from_X' (f φ) 0 (by simp [c])
    rw [←Category.assoc,right_comparison,right_inverse]
    simp
  | succ n =>
    apply homotopyCofiber.ext_from_X (f φ) n (n+1) rfl
    · apply total.hom_ext
      intro p q hpq
      rw [left_comparison_assoc φ p q n hpq,left_inverse φ p q n hpq]
      simp
    · rw [←Category.assoc,right_comparison,right_inverse]
      simp
lemma inverse_comparison (n : ℕ) : inverseF φ n ≫ (comparison φ).f n=𝟙 _ := by
  apply total.hom_ext
  intro p q hpq
  cases p with
  | zero =>
    rw [zero_inverse_assoc φ q n (by simpa using hpq),right_comparison,ιTotal_map]
    change (homotopyCofiber.sndX φ 0).f q ≫ (homotopyCofiber.inrX φ 0).f q ≫ _ = _
    rw [←Category.assoc,decomp_zero]
    simp
  | succ p =>
    obtain ⟨n,rfl⟩ : ∃ n',n=n'+1 := ⟨p+q,by dsimp at hpq;omega⟩
    rw [succ_inverse_assoc φ p q n (by dsimp at hpq;omega),Preadditive.add_comp]
    simp only [Category.assoc]
    rw [left_comparison,right_comparison,ιTotal_map]
    change (homotopyCofiber.fstX φ (p+1) p rfl).f q ≫
      (homotopyCofiber.inlX φ p (p+1) rfl).f q ≫ _ +
      (homotopyCofiber.sndX φ (p+1)).f q ≫ (homotopyCofiber.inrX φ (p+1)).f q ≫ _ = _
    simp only [←Category.assoc,←Preadditive.add_comp,decomp,Category.id_comp,Category.comp_id]
noncomputable def iso : homotopyCofiber (f φ) ≅ (B φ).total c := by
  haveI : ∀ n,IsIso ((comparison φ).f n) := fun n =>
    ⟨⟨inverseF φ n,comparison_inverse φ n,inverse_comparison φ n⟩⟩
  haveI : IsIso (comparison φ) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (comparison φ)
end TotalCone

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalProjection
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace FilteredFiniteness

universe u
variable {R : Type u} [CommRing R]
variable {A B C E : Type u} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup E] [Module R E]

namespace Data
variable (K : Data (R:=R) (A:=A) (B:=B) (C:=C))

lemma B₂_le_Z₂ (p : ℤ) : K.B₂ p ≤ K.Z₂ p := by
  apply sup_le
  · exact inf_le_inf (K.monoB (by omega)) le_rfl
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hx.1
    refine ⟨hx.2,?_⟩
    change K.e (K.d y) ∈ K.FC (p-2)
    have he : K.e (K.d y)=0 := congrArg (fun f : A →ₗ[R] C => f y) K.de
    rw [he]
    exact (K.FC _).zero_mem

end Data
end FilteredFiniteness

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_EilenbergZilber
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly

variable (X : Dᵒᵖ ⥤ Type)

noncomputable def twoIso : TotalFunctor.map₂ (assembly X) BiResolution.complex ≅ twoComplex X := by
  let F := assembly X
  let FC := F.mapHomologicalComplex c
  refine (CategoryTheory.eqToIso (congrArg (fun G => G.obj
    (BiResolution.chains ⋙ alternatingFaceMapComplex (D ⥤ A)))
      (map_alternatingFaceMapComplex FC))) ≪≫ ?_
  change AlternatingFaceMapComplex.obj
    (BiResolution.chains ⋙ alternatingFaceMapComplex (D ⥤ A) ⋙ FC) ≅ _
  rw [map_alternatingFaceMapComplex F]
  exact (alternatingFaceMapComplex (ChainComplex A ℕ)).mapIso
    (Functor.isoWhiskerRight (bisimplicialIso X) (alternatingFaceMapComplex A))

noncomputable def equiv : HomotopyEquiv (SSet.chainComplex (diag ⋙ X) Z) ((twoComplex X).total c) :=
  (HomotopyEquiv.ofIso (diagonalIso X).symm).trans
    ((assembledEquiv X).trans (HomotopyEquiv.ofIso
      (TotalFunctor.iso (assembly X) BiResolution.complex ≪≫ total.mapIso (twoIso X) c)))

noncomputable def homologyIso (n : ℕ) :
    SSet.homology (diag ⋙ X) Z n ≅ (((twoComplex X).total c).homology n) :=
  (equiv X).toHomologyIso n

end EilenbergZilber

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalFiniteness
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory HomologicalComplex HomologicalComplex₂

namespace EilenbergZilber
open DiagonalResolution ModelAssembly
variable (X : Dᵒᵖ ⥤ Type)
lemma subsingleton_diagonal (n : ℕ)
    (hzero : ∀ p q, p+q=n → Subsingleton
      ((TotalFiniteness.row (twoComplex X) q).homology p)) :
    Subsingleton (SSet.homology (C:=A) (diag ⋙ X) Z n) := by
  have := TotalFiniteness.subsingleton (twoComplex X) n hzero
  exact (homologyIso X n).toLinearEquiv.injective.subsingleton
end EilenbergZilber

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ProductChains
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainTensor
open FreeChains
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

instance leftAdditive (K : ChainComplex A ℕ) : (tensorLeft K).Additive where
  map_add {L M} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply total.hom_ext
    intro p q hpq
    change ιMapBifunctor K L (curriedTensor A) c p q n hpq ≫
        (mapBifunctorMap (𝟙 K) (f+g) (curriedTensor A) c).f n =
      ιMapBifunctor K L (curriedTensor A) c p q n hpq ≫
        ((mapBifunctorMap (𝟙 K) f (curriedTensor A) c).f n + (mapBifunctorMap (𝟙 K) g (curriedTensor A) c).f n)
    simp [Preadditive.comp_add]
instance rightAdditive (K : ChainComplex A ℕ) : (tensorRight K).Additive where
  map_add {L M} f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply total.hom_ext
    intro p q hpq
    change ιMapBifunctor L K (curriedTensor A) c p q n hpq ≫
        (mapBifunctorMap (f+g) (𝟙 K) (curriedTensor A) c).f n =
      ιMapBifunctor L K (curriedTensor A) c p q n hpq ≫
        ((mapBifunctorMap f (𝟙 K) (curriedTensor A) c).f n + (mapBifunctorMap g (𝟙 K) (curriedTensor A) c).f n)
    simp [Preadditive.comp_add]
end ChainTensor

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ProductNatural
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ChainTensor
open FreeChains

instance monoidalPreadditive : MonoidalPreadditive (ChainComplex A ℕ) where
  whiskerLeft_zero := fun {K L M} => (tensorLeft K).map_zero L M
  zero_whiskerRight := fun {K L M} => (tensorRight K).map_zero L M
  whiskerLeft_add := fun {K _ _} f g => (tensorLeft K).map_add (f:=f) (g:=g)
  add_whiskerRight := fun {K _ _} f g => (tensorRight K).map_add (f:=f) (g:=g)
end ChainTensor

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TotalComparison
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalComparison

universe u
variable {R : Type u} [CommRing R]
variable {K L : HomologicalComplex₂ (ModuleCat.{u} R) c c} (φ : K ⟶ L)
noncomputable def rowMap (q : ℕ) : TotalFiniteness.row K q ⟶ TotalFiniteness.row L q :=
  ((homologyFunctor (ModuleCat.{u} R) c q).mapHomologicalComplex c).map φ
lemma rowMap_isIso (q : ℕ) (hφ : ∀ p,IsIso (homologyMap (φ.f p) q)) : IsIso (rowMap φ q) := by
  have : ∀ p,IsIso ((rowMap φ q).f p) := hφ
  exact HomologicalComplex.Hom.isIso_of_components _
noncomputable def rowConeIso (q : ℕ) :
    TotalFiniteness.row (TotalCone.B φ) q ≅ homotopyCofiber (rowMap φ q) :=
  homotopyCofiber.mapHomologicalComplexObjIso φ (homologyFunctor (ModuleCat.{u} R) c q)
lemma rowCone_zero (hφ : ∀ p q,IsIso (homologyMap (φ.f p) q)) (p q : ℕ) :
    Subsingleton ((TotalFiniteness.row (TotalCone.B φ) q).homology p) := by
  have := rowMap_isIso φ q (fun p => hφ p q)
  have := ConeCoordinates.cone_subsingleton_of_iso (rowMap φ q) p
  let e := (homologyFunctor (ModuleCat.{u} R) c p).mapIso (rowConeIso φ q) ≪≫
    ConcreteHomology.iso _ p
  exact e.toLinearEquiv.injective.subsingleton
lemma cone_zero (hφ : ∀ p q,IsIso (homologyMap (φ.f p) q)) (n : ℕ) :
    Subsingleton (ConcreteHomology.H (homotopyCofiber (total.map φ c)) n) := by
  have := TotalFiniteness.subsingleton (TotalCone.B φ) n (fun p q _ => rowCone_zero φ hφ p q)
  let e := (ConcreteHomology.functor (R:=R) n).mapIso (TotalCone.iso φ) ≪≫
    (ConcreteHomology.iso ((TotalCone.B φ).total c) n).symm
  exact e.toLinearEquiv.injective.subsingleton
lemma total_homology_isIso (hφ : ∀ p q,IsIso (homologyMap (φ.f p) q)) (n : ℕ) :
    IsIso (homologyMap (total.map φ c) n) := by
  have := cone_zero φ hφ n
  have := cone_zero φ hφ (n+1)
  have : IsIso ((ConcreteHomology.functor n).map (total.map φ c)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨ConeCoordinates.injective_of_cone_zero _ n,ConeCoordinates.surjective_of_cone_zero _ n⟩
  exact (NatIso.isIso_map_iff (ConcreteHomology.naturalIso (R:=R) n) (total.map φ c)).mpr inferInstance
end TotalComparison

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_DiagonalComparison
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits SimplicialObject Simplicial Opposite AlgebraicTopology
open HomologicalComplex HomologicalComplex₂
namespace EilenbergZilber

open DiagonalResolution ModelAssembly
variable {X Y : Dᵒᵖ ⥤ Type} (φ : X ⟶ Y)
lemma level_homology_isIso
    (hφ : ∀ p q,IsIso (SSet.homologyMap ((bisimplicialMap φ).app p) Z q)) (n : ℕ) :
    IsIso (homologyMap (diagonalMap φ) n) := by
  have : IsIso (homologyMap (total.map (twoMap φ) c) n) := by
    apply TotalComparison.total_homology_isIso
    intro p q
    exact hφ (op ⦋p⦌) q
  have he : homologyMap (diagonalMap φ) n =
      (homologyIsoN X n).hom ≫ homologyMap (total.map (twoMap φ) c) n ≫ (homologyIsoN Y n).inv := by
    rw [←Category.assoc,←homology_natural,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [he]
  infer_instance
end EilenbergZilber

end

open _root_.CategoryTheory SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open DiagonalResolution

def rowIso (X : I ⥤ SSet) (p : I) :
    (EilenbergZilber.bisimplicial (uncurry X)).obj p ≅ X.obj p :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro q q' f
    simp [EilenbergZilber.bisimplicial,uncurry,Functor.uncurry])
theorem homologyMap_comp_iso {W X Y Z : SSet} (e : W ≅ X) (f : X ⟶ Y)
    (e' : Y ≅ Z) (q : ℕ) (hf : IsIso (SSet.homologyMap f DiagonalResolution.Z q)) :
    IsIso (SSet.homologyMap (e.hom ≫ f ≫ e'.hom) DiagonalResolution.Z q) := by
  let := hf
  rw [SSet.homologyMap_comp, SSet.homologyMap_comp]
  infer_instance

theorem row_homologyMap_isIso {X Y : I ⥤ SSet} (f : X ⟶ Y)
    (hf : ∀ p q, IsIso (SSet.homologyMap (f.app p) DiagonalResolution.Z q))
    (p : SimplexCategoryᵒᵖ) (q : ℕ) :
    IsIso (SSet.homologyMap ((EilenbergZilber.bisimplicialMap
      (Functor.whiskerLeft (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor
        (Functor.uncurry.map f))).app p) DiagonalResolution.Z q) := by
  have he : (EilenbergZilber.bisimplicialMap
      (Functor.whiskerLeft (prodOpEquiv SimplexCategory (D:=SimplexCategory)).functor
        (Functor.uncurry.map f))).app p =
      (rowIso X p).hom ≫ f.app p ≫ (rowIso Y p).inv := by
    ext k x
    rfl
  rw [he]
  exact homologyMap_comp_iso (rowIso X p) (f.app p) (rowIso Y p).symm q (hf p q)

lemma homologyMap_isIso {X Y : I ⥤ SSet} (f : X ⟶ Y)
    (hf : ∀ p q, IsIso (SSet.homologyMap (f.app p) DiagonalResolution.Z q)) (n : ℕ) :
    IsIso (SSet.homologyMap (diagonal.map f) DiagonalResolution.Z n) := by
  exact EilenbergZilber.level_homology_isIso _ (row_homologyMap_isIso f hf) n

lemma nerveDiagonal_isIso {X Y : I ⥤ Cat.{0,0}} (f : X ⟶ Y)
    (hf : ∀ p, (f.app p).toFunctor.IsEquivalence) (n : ℕ) :
    IsIso (SSet.homologyMap (nerveDiagonal.map f) DiagonalResolution.Z n) := by
  apply homologyMap_isIso
  intro p q
  have := hf p
  exact NerveHomotopy.homologyMap_isIso (f.app p).toFunctor DiagonalResolution.Z q
end SimplicialDiagonal

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalTensor
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.mapBraided _root_.OAI.IntervalBar.Diagram.mapMonoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.reindexBraided _root_.OAI.IntervalBar.Diagram.reindexMonoidal _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I : Type w} [Preorder I]

noncomputable instance evalMonoidal (n : ℕ) : (eval (C:=C) n).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso := fun A B => Iso.refl _
    μIso_hom_natural_left := by intros; ext i; simp [eval]
    μIso_hom_natural_right := by intros; ext i; simp [eval]
    associativity := by intros; ext i; simp [eval]
    left_unitality := by intros; ext i; simp [eval]
    right_unitality := by intros; ext i; simp [eval] }

end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalFunctor
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' w
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I : Type w} [Preorder I]

noncomputable instance evalBraided (n : ℕ) : (eval (C:=C) n).Braided where
  braided A B := by
    funext i
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp

end IntervalBar.Diagram

end

open _root_.CategoryTheory MonoidalCategory BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe u v u' v' u'' v'' w

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEssSurj
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory
universe u v u' v'
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]

noncomputable instance mapEssSurj (F : C ⥤ D) [F.Monoidal] [F.EssSurj] (n : ℕ) :
    (map (I:=Fin (n+1)) F).EssSurj where
  mem_essImage X := by
    let Y : Fin n → C := fun i => F.objPreimage ((eval n).obj X i)
    let A := (eval (C:=C) n).objPreimage Y
    let e := (eval (C:=C) n).objObjPreimageIso Y
    let f : (eval n).obj ((map F).obj A) ⟶ (eval n).obj X := fun i =>
      F.map (e.hom i) ≫ (F.objObjPreimageIso ((eval n).obj X i)).hom
    exact ⟨A,⟨asIso (extend f)⟩⟩

end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEquivalence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IntervalBar.Diagram

section
open _root_.CategoryTheory MonoidalCategory
universe u v u' v'

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
instance mapFaithful (F : C ⥤ D) [F.Monoidal] [F.Faithful] (n : ℕ) :
    (map (I:=Fin (n+1)) F).Faithful where
  map_injective h := by
    apply Hom.ext
    intro i j hij
    apply F.map_injective
    exact congrArg (fun f => f.app i j hij) h
noncomputable instance mapFull (F : C ⥤ D) [F.Monoidal] [F.Full] (n : ℕ) :
    (map (I:=Fin (n+1)) F).Full where
  map_surjective {X Y} φ := by
    let f : (eval n).obj X ⟶ (eval n).obj Y := fun i => F.preimage ((eval n).map φ i)
    refine ⟨extend f, ?_⟩
    apply (eval (C:=D) n).map_injective
    funext i
    change F.map ((extend f).app i.castSucc i.succ (Fin.castSucc_le_succ i)) = _
    rw [extend_elementary]
    exact F.map_preimage _
noncomputable instance mapIsEquivalence (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence] (n : ℕ) :
    (map (I:=Fin (n+1)) F).IsEquivalence where
end

section
open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
omit [SymmetricCategory C] [SymmetricCategory D] in
lemma barMap_homology_isIso (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence] (n : ℕ) :
    IsIso (SSet.homologyMap (barMap F) DiagonalResolution.Z n) := by
  apply SimplicialDiagonal.nerveDiagonal_isIso
  intro p
  exact mapIsEquivalence F p.unop.len
end

end IntervalBar.Diagram

section
open _root_.CategoryTheory SimplicialObject Simplicial Opposite MonoidalCategory
namespace SimplicialDiagonal

noncomputable def fromZero (X : I ⥤ SSet) : X.obj (op ⦋0⦌) ⟶ diagonal.obj X where
  app n := (X.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).app n
  naturality n m f := by
    change (X.obj (op ⦋0⦌)).map f ≫ (X.map _).app m =
      (X.map _).app n ≫ ((X.map f).app n ≫ (X.obj m).map f)
    rw [←Category.assoc,←NatTrans.comp_app,←X.map_comp]
    have hc : (SimplexCategory.const n.unop ⦋0⦌ 0).op ≫ f =
        (SimplexCategory.const m.unop ⦋0⦌ 0).op := Subsingleton.elim _ _
    rw [hc]
    exact (X.map (SimplexCategory.const m.unop ⦋0⦌ 0).op).naturality f
lemma fromZero_zero (X : I ⥤ SSet) (x : (X.obj (op ⦋0⦌)).obj (op ⦋0⦌)) :
    (fromZero X).app (op ⦋0⦌) x=x := by
  change (X.map _).app _ x=x
  rw [Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op (𝟙 _)]
  simp
instance diagonal_connected (X : I ⥤ SSet) [(X.obj (op ⦋0⦌)).IsConnected] :
    (diagonal.obj X).IsConnected where
  allEq u v := by
    obtain ⟨x,rfl⟩ := SSet.π₀.mk_surjective u
    obtain ⟨y,rfl⟩ := SSet.π₀.mk_surjective v
    have h := congrArg (SSet.mapπ₀ (fromZero X))
      (Subsingleton.elim (SSet.π₀.mk (X:=X.obj (op ⦋0⦌)) x) (SSet.π₀.mk y))
    erw [SSet.mapπ₀_mk, SSet.mapπ₀_mk, fromZero_zero, fromZero_zero] at h
    exact h
  nonempty := inferInstanceAs (Nonempty ((X.obj (op ⦋0⦌)).obj (op ⦋0⦌)))
end SimplicialDiagonal
namespace IntervalBar.Diagram
variable (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable instance zero_nonempty : Nonempty (Diagram C (Fin 1)) := ⟨constantUnit⟩
noncomputable def zeroHom (X Y : Diagram C (Fin 1)) : X ⟶ Y :=
  (eval 0).preimage (fun i => Fin.elim0 i)
instance zero_nerve_connected : (nerve (Diagram C (Fin 1))).IsConnected :=
  _root_.OAI.CategoryTheory.nerve.connected_of_hom (fun X Y => ⟨zeroHom C X Y⟩)
instance bar_connected : (bar (C:=C)).IsConnected := by
  let X := (((Functor.whiskeringRight SimplicialDiagonal.I Cat SSet).obj nerveFunctor).obj (simplicial (C:=C)))
  have : (X.obj (op ⦋0⦌)).IsConnected := zero_nerve_connected C
  exact SimplicialDiagonal.diagonal_connected X
end IntervalBar.Diagram

end

open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type} [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
lemma simplicialMap_reindex_comp (f : I →o J) (g : J →o K) :
    simplicialMap (reindex (C:=C) (g.comp f)) =
      simplicialMap (reindex g) ≫ simplicialMap (reindex f) := by
  apply NatTrans.ext
  funext p
  apply Cat.ext
  exact map_reindex_comp f g
lemma barMap_reindex_comp (f : I →o J) (g : J →o K) :
    barMap (reindex (C:=C) (g.comp f)) =
      barMap (reindex g) ≫ barMap (reindex f) := by
  simp [barMap,simplicialMap_reindex_comp]
  rfl
noncomputable def rows₂ : SimplexCategoryᵒᵖ ⥤ SSet where
  obj p := bar (C:=Diagram C (Fin (p.unop.len+1)))
  map f := barMap (reindex f.unop.toOrderHom)
  map_id _ := barMap_reindex_id
  map_comp f g := barMap_reindex_comp g.unop.toOrderHom f.unop.toOrderHom
noncomputable def bar₂ : SSet := SimplicialDiagonal.diagonal.obj (rows₂ (C:=C))
instance bar₂_connected : (bar₂ (C:=C)).IsConnected := by
  have : ((rows₂ (C:=C)).obj (op ⦋0⦌)).IsConnected := bar_connected _
  exact SimplicialDiagonal.diagonal_connected (rows₂ (C:=C))
lemma map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    map (I:=K) (map (I:=J) F) ⋙ map (reindex f) =
      map (reindex f) ⋙ map (map (I:=I) F) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · rfl
    · apply heq_of_eq
      funext k
      apply Iso.ext
      apply Hom.ext
      intro i j h
      change (((map F).map (A.unit k).hom ≫ Functor.OplaxMonoidal.η (map F)).app
          (f i) (f j) (f.monotone h)) ≫ 𝟙 _ =
        ((map F).map ((reindex f).map (A.unit k).hom ≫ Functor.OplaxMonoidal.η (reindex f)) ≫
          Functor.OplaxMonoidal.η (map F)).app i j h
      erw [comp_app, map_η_app (I:=J) F, comp_app, map_η_app (I:=I) F]
      change (F.map ((A.unit k).hom.app (f i) (f j) _) ≫ Functor.OplaxMonoidal.η F) ≫ 𝟙 _ =
        F.map ((A.unit k).hom.app (f i) (f j) _ ≫ 𝟙 _) ≫ Functor.OplaxMonoidal.η F
      erw [Category.comp_id, Category.comp_id]
    · apply heq_of_eq
      funext i j k hij hjk
      apply Iso.ext
      apply Hom.ext
      intro l m h
      change 𝟙 _ ≫ (Functor.LaxMonoidal.μ F _ _ ≫ F.map ((A.cut i j k hij hjk).hom.app (f l) (f m) _)) =
        Functor.LaxMonoidal.μ F _ _ ≫ F.map (𝟙 _ ≫ (A.cut i j k hij hjk).hom.app (f l) (f m) _)
      erw [Category.id_comp, Category.id_comp]
  · intro A B g
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro l m hlm
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IteratedBarMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K L : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
lemma simplicialMap_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    simplicialMap (map (I:=J) F) ≫ simplicialMap (reindex f) =
      simplicialMap (reindex f) ≫ simplicialMap (map (I:=I) F) := by
  apply NatTrans.ext; funext p; apply Cat.ext
  exact map_map_reindex F f
lemma barMap_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    barMap (map (I:=J) F) ≫ barMap (reindex f) =
      barMap (reindex f) ≫ barMap (map (I:=I) F) := by
  have h := congrArg (SimplicialDiagonal.nerveDiagonal.map) (simplicialMap_map_reindex F f)
  erw [Functor.map_comp, Functor.map_comp] at h
  exact h
noncomputable def rows₂Map (F : C ⥤ D) [F.Braided] : rows₂ (C:=C) ⟶ rows₂ (C:=D) where
  app p := barMap (map (I:=Fin (p.unop.len+1)) F)
  naturality _ _ f := (barMap_map_reindex F f.unop.toOrderHom).symm
noncomputable def bar₂Map (F : C ⥤ D) [F.Braided] : bar₂ (C:=C) ⟶ bar₂ (C:=D) :=
  SimplicialDiagonal.diagonal.map (rows₂Map F)
lemma bar₂Map_homology_isIso (F : C ⥤ D) [F.Braided] [F.IsEquivalence] (n : ℕ) :
    IsIso (SSet.homologyMap (bar₂Map F) DiagonalResolution.Z n) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p q
  exact barMap_homology_isIso (map (I:=Fin (p.unop.len+1)) F) q
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_SimplicialH0
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialH0
open FreeChains

variable {X Y : SSet}
noncomputable def connectedIso (T : SimplicialObject SSet.{0}) (hT : ∀ n,(T.obj n).IsConnected) :
    T ⋙ SSet.homologyFunctor Z 0 ≅ (Functor.const SimplexCategoryᵒᵖ).obj Z :=
  by
    let f : T ⋙ SSet.homologyFunctor Z 0 ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Z :=
      { app n := (T.obj n).homology₀ε Z
        naturality n m g := by
          change SSet.homologyMap (T.map g) Z 0 ≫ (T.obj m).homology₀ε Z =
            (T.obj n).homology₀ε Z ≫ 𝟙 Z
          simpa only [Category.comp_id] using natural (T.map g) }
    have : ∀ n, IsIso (f.app n) := fun n => by
      have : (T.obj n).IsConnected := hT n
      change IsIso ((T.obj n).homology₀ε Z)
      infer_instance
    have : IsIso f := NatIso.isIso_of_isIso_app f
    exact asIso f
end SimplicialH0

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace BarHomology
open FreeChains

variable (X : Dᵒᵖ ⥤ Type)
noncomputable def rowIso (q : ℕ) : TotalFiniteness.row (EilenbergZilber.twoComplex X) q ≅
    AlternatingFaceMapComplex.obj (EilenbergZilber.bisimplicial X ⋙ SSet.homologyFunctor Z q) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) ?_
  intro n m hnm
  obtain rfl : n=m+1 := hnm.symm
  simp only [Iso.refl_hom]
  change _ = (homologyFunctor A c q).map
    ((AlternatingFaceMapComplex.obj (EilenbergZilber.bisimplicial (X ⋙ sigmaConst.obj Z) ⋙ alternatingFaceMapComplex A)).d (m+1) m)
  simp only [AlternatingFaceMapComplex.obj_d_eq,Functor.map_sum,Functor.map_zsmul]
  rfl
noncomputable def zeroRowIso (hX : ∀ n, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj n)) :
    TotalFiniteness.row (EilenbergZilber.twoComplex X) 0 ≅
      AlternatingFaceMapComplex.obj ((Functor.const SimplexCategoryᵒᵖ).obj Z) :=
  rowIso X 0 ≪≫ (alternatingFaceMapComplex A).mapIso
    (SimplicialH0.connectedIso (EilenbergZilber.bisimplicial X) hX)
lemma zeroRow_vanish (hX : ∀ n, SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj n))
    (p : ℕ) (hp : p≠0) : IsZero ((TotalFiniteness.row (EilenbergZilber.twoComplex X) 0).homology p) := by
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const Z).homotopyEquiv
  exact IsZero.of_iso (AugmentedSplit.uni_isZero p hp)
    (((homologyFunctor A c p).mapIso (zeroRowIso X hX)) ≪≫ e.toHomologyIso p)
end BarHomology

end

section
open _root_.CategoryTheory Limits HomologicalComplex HomologicalComplex₂ SimplicialObject Simplicial Opposite AlgebraicTopology
namespace BarHomology
open FreeChains

lemma zero_homology (K : ChainComplex A ℕ) (n : ℕ) (hz : IsZero (K.X n)) :
    IsZero (K.homology n) := ShortComplex.isZero_homology_of_isZero_X₂ (K.sc n) hz
variable (X : Dᵒᵖ ⥤ Type)
lemma E2_zero (p q : ℕ) (hz : IsZero
    (SSet.homology (C:=A) ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q)) :
    IsZero ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).homology p) :=
  zero_homology _ p hz

lemma connectivity (d : ℕ)
    (hc : ∀ n,SSet.IsConnected ((EilenbergZilber.bisimplicial X).obj n))
    (hz : ∀ q, 0 < q → IsZero (SSet.homology (C:=A)
      ((EilenbergZilber.bisimplicial X).obj (op ⦋0⦌)) Z q))
    (hr : ∀ p q, 0 < q → q < d → IsZero (SSet.homology (C:=A)
      ((EilenbergZilber.bisimplicial X).obj (op ⦋p⦌)) Z q))
    (n : ℕ) (hn : 0 < n) (hd : n < d+1) :
    Subsingleton (SSet.homology (C:=A) (EilenbergZilber.diag ⋙ X) Z n) := by
  apply EilenbergZilber.subsingleton_diagonal X n
  intro p q hpq
  by_cases hq : q=0
  · subst q
    exact (ModuleCat.isZero_iff_subsingleton).mp (zeroRow_vanish X hc p (by omega))
  · have h : IsZero ((TotalFiniteness.row (EilenbergZilber.twoComplex X) q).homology p) := by
      by_cases hp : p=0
      · subst p; exact E2_zero X 0 q (hz q (by omega))
      · exact E2_zero X p q (hr p q (by omega) (by omega))
    exact (ModuleCat.isZero_iff_subsingleton).mp h

end BarHomology

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarContractible
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits SimplicialObject Simplicial Opposite MonoidalCategory
namespace SimplicialDiagonal
open FreeChains

lemma connectivity (X : I ⥤ SSet) (d : ℕ)
    (hc : ∀ p,(X.obj p).IsConnected)
    (hz : ∀ q,0<q → IsZero (SSet.homology (C:=A) (X.obj (op ⦋0⦌)) Z q))
    (hr : ∀ p q,0<q → q<d → IsZero (SSet.homology (C:=A) (X.obj (op ⦋p⦌)) Z q))
    (n : ℕ) (hn : 0<n) (hd : n<d+1) : IsZero (SSet.homology (C:=A) (diagonal.obj X) Z n) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply BarHomology.connectivity (uncurry X) d
  · intro p
    have := hc p
    exact connected_of_iso (rowIso X p)
  · intro q hq
    exact IsZero.of_iso (hz q hq) ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋0⦌)))
  · intro p q hq hqd
    exact IsZero.of_iso (hr p q hq hqd) ((SSet.homologyFunctor Z q).mapIso (rowIso X (op ⦋p⦌)))
  · exact hn
  · exact hd
end SimplicialDiagonal
namespace CategoryTheory.nerve
open scoped _root_.CategoryTheory _root_.CategoryTheory.nerve
open FreeChains

lemma positive_zero {C : Type} [_root_.CategoryTheory.Category.{0} C] [Nonempty C]
    [∀ x y : C,Subsingleton (x ⟶ y)] (hh : ∀ x y : C,Nonempty (x ⟶ y))
    (n : ℕ) (hn : n≠0) : IsZero (SSet.homology (C:=A) (_root_.CategoryTheory.nerve C) Z n) := by
  let c := Classical.arbitrary C
  let α : 𝟭 C ⟶ (_root_.CategoryTheory.Functor.const C).obj c :=
    { app x := Classical.choice (hh x c)
      naturality _ _ _ := Subsingleton.elim _ _ }
  have h := (NerveHomotopy.ofNatTrans α).congr_homologyMap Z n
  change SSet.homologyMap (𝟙 (_root_.CategoryTheory.nerve C)) Z n = SSet.homologyMap (_root_.CategoryTheory.nerveMap ((_root_.CategoryTheory.Functor.const C).obj c)) Z n at h
  erw [SSet.homologyMap_id,const_map,ConnectedProduct.const_homology_zero _ n hn] at h
  exact (IsZero.iff_id_eq_zero _).mpr h
end CategoryTheory.nerve
namespace IntervalBar.Diagram
open FreeChains

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
instance zero_thin (X Y : Diagram C (Fin 1)) : Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => (eval 0).map_injective (funext (fun i => Fin.elim0 i))⟩
instance zero_hom_nonempty (X Y : Diagram C (Fin 1)) : Nonempty (X ⟶ Y) := ⟨zeroHom C X Y⟩
instance hom_thin [∀ x y : C,Subsingleton (x ⟶ y)] (n : ℕ)
    (X Y : Diagram C (Fin (n+1))) : Subsingleton (X ⟶ Y) :=
  ⟨fun _ _ => Hom.ext (fun _ _ _ => Subsingleton.elim _ _)⟩
noncomputable def homOfAll (hh : ∀ x y : C,Nonempty (x ⟶ y)) (n : ℕ)
    (X Y : Diagram C (Fin (n+1))) : X ⟶ Y :=
  (eval n).preimage (fun _ => Classical.choice (hh _ _))
omit [SymmetricCategory C] in
lemma bar_acyclic [∀ x y : C,Subsingleton (x ⟶ y)]
    (hh : ∀ x y : C,Nonempty (x ⟶ y)) (n : ℕ) (hn : 0<n) :
    IsZero (SSet.homology (C:=A) (bar (C:=C)) Z n) := by
  let X := (((Functor.whiskeringRight SimplicialDiagonal.I Cat SSet).obj nerveFunctor).obj (simplicial (C:=C)))
  have hc (p : SimplicialDiagonal.I) : (X.obj p).IsConnected := by
    have : Nonempty (Diagram C (Fin (p.unop.len+1))) := ⟨constantUnit⟩
    change (nerve (Diagram C (Fin (p.unop.len+1)))).IsConnected
    exact nerve.connected_of_hom (fun x y => ⟨homOfAll hh _ x y⟩)
  have hz (p : ℕ) (q : ℕ) (hq : 0<q) : IsZero (SSet.homology (C:=A) (X.obj (op ⦋p⦌)) Z q) := by
    have : Nonempty (Diagram C (Fin (p+1))) := ⟨constantUnit⟩
    exact nerve.positive_zero (fun x y => ⟨homOfAll hh p x y⟩) q (by omega)
  exact SimplicialDiagonal.connectivity X n hc (hz 0) (fun p q hq _ => hz p q hq) n hn (by omega)
lemma zero_bar_acyclic (n : ℕ) (hn : 0<n) :
    IsZero (SSet.homology (C:=A) (bar (C:=Diagram C (Fin 1))) Z n) :=
  bar_acyclic (fun _ _ => inferInstance) n hn
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I J K L M : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L] [Preorder M]
lemma map_map_reindex_unit_app (f : I →o J)
    (A : Diagram (Diagram (Diagram C J) L) M) (i : M)
    (j k : L) (h : j ≤ k) (l m : I) (hlm : l ≤ m) :
    ((((map (map (reindex f))).obj A).unit i).hom.app j k h).app l m hlm =
      ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) := by
  change (((map (reindex f)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (map (reindex f))).app j k h).app l m hlm = _
  erw [comp_app, map_η_app (I:=L) (reindex (C:=C) f)]
  change ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma map_map_reindex_comp (f : I →o J) (g : J →o K) :
    map (I:=M) (map (I:=L) (reindex (C:=C) (g.comp f))) =
      map (map (reindex g)) ⋙ map (map (reindex f)) := by
  have he (X : Diagram (Diagram C K) L) : mapObj (reindex (g.comp f)) X=
      mapObj (reindex f) (mapObj (reindex g) X) :=
    congrArg (fun F => F.obj X) (map_reindex_comp f g)
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h; exact he _
    · apply hfunext; intro i
      apply iso_hext (he _) rfl
      apply hom_hext (he _) rfl
      intro j k h
      apply hom_hext rfl rfl
      intro l m hlm
      apply heq_of_eq
      erw [map_map_reindex_unit_app, map_map_reindex_unit_app, map_map_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _) (he _)) (he _)
      intro l m hlm
      apply hom_hext rfl rfl
      intro n p hnp
      apply heq_of_eq
      change 𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app (g (f n)) (g (f p)) _ =
        𝟙 _ ≫ (𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app (g (f n)) (g (f p)) _)
      simp only [Category.id_comp]
  · intro A B h
    apply Hom.ext; intro i j hij
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro k l hkl
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro m n hmn
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
lemma barMap_map_reindex_id : barMap (map (I:=J) (reindex (C:=C) (OrderHom.id (α:=I))))=𝟙 _ := by
  have he : simplicialMap (map (I:=J) (reindex (C:=C) (OrderHom.id (α:=I))))=𝟙 _ := by
    apply NatTrans.ext; funext p; apply Cat.ext
    exact map_map_reindex_id
  simp only [barMap,he]
  rfl
lemma barMap_map_reindex_comp (f : I →o J) (g : J →o K) :
    barMap (map (I:=L) (reindex (C:=C) (g.comp f))) =
      barMap (map (reindex g)) ≫ barMap (map (reindex f)) := by
  have he : simplicialMap (map (I:=L) (reindex (C:=C) (g.comp f))) =
      simplicialMap (map (reindex g)) ≫ simplicialMap (map (reindex f)) := by
    apply NatTrans.ext; funext p; apply Cat.ext
    exact map_map_reindex_comp f g
  simp only [barMap,he,Functor.map_comp]
  rfl
lemma bar₂Map_reindex_id : bar₂Map (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
  have he : rows₂Map (reindex (C:=C) (OrderHom.id (α:=I)))=𝟙 _ := by
    apply NatTrans.ext; funext p
    exact barMap_map_reindex_id
  simp only [bar₂Map,he]
  rfl
lemma bar₂Map_reindex_comp (f : I →o J) (g : J →o K) :
    bar₂Map (reindex (C:=C) (g.comp f)) = bar₂Map (reindex g) ≫ bar₂Map (reindex f) := by
  have he : rows₂Map (reindex (C:=C) (g.comp f)) = rows₂Map (reindex g) ≫ rows₂Map (reindex f) := by
    apply NatTrans.ext; funext p
    exact barMap_map_reindex_comp f g
  simp only [bar₂Map,he,Functor.map_comp]
  rfl
noncomputable def rows₃ : SimplexCategoryᵒᵖ ⥤ SSet where
  obj p := bar₂ (C:=Diagram C (Fin (p.unop.len+1)))
  map f := bar₂Map (reindex f.unop.toOrderHom)
  map_id _ := bar₂Map_reindex_id
  map_comp f g := bar₂Map_reindex_comp g.unop.toOrderHom f.unop.toOrderHom
noncomputable def bar₃ : SSet := SimplicialDiagonal.diagonal.obj (rows₃ (C:=C))
open FreeChains
lemma bar₂_acyclic [∀ x y : C,Subsingleton (x ⟶ y)]
    (hh : ∀ x y : C,Nonempty (x ⟶ y)) (n : ℕ) (hn : 0<n) :
    Limits.IsZero (SSet.homology (C:=A) (bar₂ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₂ (C:=C)) n
  · intro _; exact bar_connected _
  · intro q hq
    exact bar_acyclic (fun x y => ⟨homOfAll hh 0 x y⟩) q hq
  · intro p q hq _
    exact bar_acyclic (fun x y => ⟨homOfAll hh p x y⟩) q hq
  · exact hn
  · omega
lemma bar₂_H1_zero (n : ℕ) (hn : 0<n) (hd : n<2) :
    Limits.IsZero (SSet.homology (C:=A) (bar₂ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₂ (C:=C)) 1
  · intro _; exact bar_connected _
  · exact zero_bar_acyclic
  · intro p q hq hd; omega
  · exact hn
  · exact hd
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PowerEquivalence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace IntervalBar.Diagram
open StageProductColimit MonoidalCategory

variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
noncomputable def eval₃ (l m n:ℕ) : Diagram (Diagram (Diagram C (Fin (n+1))) (Fin (m+1)))
    (Fin (l+1)) ⥤ (Fin l × (Fin m × Fin n) → C) :=
  eval l ⋙ powerMap (Fin l) (eval₂ m n) ⋙ uncurry (Fin l) (Fin m × Fin n)
noncomputable instance instIsEquivalenceFinHAddNatOfNatForallProdEval₃ (l m n:ℕ) : (eval₃ (C:=C) l m n).IsEquivalence := by
  dsimp [eval₃]; infer_instance
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleBarMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K L : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
lemma map_reindex_unit_app (f : I →o J)
    (A : Diagram (Diagram (Diagram C J) K) L) (i : L)
    (j k : K) (h : j ≤ k) (l m : I) (hlm : l ≤ m) :
    ((((map (map (reindex f))).obj A).unit i).hom.app j k h).app l m hlm =
      ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) := by
  change (((map (reindex f)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (map (reindex f))).app j k h).app l m hlm = _
  erw [comp_app, map_η_app (I:=K) (reindex (C:=C) f)]
  change ((A.unit i).hom.app j k h).app (f l) (f m) (f.monotone hlm) ≫ 𝟙 _ = _
  exact Category.comp_id _

lemma map_triple_unit_app (F : C ⥤ D) [F.Braided]
    (A : Diagram (Diagram (Diagram C J) K) L) (i : L)
    (j k : K) (h : j ≤ k) (l m : J) (hlm : l ≤ m) :
    ((((map (map (map F))).obj A).unit i).hom.app j k h).app l m hlm =
      F.map (((A.unit i).hom.app j k h).app l m hlm) ≫ Functor.OplaxMonoidal.η F := by
  change (((map (map F)).map (A.unit i).hom ≫
    Functor.OplaxMonoidal.η (map (map F))).app j k h).app l m hlm = _
  erw [comp_app, map_η_app (I:=K) (map (I:=J) F), map_η_app (I:=J) F]
  rfl

lemma map_map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    map (I:=L) (map (I:=K) (map (I:=J) F)) ⋙ map (map (reindex f)) =
      map (map (reindex f)) ⋙ map (map (map (I:=I) F)) := by
  have he (X : Diagram (Diagram C J) K) :
      mapObj (map F) (mapObj (reindex f) X) = mapObj (reindex f) (mapObj (map F) X) :=
    congrArg (fun T => T.obj X) (map_map_reindex F f).symm
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq ?_ ?_ ?_
    · funext i j h; exact (he _).symm
    · apply hfunext; intro i
      apply iso_hext (he _).symm rfl
      apply hom_hext (he _).symm rfl
      intro j k h
      apply hom_hext rfl rfl
      intro l m hlm
      apply heq_of_eq
      erw [map_reindex_unit_app, map_triple_unit_app,
        map_triple_unit_app, map_reindex_unit_app]
      rfl
    · apply hfunext; intro i
      apply hfunext; intro j
      apply hfunext; intro k
      apply hfunext; intro hij
      apply hfunext; intro hjk
      apply iso_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _).symm (he _).symm) (he _).symm
      apply hom_hext (congrArg₂ (fun X Y => X ⊗ Y) (he _).symm (he _).symm) (he _).symm
      intro l m hlm
      apply hom_hext rfl rfl
      intro n p hnp
      apply heq_of_eq
      change 𝟙 _ ≫ (Functor.LaxMonoidal.μ F _ _ ≫
          F.map (((A.cut i j k hij hjk).hom.app l m hlm).app (f n) (f p) _)) =
        Functor.LaxMonoidal.μ F _ _ ≫
          F.map (𝟙 _ ≫ ((A.cut i j k hij hjk).hom.app l m hlm).app (f n) (f p) _)
      erw [Category.id_comp, Category.id_comp]
  · intro A B g
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro k l hkl
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    apply Hom.ext; intro m n hmn
    erw [comp_app, comp_app, eqToHom_app, eqToHom_app]
    simp only [map,reindex]
    erw [Category.id_comp, Category.comp_id]
    rfl
lemma barMap_map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    barMap (map (I:=K) (map (I:=J) F)) ≫ barMap (map (reindex f)) =
      barMap (map (reindex f)) ≫ barMap (map (map (I:=I) F)) := by
  have he : simplicialMap (map (I:=K) (map (I:=J) F)) ≫ simplicialMap (map (reindex f)) =
      simplicialMap (map (reindex f)) ≫ simplicialMap (map (map (I:=I) F)) := by
    apply NatTrans.ext; funext p; apply Cat.ext
    exact map_map_map_reindex F f
  have h := congrArg SimplicialDiagonal.nerveDiagonal.map he
  erw [Functor.map_comp, Functor.map_comp] at h
  exact h
lemma bar₂Map_map_reindex (F : C ⥤ D) [F.Braided] (f : I →o J) :
    bar₂Map (map (I:=J) F) ≫ bar₂Map (reindex f) =
      bar₂Map (reindex f) ≫ bar₂Map (map (I:=I) F) := by
  have he : rows₂Map (map (I:=J) F) ≫ rows₂Map (reindex f) =
      rows₂Map (reindex f) ≫ rows₂Map (map (I:=I) F) := by
    apply NatTrans.ext; funext p
    exact barMap_map_map_reindex F f
  have h := congrArg SimplicialDiagonal.diagonal.map he
  erw [Functor.map_comp, Functor.map_comp] at h
  exact h
noncomputable def rows₃Map (F : C ⥤ D) [F.Braided] : rows₃ (C:=C) ⟶ rows₃ (C:=D) where
  app p := bar₂Map (map (I:=Fin (p.unop.len+1)) F)
  naturality _ _ f := (bar₂Map_map_reindex F f.unop.toOrderHom).symm
noncomputable def bar₃Map (F : C ⥤ D) [F.Braided] : bar₃ (C:=C) ⟶ bar₃ (C:=D) :=
  SimplicialDiagonal.diagonal.map (rows₃Map F)
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D E : Type} [Groupoid.{0} C] [Groupoid.{0} D] [Groupoid.{0} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
  (F:C ⥤ D) (G:D ⥤ E) [F.Braided] [G.Braided]
lemma map_unit_component (A : Diagram (Diagram C I) J) (i : J)
    (j k : I) (h : j ≤ k) :
    ((mapObj (map F) A).unit i).hom.app j k h =
      F.map ((A.unit i).hom.app j k h) ≫ Functor.OplaxMonoidal.η F := by
  change ((map F).map (A.unit i).hom ≫ Functor.OplaxMonoidal.η (map F)).app j k h = _
  erw [comp_app, map_η_app (I:=I) F]
  rfl

lemma map_cut_component (A : Diagram (Diagram C I) J) (i j k : J)
    (hij : i ≤ j) (hjk : j ≤ k) (l m : I) (h : l ≤ m) :
    ((mapObj (map F) A).cut i j k hij hjk).hom.app l m h =
      Functor.LaxMonoidal.μ F ((A.obj i j hij).obj l m h) ((A.obj j k hjk).obj l m h) ≫
        F.map ((A.cut i j k hij hjk).hom.app l m h) := rfl

lemma map₂_comp_obj (A : Diagram (Diagram C I) J) :
    mapObj (map (I:=I) (F⋙G)) A=mapObj (map G) (mapObj (map F) A) := by
  have he (X : Diagram C I) := mapObj_comp F G X
  refine ext_heq ?_ ?_ ?_
  · funext i j h; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j k h
    apply heq_of_eq
    erw [map_unit_component, map_unit_component, map_unit_component]
    simp only [Functor.comp_map, Functor.OplaxMonoidal.comp_η]
    erw [Functor.map_comp, Category.assoc]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro k
    apply hfunext; intro hij
    apply hfunext; intro hjk
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro l m h
    apply heq_of_eq
    erw [map_cut_component, map_cut_component, map_cut_component]
    simp only [Functor.LaxMonoidal.comp_μ]
    erw [Functor.map_comp, Category.assoc]
    rfl

end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower

variable {C : Type} (κ : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
open IntervalBar IntervalBar.Diagram StageProductColimit
noncomputable def tripleProject (l m n:ℕ) :
    Diagram (Diagram (Diagram (κ → C) (Fin (n+1))) (Fin (m+1))) (Fin (l+1)) ⥤
      (κ → Diagram (Diagram (Diagram C (Fin (n+1))) (Fin (m+1))) (Fin (l+1))) :=
  Functor.pi' (fun k => map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) (project κ k))))
lemma tripleProject_eval (l m n:ℕ) :
    tripleProject (C:=C) κ l m n ⋙ powerMap κ (eval₃ l m n) =
      eval₃ l m n ⋙ swap (Fin l × (Fin m × Fin n)) κ := rfl
noncomputable instance instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject (l m n:ℕ) : (tripleProject (C:=C) κ l m n).IsEquivalence := by
  have : (tripleProject (C:=C) κ l m n ⋙ powerMap κ (eval₃ l m n)).IsEquivalence := by
    rw [tripleProject_eval]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (powerMap κ (eval₃ l m n))
end BarFinitePower

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageRefinementMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
namespace IntervalBar.Diagram

universe u v u' v' w
variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
    {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
    {F G : C ⥤ D} [F.Braided] [G.Braided]
    {I : Type w} [Preorder I]

noncomputable def mapNatTrans (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    map (I:=I) F ⟶ map G where
  app A := {
    app i j h := α.app (A.obj i j h)
    unit i := by
      change α.app _ ≫ (G.map (A.unit i).hom ≫ η G) = F.map (A.unit i).hom ≫ η F
      rw [←Category.assoc,←α.naturality,Category.assoc,monoidalNatTrans_eta]
    cut i j k hij hjk := by
      change (α.app _ ⊗ₘ α.app _) ≫ (μ G _ _ ≫ G.map (A.cut i j k hij hjk).hom)=
        (μ F _ _ ≫ F.map (A.cut i j k hij hjk).hom) ≫ α.app _
      rw [←Category.assoc,←NatTrans.IsMonoidal.tensor,Category.assoc,←α.naturality,Category.assoc] }
  naturality _ _ f := by
    apply Hom.ext
    intro i j h
    exact α.naturality (f.app i j h)

instance mapNatTrans_monoidal (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    NatTrans.IsMonoidal (mapNatTrans (I:=I) α) where
  unit := by
    apply Hom.ext
    intro i j h
    exact NatTrans.IsMonoidal.unit (τ:=α)
  tensor A B := by
    apply Hom.ext
    intro i j h
    exact NatTrans.IsMonoidal.tensor (τ:=α) _ _
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace NerveHomotopy
universe u v
variable {C D C' D' : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} C'] [Category.{v} D']
variable {F G : C ⥤ D} {F' G' : C' ⥤ D'}
variable (R:C⥤C') (S:D⥤D') (α:F⟶G) (α':F'⟶G')
    (eF:F⋙S=R⋙F') (eG:G⋙S=R⋙G')
    (eα:∀ X,HEq (S.map (α.app X)) (α'.app (R.obj X)))
include eF eG eα
lemma cylinder_natural : cylinder α ⋙ S = R.prod (𝟭 (Fin 2)) ⋙ cylinder α' := by
  apply CategoryTheory.Functor.hext
  · rintro ⟨X,i⟩
    fin_cases i
    · exact congrArg (fun H=>H.obj X) eF
    · exact congrArg (fun H=>H.obj X) eG
  · rintro ⟨X,i⟩ ⟨Y,j⟩ f
    have hij : i≤j := leOfHom f.2
    fin_cases i <;> fin_cases j
    · change HEq (S.map (F.map f.1 ≫ 𝟙 _)) (F'.map (R.map f.1) ≫ 𝟙 _)
      simp only [Category.comp_id]
      exact functor_map_heq eF f.1
    · change HEq (S.map (F.map f.1 ≫ α.app Y)) (F'.map (R.map f.1) ≫ α'.app (R.obj Y))
      rw [S.map_comp]
      exact comp_heq (congrArg (fun H=>H.obj X) eF) (congrArg (fun H=>H.obj Y) eF)
        (congrArg (fun H=>H.obj Y) eG) (functor_map_heq eF f.1) (eα Y)
    · simp at hij
    · change HEq (S.map (G.map f.1 ≫ 𝟙 _)) (G'.map (R.map f.1) ≫ 𝟙 _)
      simp only [Category.comp_id]
      exact functor_map_heq eG f.1
end NerveHomotopy

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J : Type} [Preorder I] [Preorder J]
noncomputable def diagonalReindex (f : I →o J) :
    Diagram (Diagram (Diagram C J) J) J ⥤ Diagram (Diagram (Diagram C I) I) I :=
  map (map (reindex f)) ⋙ map (reindex f) ⋙ reindex f
noncomputable abbrev map₃ (F : C ⥤ D) [F.Braided] (I : Type) [Preorder I] :=
  map (I:=I) (map (I:=I) (map (I:=I) F))
lemma map₃_diagonalReindex (F:C⥤D) [F.Braided] (f:I→o J) :
    map₃ F J ⋙ diagonalReindex f = diagonalReindex f ⋙ map₃ F I := by
  dsimp only [diagonalReindex,map₃]
  simp only [CategoryTheory.Functor.assoc]
  conv_lhs =>
    rw [←CategoryTheory.Functor.assoc,map_map_map_reindex,CategoryTheory.Functor.assoc]
    enter [2]
    rw [←CategoryTheory.Functor.assoc,map_map_reindex,CategoryTheory.Functor.assoc]
    enter [2]
    rw [←reindex_map]

lemma bar₃_map (n m : SimplexCategoryᵒᵖ) (f : n⟶m) (x : (bar₃ (C:=C)).obj n) :
    (bar₃ (C:=C)).map f x = f.unop.toOrderHom.toFunctor ⋙ x ⋙ diagonalReindex f.unop.toOrderHom := by
  rfl

variable {F G:C⥤D} [F.Braided] [G.Braided]
noncomputable def natTrans₃ (α:F⟶G) [NatTrans.IsMonoidal α] (I:Type) [Preorder I] : map₃ F I ⟶ map₃ G I :=
  mapNatTrans (mapNatTrans (mapNatTrans α))
lemma natTrans₃_reindex (α:F⟶G) [NatTrans.IsMonoidal α] (f:I→o J)
    (A : Diagram (Diagram (Diagram C J) J) J) :
    HEq ((diagonalReindex f).map ((natTrans₃ α J).app A)) ((natTrans₃ α I).app ((diagonalReindex f).obj A)) := by
  have eF := congrArg (fun H=>H.obj A) (map₃_diagonalReindex F f)
  have eG := congrArg (fun H=>H.obj A) (map₃_diagonalReindex G f)
  apply hom_hext eF eG
  intro i j hij
  have eF' := congrArg (fun X=>X.obj i j hij) eF
  have eG' := congrArg (fun X=>X.obj i j hij) eG
  apply hom_hext eF' eG'
  intro k l hkl
  have eF'' := congrArg (fun X=>X.obj k l hkl) eF'
  have eG'' := congrArg (fun X=>X.obj k l hkl) eG'
  apply hom_hext eF'' eG''
  intro p q hpq
  rfl
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
  {F G : C ⥤ D} [F.Braided] [G.Braided]
noncomputable def tripleNatTrans (α : F ⟶ G) [NatTrans.IsMonoidal α] (n : ℕ) :
    map (I:=Fin (n+1)) (map (I:=Fin (n+1)) (map (I:=Fin (n+1)) F)) ⟶
      map (I:=Fin (n+1)) (map (I:=Fin (n+1)) (map (I:=Fin (n+1)) G)) :=
  mapNatTrans (mapNatTrans (mapNatTrans α))

end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PowerDiagonal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.connected _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite
namespace BarFinitePower
open SimplicialDiagonal

variable (κ : Type) {X Y : SimplexCategoryᵒᵖ ⥤ SSet}
lemma homologyLiftDiagonal_isIso (f : κ → (X ⟶ Y))
    (h : ∀p n, IsIso (SSet.homologyMap (lift κ (fun k => (f k).app p)) DiagonalResolution.Z n)) (n:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k => diagonal.map (f k))) DiagonalResolution.Z n) := by
  rw [liftDiagonal]
  apply homologyMap_isIso
  exact h
end BarFinitePower

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram SimplicialDiagonal

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] (κ : Type)
noncomputable def triplePowerComparison : bar₃ (C:=κ → C) ⟶ (power κ).obj (bar₃ (C:=C)) :=
  lift κ (fun k => bar₃Map (project κ k))
lemma tripleDegree_homology_isIso (l m p k:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun j => nerveMap
      (map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j))))))
      DiagonalResolution.Z k) := by
  have : (Functor.pi' (fun j => map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j))))).IsEquivalence :=
    inferInstanceAs (tripleProject (C:=C) κ l m p).IsEquivalence
  exact lift_nerve_homology_isIso κ (fun j => map (I:=Fin (l+1))
      (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j)))) k
lemma tripleBarOne_homology_isIso (m p k:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun j => barMap
      (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (project (C:=C) κ j))))) DiagonalResolution.Z k) := by
  apply homologyLiftDiagonal_isIso κ (fun j =>
    Functor.whiskerRight (simplicialMap (map (I:=Fin (m+1))
      (map (I:=Fin (p+1)) (project (C:=C) κ j)))) nerveFunctor)
  intro l q
  exact tripleDegree_homology_isIso κ l.unop.len m p q
lemma tripleBarTwo_homology_isIso (p k:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun j => bar₂Map
      (map (I:=Fin (p+1)) (project (C:=C) κ j)))) DiagonalResolution.Z k) := by
  apply homologyLiftDiagonal_isIso κ (fun j => rows₂Map (map (I:=Fin (p+1)) (project (C:=C) κ j)))
  intro m q
  exact tripleBarOne_homology_isIso κ m.unop.len p q

lemma triplePowerComparison_homology_isIso (n:ℕ) :
    IsIso (SSet.homologyMap (triplePowerComparison (C:=C) κ) DiagonalResolution.Z n) := by
  apply homologyLiftDiagonal_isIso κ (fun k => rows₃Map (project (C:=C) κ k))
  intro p q
  exact tripleBarTwo_homology_isIso κ p.unop.len q
end BarFinitePower

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PiSSet
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentTranslation.fiber_nerve_connected _root_.OAI.ComponentTranslation.fiber_nonempty _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.GroupoidComponentHomology.fiberInclusion_essSurj _root_.OAI.GroupoidComponentHomology.fiberInclusion_faithful _root_.OAI.GroupoidComponentHomology.fiberInclusion_full _root_.OAI.GroupoidComponentHomology.fiberInclusion_isEquivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet
open FreeChains

variable {ι:Type} (X:ι→SSet)
noncomputable def finZeroIso (X:Fin 0→SSet) : obj X ≅ ConnectedProduct.one where
  hom := { app _ := ↾fun _=>PUnit.unit
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun _ i=>Fin.elim0 i
           naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0 }
  hom_inv_id := by apply NatTrans.ext; funext p; apply ConcreteCategory.hom_ext; intro x; funext i; exact i.elim0
  inv_hom_id := by ext p x; rfl
lemma fin_connected (n:ℕ) (X:Fin n→SSet) (hX:∀i,(X i).IsConnected) : (obj X).IsConnected := by
  induction n with
  | zero => exact BarFinitePower.connected_of_iso _ (finZeroIso X)
  | succ n ih =>
    have := hX 0
    have := ih (fun i=>X i.succ) (fun i=>hX i.succ)
    exact BarFinitePower.connected_of_iso _ (finSuccIso X)
lemma biprod_element_ext {M N:A} (a b:(M ⊞ N : A))
    (hf:(biprod.fst : M ⊞ N ⟶ M) a=(biprod.fst : M ⊞ N ⟶ M) b)
    (hs:(biprod.snd : M ⊞ N ⟶ N) a=(biprod.snd : M ⊞ N ⟶ N) b) : a=b := by
  have ha:=congrArg (fun f:(M ⊞ N)⟶(M ⊞ N)=>f a) (biprod.total (X:=M) (Y:=N))
  have hb:=congrArg (fun f:(M ⊞ N)⟶(M ⊞ N)=>f b) (biprod.total (X:=M) (Y:=N))
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) a) +
    (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) a)=a at ha
  change (biprod.inl : M ⟶ M ⊞ N) ((biprod.fst : M ⊞ N ⟶ M) b) +
    (biprod.inr : N ⟶ M ⊞ N) ((biprod.snd : M ⊞ N ⟶ N) b)=b at hb
  rw [←ha,←hb,hf,hs]
lemma homology_ext (n:ℕ) (X:Fin n→SSet) (hX:∀i,(X i).IsConnected)
    (a b:((obj X).homology Z 1 : A)) (h:∀i,SSet.homologyMap (proj X i) Z 1 a=SSet.homologyMap (proj X i) Z 1 b) : a=b := by
  induction n with
  | zero =>
    have hz : IsZero ((obj X).homology Z 1) :=
      IsZero.of_iso (ConnectedProduct.one_homology_zero 1 (by decide))
        ((SSet.homologyFunctor Z 1).mapIso (finZeroIso X))
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _
  | succ n ih =>
    have := hX 0
    have := fin_connected n (fun i=>X i.succ) (fun i=>hX i.succ)
    have := ConnectedProduct.projection_isIso_arbitrary (X 0) (obj (fun i:Fin n=>X i.succ))
      1 1 1 (by omega) (by omega) (by intros; omega) (by intros; omega)
    let e := (SSet.homologyFunctor Z 1).mapIso (finSuccIso X)
    apply e.toLinearEquiv.injective
    apply (ConcreteCategory.bijective_of_isIso (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1)).1
    apply biprod_element_ext
    · change (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.fst) (e.hom a)=
        (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.fst) (e.hom b)
      rw [ConnectedProduct.projection,biprod.lift_fst]
      change (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.fst _ _) Z 1) a =
        (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.fst _ _) Z 1) b
      rw [←SSet.homologyMap_comp,finSucc_fst]
      exact h 0
    · change (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.snd) (e.hom a)=
        (ConnectedProduct.projection (X 0) (obj (fun i:Fin n=>X i.succ)) 1 ≫ biprod.snd) (e.hom b)
      rw [ConnectedProduct.projection,biprod.lift_snd]
      apply ih (fun i=>X i.succ) (fun i=>hX i.succ)
      intro i
      change (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.snd _ _) Z 1 ≫
        SSet.homologyMap (proj (fun i:Fin n=>X i.succ) i) Z 1) a =
        (SSet.homologyMap (finSuccIso X).hom Z 1 ≫
        SSet.homologyMap (CartesianMonoidalCategory.snd _ _) Z 1 ≫
        SSet.homologyMap (proj (fun i:Fin n=>X i.succ) i) Z 1) b
      rw [←SSet.homologyMap_comp,←SSet.homologyMap_comp,finSucc_snd]
      exact h i.succ
end PiSSet

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentTranslation
open FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma homology_one (p:P C) (h:(1:P C)*p=p) (j:ℕ) :
    SSet.homologyMap (nerveMap (translate 1 p p h)) Z j=𝟙 _ := by
  have h:=(NerveHomotopy.ofNatTrans (translateOne p h)).congr_homologyMap Z j
  change SSet.homologyMap (nerveMap (translate 1 p p _)) Z j=SSet.homologyMap (𝟙 _) Z j at h
  simpa only [SSet.homologyMap_id] using h
omit [SymmetricCategory C] in
lemma homology_comp {p q t:P C} (r s:P C) (h:r*p=q) (k:s*q=t) (l:(s*r)*p=t) (j:ℕ) :
    SSet.homologyMap (nerveMap (translate (s*r) p t l)) Z j =
      SSet.homologyMap (nerveMap (translate r p q h)) Z j ≫
      SSet.homologyMap (nerveMap (translate s q t k)) Z j := by
  have hh:=(NerveHomotopy.ofNatTrans (translateComp r s h k l)).congr_homologyMap Z j
  change SSet.homologyMap (nerveMap (translate (s*r) p t l)) Z j =
    SSet.homologyMap (nerveMap (translate r p q h) ≫ nerveMap (translate s q t k)) Z j at hh
  simpa only [SSet.homologyMap_comp] using hh
noncomputable def homologyDiagram (j:ℕ) : ActionCategory (P C) (P C) ⥤ A where
  obj p := (nerve (Fiber p.back)).homology Z j
  map {p q} f := SSet.homologyMap (nerveMap (translate f.val p.back q.back f.property)) Z j
  map_id p := homology_one p.back _ j
  map_comp f g := homology_comp (f.val:P C) (g.val:P C) f.property g.property _ j
end ComponentTranslation

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ExactShapeHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace ComponentCoproduct
open ComponentTranslation FreeChains

variable (C:Type) [Groupoid.{0} C]
noncomputable def homologyIsColimit (q:ℕ) :
    IsColimit ((SSet.homologyFunctor Z q).mapCocone (cocone C)) :=
  isColimitOfPreserves _ (isColimit C)
end ComponentCoproduct

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentTranslation.fiber_nerve_connected _root_.OAI.ComponentTranslation.fiber_nonempty _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.GroupoidComponentHomology.fiberInclusion_essSurj _root_.OAI.GroupoidComponentHomology.fiberInclusion_faithful _root_.OAI.GroupoidComponentHomology.fiberInclusion_full _root_.OAI.GroupoidComponentHomology.fiberInclusion_isEquivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable abbrev H (q:ℕ) := SSet.homologyFunctor Z q
noncomputable abbrev object (q:ℕ) := colimit (homologyDiagram (C:=C) q)
noncomputable def inclusion (p:Skeleton C) (q:ℕ) :
    (nerve (Fiber p)).homology Z q ⟶ (nerve C).homology Z q :=
  SSet.homologyMap (nerveMap (property p).ι) Z q
noncomputable def unionCocone (q:ℕ) :
    Cocone (ComponentCoproduct.diagram C ⋙ H q) where
  pt := object (C:=C) q
  ι := Discrete.natTrans (fun p=>colimit.ι (homologyDiagram (C:=C) q) ((ActionCategory.objEquiv _ _) p.as))
noncomputable def toStable (q:ℕ) : (nerve C).homology Z q ⟶ object (C:=C) q :=
  (ComponentCoproduct.homologyIsColimit C q).desc (unionCocone q)
omit [SymmetricCategory C] in
@[reassoc (attr:=simp)] lemma inclusion_toStable (p:Skeleton C) (q:ℕ) :
    inclusion p q ≫ toStable q=colimit.ι (homologyDiagram q) ((ActionCategory.objEquiv _ _) p) :=
  (ComponentCoproduct.homologyIsColimit C q).fac (unionCocone q) ⟨p⟩
instance epi_toStable (q:ℕ) : Epi (toStable (C:=C) q) where
  left_cancellation f g h := by
    apply colimit.hom_ext
    intro stage
    obtain ⟨component,rfl⟩ := (ActionCategory.objEquiv (Skeleton C) (Skeleton C)).surjective stage
    have hp:=congrArg (fun k=>inclusion component q ≫ k) h
    simp only [←Category.assoc,inclusion_toStable] at hp
    change colimit.ι (homologyDiagram (C:=C) q) ((ActionCategory.objEquiv _ _) component) ≫ f =
      colimit.ι (homologyDiagram (C:=C) q) ((ActionCategory.objEquiv _ _) component) ≫ g
    exact hp
omit [SymmetricCategory C] in
lemma translate_toStable (r p s:Skeleton C) (h:r*p=s) (q:ℕ) :
    SSet.homologyMap (nerveMap (translate r p s h)) Z q ≫ inclusion s q ≫ toStable q =
      inclusion p q ≫ toStable q := by
  rw [inclusion_toStable,inclusion_toStable]
  exact colimit.w (homologyDiagram q) (show (ActionCategory.objEquiv _ _) p ⟶
    (ActionCategory.objEquiv _ _) s from ⟨r,h⟩)
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_NerveProduct
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def binaryD (q:ℕ) : (nerve C⊗nerve C).homology Z q ⟶ object (C:=C) q :=
  (SSet.homologyMap (CartesianMonoidalCategory.fst _ _) Z q +
    SSet.homologyMap (CartesianMonoidalCategory.snd _ _) Z q -
      SSet.homologyMap multiplication Z q) ≫ toStable q
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_BinaryPullback
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace ComponentStable
open FreeChains ComponentTranslation ConnectedProduct

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {X Y X' Y':SSet}
noncomputable def pullD (f:X⟶nerve C) (g:Y⟶nerve C) (q:ℕ) :
    (X⊗Y).homology Z q ⟶ object (C:=C) q := SSet.homologyMap (f⊗ₘg) Z q ≫ binaryD q
omit [SymmetricCategory C] in
@[reassoc] lemma pullD_comp (f:X⟶X') (g:Y⟶Y') (F:X'⟶nerve C) (G:Y'⟶nerve C) (q:ℕ) :
    SSet.homologyMap (f⊗ₘg) Z q ≫ pullD F G q=pullD (f≫F) (g≫G) q := by
  rw [pullD,←SSet.homologyMap_comp_assoc,tensorHom_comp_tensorHom, pullD]
end ComponentStable

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PiFiber
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiFiber
open ComponentTranslation FreeChains

variable (C:Type) [Groupoid.{0} C] (ι:Type)
noncomputable def homologyIsColimit (q:ℕ) :
    IsColimit ((SSet.homologyFunctor Z q).mapCocone (cocone C ι)) :=
  isColimitOfPreserves _ (isColimit C ι)
end PiFiber

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PiH1Coproduct
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.GroupoidComponentHomology.fiberInclusion_essSurj _root_.OAI.GroupoidComponentHomology.fiberInclusion_faithful _root_.OAI.GroupoidComponentHomology.fiberInclusion_full _root_.OAI.GroupoidComponentHomology.fiberInclusion_isEquivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace PiSSet
open FreeChains

variable {n:ℕ} (X:Fin n→SSet) (x:∀i,(X i).obj (op ⦋0⦌))
noncomputable def h1Cocone : Cofan (fun i=>(X i).homology Z 1) :=
  Cofan.mk ((obj X).homology Z 1) (fun i=>SSet.homologyMap (incl X x i) Z 1)
lemma incl_proj_h1 (i j:Fin n) :
    SSet.homologyMap (incl X x i) Z 1 ≫ SSet.homologyMap (proj X j) Z 1=
      if h:i=j then eqToHom (congrArg (fun i=>(X i).homology Z 1) h) else 0 := by
  classical
  rw [←SSet.homologyMap_comp]
  by_cases h:i=j
  · subst j; simp
  · rw [incl_other X x h,ConnectedProduct.const_homology_zero _ 1 (by decide)]
    simp [h]
lemma h1_decomposition (hX:∀i,(X i).IsConnected) :
    ∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ SSet.homologyMap (incl X x i) Z 1=𝟙 _ := by
  classical
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply homology_ext n X hX
  intro j
  change ((∑ i:Fin n, SSet.homologyMap (proj X i) Z 1 ≫ SSet.homologyMap (incl X x i) Z 1) ≫
      SSet.homologyMap (proj X j) Z 1) a=SSet.homologyMap (proj X j) Z 1 a
  rw [Preadditive.sum_comp]
  simp_rw [Category.assoc]
  rw [Finset.sum_eq_single j]
  · rw [incl_proj_h1]; simp
  · intro i hi hij; rw [incl_proj_h1]; simp [hij]
  · simp
noncomputable def h1IsColimit (hX:∀i,(X i).IsConnected) : IsColimit (h1Cocone X x) where
  desc s := ∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ s.ι.app ⟨i⟩
  fac s j := by
    classical
    cases j with | mk j =>
      change SSet.homologyMap (incl X x j) Z 1 ≫
        (∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ s.ι.app ⟨i⟩)=s.ι.app ⟨j⟩
      rw [Preadditive.comp_sum,Finset.sum_eq_single j]
      · rw [←Category.assoc,incl_proj_h1]; simp
      · intro i hi hij; rw [←Category.assoc,incl_proj_h1]; simp [Ne.symm hij]
      · simp
  uniq s f hf := by
    dsimp only [h1Cocone, Cofan.mk_pt] at f hf ⊢
    change f = ∑ i:Fin n,SSet.homologyMap (proj X i) Z 1 ≫ s.ι.app ⟨i⟩
    rw [←Category.id_comp f,←h1_decomposition X x hX,Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Category.assoc]
    exact congrArg (fun g=>SSet.homologyMap (proj X i) Z 1 ≫ g) (hf ⟨i⟩)
end PiSSet

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def evalIso (n:ℕ) :
    (nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 ≅
      (PiFiber.prod C (Fin n)).homology Z 1 := by
  haveI := NerveHomotopy.homologyMap_isIso (IntervalBar.Diagram.eval (C:=C) n) Z 1
  exact asIso (SSet.homologyMap (nerveMap (IntervalBar.Diagram.eval (C:=C) n)) Z 1) ≪≫
    (SSet.homologyFunctor Z 1).mapIso (PiSSet.nervePiIso (fun _:Fin n=>C))
noncomputable def primitive {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    (nerve (Fiber (p i))).homology Z 1 ⟶
      (nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 :=
  SSet.homologyMap (PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i) Z 1 ≫
    SSet.homologyMap (PiFiber.inclusion C (Fin n) p) Z 1 ≫ (evalIso n).inv
omit [SymmetricCategory C] in
lemma hom_ext {n:ℕ} {M:A}
    {f g:(nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 ⟶ M}
    (h:∀ (p:Fin n→Skeleton C) (i:Fin n),primitive p i ≫ f=primitive p i ≫ g) : f=g := by
  apply (cancel_epi (evalIso n).inv).mp
  apply (PiFiber.homologyIsColimit C (Fin n) 1).hom_ext
  intro p
  apply (PiSSet.h1IsColimit (fun i=>nerve (Fiber (p.as i))) (points p.as) (fun _=>inferInstance)).hom_ext
  intro i
  exact (Category.assoc _ _ _).symm.trans ((h p.as i.as).trans (Category.assoc _ _ _))
noncomputable def descCocone {n:ℕ} {M:A}
    (f:∀ (p:Fin n→Skeleton C) (i:Fin n),(nerve (Fiber (p i))).homology Z 1 ⟶ M) :
    Cocone (PiFiber.diagram C (Fin n) ⋙ SSet.homologyFunctor Z 1) where
  pt := M
  ι := Discrete.natTrans (fun p => (PiSSet.h1IsColimit (fun i=>nerve (Fiber (p.as i))) (points p.as) (fun _=>inferInstance)).desc
      (Cofan.mk M (f p.as)))
noncomputable def desc {n:ℕ} {M:A}
    (f:∀ (p:Fin n→Skeleton C) (i:Fin n),(nerve (Fiber (p i))).homology Z 1 ⟶ M) :
    (nerve (IntervalBar.Diagram C (Fin (n+1)))).homology Z 1 ⟶ M :=
  (evalIso n).hom ≫ (PiFiber.homologyIsColimit C (Fin n) 1).desc (descCocone f)
omit [SymmetricCategory C] in
@[reassoc (attr:=simp)] lemma primitive_desc {n:ℕ} {M:A}
    (f:∀ (p:Fin n→Skeleton C) (i:Fin n),(nerve (Fiber (p i))).homology Z 1 ⟶ M)
    (p:Fin n→Skeleton C) (i:Fin n) : primitive p i ≫ desc f=f p i := by
  let coordinateMap : (nerve (Fiber (p i))).homology Z 1 ⟶
      (PiFiber.piece C (Fin n) p).homology Z 1 :=
    SSet.homologyMap (PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i) Z 1
  let inclusionMap : (PiFiber.piece C (Fin n) p).homology Z 1 ⟶
      (PiFiber.prod C (Fin n)).homology Z 1 :=
    SSet.homologyMap (PiFiber.inclusion C (Fin n) p) Z 1
  let coconeDesc : (PiFiber.prod C (Fin n)).homology Z 1 ⟶ M :=
    (PiFiber.homologyIsColimit C (Fin n) 1).desc (descCocone f)
  change (coordinateMap ≫ inclusionMap ≫ (evalIso n).inv) ≫
    (evalIso n).hom ≫ coconeDesc = f p i
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  have h:=(PiFiber.homologyIsColimit C (Fin n) 1).fac (descCocone f) ⟨p⟩
  change inclusionMap ≫ coconeDesc = _ at h
  rw [h]
  exact (PiSSet.h1IsColimit (fun j=>nerve (Fiber (p j))) (points p) (fun _=>inferInstance)).fac
    (Cofan.mk M (f p)) ⟨i⟩
end MarkedH1

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_GroupNerveCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Simplicial SimplicialObject Opposite AlgebraicTopology
open scoped BigOperators
namespace GroupNerveCoordinates
open FreeChains

attribute [local instance 1200] Rep.hV2
variable (G : Type) [Group G]
noncomputable def chainCoordinates (n:ℕ) :
    (complex (nerve (SingleObj G))).X n ≅
      (groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).X n :=
  (Finsupp.domLCongr (M:=ℤ) (R:=ℤ) (equiv G n)).toModuleIso
lemma coordinates_single (n:ℕ) (F:ComposableArrows (SingleObj G) n) (z:ℤ) :
    (chainCoordinates G n).hom (Finsupp.single F z) = Finsupp.single (labels F) z :=
  Finsupp.domLCongr_single _ _ _
lemma coordinates_d (n:ℕ) :
    (complex (nerve (SingleObj G))).d (n+1) n ≫ (chainCoordinates G n).hom =
      (chainCoordinates G (n+1)).hom ≫
        (groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ)).d (n+1) n := by
  classical
  rw [groupHomology.inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro F
  apply LinearMap.ext
  intro z
  change (chainCoordinates G n).hom.hom (((complex (nerve (SingleObj G))).d (n+1) n).hom
      (Finsupp.single F z)) = _
  rw [show (complex (nerve (SingleObj G))).d (n+1) n =
    ∑ i:Fin (n+2), (-1:ℤ)^(i:ℕ) • (ModuleCat.free ℤ).map ((nerve (SingleObj G)).δ i) from
    AlternatingFaceMapComplex.obj_d_eq _ n]
  erw [ModuleCat.hom_sum]
  change (Finsupp.domLCongr (M:=ℤ) (R:=ℤ) (equiv G n))
    ((∑ index:Fin (n+2), (-1:ℤ)^(index:ℕ) •
      Finsupp.lmapDomain (α:=ComposableArrows (SingleObj G) (n+1))
        (α':=ComposableArrows (SingleObj G) n) ℤ ℤ ((nerve (SingleObj G)).δ index))
      (Finsupp.single F z)) = _
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_zsmul]
  have hmap (i:Fin (n+2)) : (chainCoordinates G n).hom
      ((ModuleCat.free ℤ).map ((nerve (SingleObj G)).δ i) (Finsupp.single F z)) =
      Finsupp.single (labels ((nerve (SingleObj G)).δ i F)) z := by
    change (Finsupp.domLCongr (equiv G n))
      (Finsupp.lmapDomain ℤ ℤ ((nerve (SingleObj G)).δ i) (Finsupp.single F z)) = _
    rw [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
    exact Finsupp.domLCongr_single _ _ _
  change (∑ i:Fin (n+2), (-1:ℤ)^(i:ℕ) • (chainCoordinates G n).hom
        ((ModuleCat.free ℤ).map ((nerve (SingleObj G)).δ i) (Finsupp.single F z))) = _
  simp only [hmap]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_zsmul,Fin.val_succ]
  change _ = groupHomology.inhomogeneousChains.d (Rep.trivial ℤ G ℤ) n
    ((chainCoordinates G (n+1)).hom (Finsupp.single F z))
  erw [coordinates_single,groupHomology.inhomogeneousChains.d_single]
  apply congrArg₂ (· + ·)
  · exact congrArg (fun faceLabels => Finsupp.single faceLabels z) (labels_zero_face F)
  · apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun faceLabels => (-1:ℤ)^((index:ℕ)+1) • Finsupp.single faceLabels z)
      (labels_succ_face F index)
noncomputable def chainIso : complex (nerve (SingleObj G)) ≅
    groupHomology.inhomogeneousChains (Rep.trivial ℤ G ℤ) := by
  refine HomologicalComplex.Hom.isoOfComponents (chainCoordinates G) ?_
  rintro n m rfl
  exact (coordinates_d G m).symm
noncomputable def homologyIso (n:ℕ) :
    (nerve (SingleObj G)).homology Z n ≅ groupHomology (Rep.trivial ℤ G ℤ) n :=
  (HomologicalComplex.homologyFunctor A c n).mapIso (complexIso _ ≪≫ chainIso G)
end GroupNerveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_GroupoidComponentHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace GroupoidComponentHomology
open FreeChains ComponentTranslation SimpleAmenable

variable {C:Type} [Groupoid.{0} C]
noncomputable def fiberIsoHomology {p:Skeleton C} (U:Fiber p) (q:ℕ) :
    groupHomology (Rep.trivial ℤ (Aut U.obj) ℤ) q ≅ (nerve (Fiber p)).homology Z q := by
  haveI := NerveHomotopy.homologyMap_isIso (fiberInclusion U) Z q
  exact (GroupNerveCoordinates.homologyIso (Aut U.obj) q).symm ≪≫
    asIso (SSet.homologyMap (nerveMap (fiberInclusion U)) Z q)
end GroupoidComponentHomology

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_CoefficientNaturality
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CoefficientNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
open ExactShapeHomology

variable {C:Type} [Category.{0} C]
noncomputable def rowIso (L:ChainComplex (C ⥤ A) ℕ) (q:ℕ) :
    TotalFiniteness.row (double L) q ≅ complex (L.homology q) := by
  exact eqToIso (congrArg (fun T => T.obj (chainSimplicial L))
    (map_alternatingFaceMapComplex (homologyFunctor A c q))) ≪≫
      (alternatingFaceMapComplex A).mapIso (chainSimplicialHomology L q)
end

end CoefficientNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_ConstantCoefficient
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.leftAdditive _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.ChainTensor.rightAdditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology MonoidalCategory
namespace CoefficientNerve
open FreeChains

variable {C:Type} [Category.{0} C]
noncomputable def constant (M:A) : C ⥤ A := (Functor.const C).obj M
noncomputable def constIso (M:A) (n:ℕ) :
    Obj (constant (C:=C) M) n ≅ ((ModuleCat.free ℤ).obj (Simplex C n)) ⊗ M := by
  classical
  exact ((finsuppLEquivDirectSum ℤ M (Simplex C n)).symm ≪≫ₗ
    (TensorProduct.finsuppScalarLeft ℤ M (Simplex C n)).symm).toModuleIso
lemma constIso_single (M:A) {n:ℕ} (s:Simplex C n) (m:M) :
    (constIso M n).hom (single (constant M) s m) = (ModuleCat.freeMk (R:=ℤ) s) ⊗ₜ[ℤ] m := by
  classical
  change (TensorProduct.finsuppScalarLeft ℤ M (Simplex C n)).symm
    ((finsuppLEquivDirectSum ℤ M (Simplex C n)).symm (DirectSum.lof ℤ _ _ s m)) = _
  simp only [finsuppLEquivDirectSum_symm_lof,TensorProduct.finsuppScalarLeft_symm_apply_single]
  rfl
noncomputable def constantSimplicialIso (M:A) :
    simplicial (constant (C:=C) M) ≅ nerve Cᵒᵖ ⋙ ModuleCat.free ℤ ⋙ tensorRight M :=
  NatIso.ofComponents (fun p=>constIso M p.unop.len) (by
    intro p q f
    apply hom_ext; intro s
    change single (constant M) s ≫ map (constant M) f.unop ≫ _ = _
    erw [single_map_assoc]
    change (𝟙 M) ≫ single (constant M) (trunc f.unop s) ≫ _ = _
    rw [Category.id_comp]
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro m
    change (constIso M _).hom (single (constant M) (trunc f.unop s) m) =
      ((tensorRight M).map ((ModuleCat.free ℤ).map ((nerve Cᵒᵖ).map f)))
        ((constIso M _).hom (single (constant M) s m))
    rw [constIso_single,constIso_single]
    change _ = ((ModuleCat.free ℤ).map ((nerve Cᵒᵖ).map f) (ModuleCat.freeMk s)) ⊗ₜ[ℤ] m
    erw [ModuleCat.free_map_apply]
    rfl)
noncomputable def constantComplexIso (M:A) :
    complex (constant (C:=C) M) ≅ (TensorCoefficient.functor (FreeChains.complex (nerve Cᵒᵖ))).obj M :=
  (alternatingFaceMapComplex A).mapIso (constantSimplicialIso M) ≪≫
    (eqToIso (congrArg (fun T => T.obj (nerve Cᵒᵖ ⋙ ModuleCat.free ℤ))
      (map_alternatingFaceMapComplex (tensorRight M)))).symm
end CoefficientNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularCoefficientDouble
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularCoefficient
open CoefficientNerve FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
noncomputable def coeffComplex : ChainComplex (SingleObj P ⥤ A) ℕ :=
  ExactShapeHomology.complex (representation F ⋙ alternatingFaceMapComplex A)
noncomputable def double : HomologicalComplex₂ A c c := CoefficientNerve.double (coeffComplex F)
end RegularCoefficient

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularBlock
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularCoefficient
open CoefficientNerve FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
noncomputable def block {h v:ℕ} (s:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v) :
    F.obj t.right.unop ⟶ ((double F).X h).X v :=
  single F t ≫ single ((coeffComplex F).X v) s
lemma block_hom_ext {h v:ℕ} {M:A} {f g:((double F).X h).X v ⟶ M}
    (hh:∀s t,block F s t ≫ f=block F s t ≫ g) : f=g := by
  apply CoefficientNerve.hom_ext
  intro s
  apply CoefficientNerve.hom_ext
  intro t
  exact (Category.assoc _ _ _).symm.trans ((hh s t).trans (Category.assoc _ _ _))
noncomputable def blockDesc {h v:ℕ} {M:A}
    (f:∀(_:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v),F.obj t.right.unop ⟶ M) :
    ((double F).X h).X v ⟶ M :=
  CoefficientNerve.desc ((coeffComplex F).X v) (fun s=>CoefficientNerve.desc F (f s))
@[reassoc (attr:=simp)] lemma block_desc {h v:ℕ} {M:A}
    (f:∀(_:Simplex (SingleObj P) h) (t:Simplex (ActionCategory P P) v),F.obj t.right.unop ⟶ M) (s) (t) :
    block F s t ≫ blockDesc F f=f s t := by
  dsimp only [block,blockDesc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => CoefficientNerve.single F t ≫ g)
      (CoefficientNerve.single_desc ((coeffComplex F).X v)
        (fun s => CoefficientNerve.desc F (f s)) s)).trans
      (CoefficientNerve.single_desc F (f s) t))
end RegularCoefficient

namespace RegularLabels
open FreeChains CoefficientNerve RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
abbrev fiber (p:P) : A := F.obj (ActionCategory.objEquiv P P p)
noncomputable def inj {h v:ℕ} (w:W (P:=P) h v) :
    fiber F w.2.1 ⟶ ((RegularCoefficient.double F).X h).X v :=
  eqToHom (congrArg F.obj (rightEq w.2.1 w.1).symm) ≫
    RegularCoefficient.block F (ofLabels w.2.2) (lift w.2.1 (ofLabels w.1))
noncomputable def desc {h v:ℕ} {M:A} (f:∀w:W (P:=P) h v,fiber F w.2.1 ⟶ M) :
    ((RegularCoefficient.double F).X h).X v ⟶ M :=
  RegularCoefficient.blockDesc F (fun s t=> f (labels (t ⋙ (ActionCategory.π P P).op),t.right.unop.back,labels s))
@[reassoc (attr:=simp)] lemma include_desc {h v:ℕ} {M:A}
    (f:∀w:W (P:=P) h v,fiber F w.2.1 ⟶ M) (w:W (P:=P) h v) :
    inj F w ≫ desc F f=f w := by
  dsimp only [inj,desc]
  erw [Category.assoc,RegularCoefficient.block_desc]
  have hr:=lift_right w.2.1 (ofLabels w.1)
  change eqToHom (congrArg (fiber F) hr.symm) ≫
    f (labels (lift w.2.1 (ofLabels w.1) ⋙ (ActionCategory.π P P).op),
      (lift w.2.1 (ofLabels w.1)).right.unop.back,labels (ofLabels w.2.2)) = f w
  rw [lift_project,labels_ofLabels,labels_ofLabels]
  generalize (lift w.2.1 (ofLabels w.1)).right.unop.back = p at *
  cases hr
  simp
lemma hom_ext {h v:ℕ} {M:A} {f g:((RegularCoefficient.double F).X h).X v ⟶ M}
    (hh:∀w:W (P:=P) h v,inj F w ≫ f=inj F w ≫ g) : f=g := by
  apply RegularCoefficient.block_hom_ext
  intro s t
  obtain ⟨x,rfl⟩ := (MonoidNerveCoordinates.equiv P h).symm.surjective s
  obtain ⟨⟨p,y⟩,rfl⟩ := (RegularCoordinates.coordinates v).symm.surjective t
  obtain ⟨z,rfl⟩ := (MonoidNerveCoordinates.equiv P v).symm.surjective y
  change RegularCoefficient.block F (ofLabels x) (lift p (ofLabels z)) ≫ f =
    RegularCoefficient.block F (ofLabels x) (lift p (ofLabels z)) ≫ g
  exact (cancel_epi (eqToHom (congrArg F.obj (rightEq p z).symm))).mp
    (by simpa only [inj,Category.assoc] using hh (z,p,x))
end RegularLabels

end

namespace MarkedCoordinates
variable {P:Type} {n:ℕ}
lemma word_right (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) (j:Fin (n-i.val)) :
    word i y p x ⟨n-j.val,by omega⟩=x j := by
  simp only [word,dite_eq_right (show ¬n-j.val < i.val from by omega),dite_eq_right (show ¬n-j.val = i.val from by omega)]
  congr 1
  apply Fin.ext
  dsimp
  omega
lemma horizontal_word (i:Fin (n+1)) (y:Fin i.val→P) (p:P) (x:Fin (n-i.val)→P) :
    horizontal (word i y p x) i=x := by funext j; exact word_right i y p x j
noncomputable def equiv (P:Type) (n:ℕ) : Split P n ≃ (Σ_:Fin (n+1),(Fin (n+1)→P)) where
  toFun s := ⟨s.1,word s.1 s.2.1 s.2.2.1 s.2.2.2⟩
  invFun s := ⟨s.1,vertical s.2 s.1,s.2 s.1,horizontal s.2 s.1⟩
  left_inv := by rintro ⟨i,y,p,x⟩; simp only [vertical_word,word_center,horizontal_word]
  right_inv := by rintro ⟨i,w⟩; simp only [word_recover]
end MarkedCoordinates

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalBinary
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.mapEssSurj _root_.OAI.IntervalBar.Diagram.mapFaithful _root_.OAI.IntervalBar.Diagram.mapFull _root_.OAI.IntervalBar.Diagram.mapIsEquivalence _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_nerve_connected _root_.OAI.IntervalBar.Diagram.zero_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def oneEval : Diagram C (Fin 2) ⥤ C := eval 1 ⋙ Pi.eval (fun _:Fin 1=>C) 0
lemma binary_zero : reindex (C:=C) (SimplexCategory.δ (0:Fin 3)).toOrderHom ⋙ oneEval =
    eval 2 ⋙ Pi.eval (fun _:Fin 2=>C) 1 := rfl
lemma binary_last : reindex (C:=C) (SimplexCategory.δ (2:Fin 3)).toOrderHom ⋙ oneEval =
    eval 2 ⋙ Pi.eval (fun _:Fin 2=>C) 0 := rfl
noncomputable def binaryFace (i:Fin 3) : (Fin 2→C) ⥤ C :=
  (eval 2).asEquivalence.inverse ⋙ reindex (SimplexCategory.δ i).toOrderHom ⋙ oneEval
noncomputable def binaryFaceZero : binaryFace (C:=C) 0 ≅ Pi.eval (fun _:Fin 2=>C) 1 :=
  Functor.isoWhiskerLeft (eval 2).asEquivalence.inverse (eqToIso binary_zero) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eval 2).asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _
noncomputable def binaryFaceLast : binaryFace (C:=C) 2 ≅ Pi.eval (fun _:Fin 2=>C) 0 :=
  Functor.isoWhiskerLeft (eval 2).asEquivalence.inverse (eqToIso binary_last) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eval 2).asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_DoubleCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace DoubleCoordinates
variable {P:Type} {n:ℕ}
noncomputable def words (P:Type) (n:ℕ) : Index P n ≃ (Σ_:Fin (n+1),Fin (n+1)→P) :=
  (equiv P n).trans (MarkedCoordinates.equiv P n)
lemma center (s:Index P n) : (words P n s).2 (words P n s).1=s.2.2.1 :=
  MarkedCoordinates.word_center _ _ _ _
end DoubleCoordinates

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
noncomputable def totalInj {n:ℕ} (s:DoubleCoordinates.Index P n) :
    fiber F s.2.2.1 ⟶ ((RegularCoefficient.double F).total c).X n :=
  inj F s.2 ≫ (RegularCoefficient.double F).ιTotal c s.1.val.1 s.1.val.2 n s.1.property
noncomputable def totalDesc {n:ℕ} {M:A}
    (f:∀s:DoubleCoordinates.Index P n,fiber F s.2.2.1 ⟶ M) :
    ((RegularCoefficient.double F).total c).X n ⟶ M :=
  (RegularCoefficient.double F).totalDesc (fun h v hn=>desc F (fun w=>f ⟨⟨(h,v),hn⟩,w⟩))
@[reassoc (attr:=simp)] lemma totalInj_desc {n:ℕ} {M:A}
    (f:∀s:DoubleCoordinates.Index P n,fiber F s.2.2.1 ⟶ M) (s:DoubleCoordinates.Index P n) :
    totalInj F s ≫ totalDesc F f=f s := by
  dsimp only [totalInj,totalDesc]
  rw [Category.assoc,HomologicalComplex₂.ι_totalDesc,include_desc]
lemma total_hom_ext {n:ℕ} {M:A} {f g:((RegularCoefficient.double F).total c).X n ⟶ M}
    (hh:∀s:DoubleCoordinates.Index P n,totalInj F s ≫ f=totalInj F s ≫ g) : f=g := by
  apply HomologicalComplex₂.total.hom_ext
  intro h v hn
  apply hom_ext F
  intro w
  exact (Category.assoc _ _ _).symm.trans ((hh ⟨⟨(h,v),hn⟩,w⟩).trans (Category.assoc _ _ _))
noncomputable def totalIsColimit (n:ℕ) : IsColimit (Cofan.mk _ (totalInj F (n:=n))) :=
  Cofan.IsColimit.mk _ (fun s=>totalDesc F s.inj) (fun _ _=>totalInj_desc F _ _)
    (fun s _ hh=>total_hom_ext F (fun w=>(hh w).trans (totalInj_desc F s.inj w).symm))
end RegularLabels

end

namespace MarkedH1

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def wordInclude {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) : Fiber (p i) ⥤ (Fin n→C) := by
  classical
  exact Functor.pi' (fun j=>if i=j then (property (p i)).ι else (Functor.const _).obj (repr (p j)))
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma wordInclude_nerve {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    nerveMap (wordInclude p i) ≫ (PiSSet.nervePiIso (fun _:Fin n=>C)).hom =
      PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i ≫ PiFiber.inclusion C (Fin n) p := by
  classical
  apply NatTrans.ext; funext d
  apply ConcreteCategory.hom_ext; intro s
  funext j
  change (s ⋙ wordInclude p i ⋙ Pi.eval _ j) =
    ((PiSSet.incl (fun j=>nerve (Fiber (p j))) (points p) i ≫ PiSSet.proj _ j ≫
      nerveMap (property (p j)).ι).app d s)
  dsimp only [wordInclude]
  rw [Functor.pi'_eval]
  by_cases h:i=j
  · subst j
    rw [ite_eq_left rfl, ←Category.assoc, PiSSet.incl_self]
    rfl
  · rw [ite_eq_right h, ←Category.assoc, PiSSet.incl_other _ _ h, SSet.const_comp]
    rfl
noncomputable def wordDiagram {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    Fiber (p i) ⥤ IntervalBar.Diagram C (Fin (n+1)) :=
  wordInclude p i ⋙ (IntervalBar.Diagram.eval (C:=C) n).asEquivalence.inverse
omit [SymmetricCategory C] in
lemma primitive_eq {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    primitive p i=SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 := by
  have:=NerveHomotopy.homologyMap_isIso ((IntervalBar.Diagram.eval (C:=C) n).asEquivalence.functor) Z 1
  apply (cancel_mono (evalIso (C:=C) n).hom).mp
  dsimp only [primitive]
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [←SSet.homologyMap_comp,←wordInclude_nerve]
  erw [SSet.homologyMap_comp]
  dsimp only [wordDiagram,evalIso,Iso.trans_hom,Functor.mapIso_hom,asIso_hom]
  have h:=(NerveHomotopy.ofNatTrans
    (Functor.isoWhiskerLeft (wordInclude p i) (IntervalBar.Diagram.eval (C:=C) n).asEquivalence.counitIso).hom).congr_homologyMap Z 1
  have hh : SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 ≫
      SSet.homologyMap (nerveMap (IntervalBar.Diagram.eval (C:=C) n)) Z 1 =
        SSet.homologyMap (nerveMap (wordInclude p i)) Z 1 := by
    rw [←SSet.homologyMap_comp]
    exact h
  change SSet.homologyMap (nerveMap (wordInclude p i)) Z 1 ≫ _ =
    SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 ≫
      SSet.homologyMap (nerveMap (IntervalBar.Diagram.eval (C:=C) n)) Z 1 ≫ _
  rw [←Category.assoc,hh]
  rfl
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma wordInclude_proj {n:ℕ} (p:Fin n→Skeleton C) (i j:Fin n) :
    wordInclude p i ⋙ Pi.eval (fun _:Fin n=>C) j =
      if i=j then (property (p i)).ι else (Functor.const _).obj (repr (p j)) := by
  classical
  exact Functor.pi'_eval _ _
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_face (p:Fin 2→Skeleton C) (i:Fin 2) (k:Fin 3) :
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 =
        SSet.homologyMap (nerveMap (wordInclude p i ⋙ binaryFace k)) Z 1 := by
  rw [primitive_eq]
  change SSet.homologyMap (nerveMap (wordDiagram p i)) Z 1 ≫
    SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 =
    SSet.homologyMap (nerveMap (wordDiagram p i) ≫
      nerveMap (reindex (SimplexCategory.δ k).toOrderHom) ≫ nerveMap oneEval) Z 1
  simp only [SSet.homologyMap_comp]
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_zero (p:Fin 2→Skeleton C) :
    primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=ComponentStable.inclusion (p 1) 1 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z 1
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_last (p:Fin 2→Skeleton C) :
    primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=ComponentStable.inclusion (p 0) 1 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z 1
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_zero_other (p:Fin 2→Skeleton C) :
    primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=0 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z 1
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 0))).obj (repr (p 1))) =
      SSet.const (nerveEquiv.symm (repr (p 1))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ 1 (by decide)
omit [SymmetricCategory C] in
@[reassoc] lemma binary_primitive_last_other (p:Fin 2→Skeleton C) :
    primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1=0 := by
  rw [binary_primitive_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z 1
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 1))).obj (repr (p 0))) =
      SSet.const (nerveEquiv.symm (repr (p 0))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ 1 (by decide)
end

end MarkedH1

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularLiftFaces
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite
namespace RegularCoordinates
open CoefficientNerve MonoidNerveCoordinates

variable {P:Type} [CommMonoid P]
lemma trunc_lift {m n:ℕ} (f:⦋m⦌⟶⦋n⦌) (p:P) (s:B (P:=P) n) :
    trunc f (lift p s)=lift (tail f s * p) (trunc f s) := by
  apply (coordinates m).injective
  apply Prod.ext
  · change (trunc f (lift p s)).right.unop.back=(lift _ _).right.unop.back
    rw [lift_right]
    rfl
  · change trunc f (lift p s) ⋙ (ActionCategory.π P P).op=lift _ _ ⋙ (ActionCategory.π P P).op
    rw [lift_project]
    change (SimplexCategory.toCat.map f).toFunctor ⋙ (lift p s ⋙ (ActionCategory.π P P).op)=_
    erw [lift_project]
    rfl
end RegularCoordinates
namespace RegularLabels
open CoefficientNerve RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ FreeChains.A)
noncomputable def singleLabel {n:ℕ} (p:P) (y:Fin n→P) : fiber F p ⟶ Obj F n :=
  eqToHom (congrArg F.obj (rightEq p y).symm) ≫ single F (lift p (ofLabels y))
lemma singleLabel_map_general {m n:ℕ} (f:⦋m⦌⟶⦋n⦌) (p:P) (y:Fin n→P) :
    singleLabel F p y ≫ map F f =
      F.map (arrow (tail f (ofLabels y)) p) ≫
        singleLabel F (tail f (ofLabels y)*p) (labels (trunc f (ofLabels y))) := by
  dsimp only [singleLabel]
  rw [←eqToHom_map F (rightEq p y).symm,
    ←eqToHom_map F (rightEq (tail f (ofLabels y)*p) (labels (trunc f (ofLabels y)))).symm]
  simp only [Category.assoc,single_map,←F.map_comp_assoc]
  apply weighted_eq F (by rw [trunc_lift,ofLabels_labels])
  apply Subtype.ext
  repeat (first | erw [CategoryOfElements.comp_val] | erw [RegularTranslation.eqToHom_val])
  repeat (first | erw [SingleObj.comp_as_mul] | erw [one_mul] | erw [mul_one])
  rfl
@[reassoc] lemma singleLabel_face {n:ℕ} (k:Fin (n+2)) (p:P) (y:Fin (n+1)→P) :
    singleLabel F p y ≫ (simplicial F).δ k =
      F.map (arrow (faceWeight k y) p) ≫
        singleLabel F (faceWeight k y*p) (faceLabels k y) := by
  change singleLabel F p y ≫ map F (SimplexCategory.δ k)=_
  rw [singleLabel_map_general,tail_face]
  congr 2
  exact (labels_face (ofLabels y) k).trans (congrArg (faceLabels k) (labels_ofLabels y))
@[reassoc] lemma singleLabel_action (a p:P) {n:ℕ} (y:Fin n→P) :
    singleLabel F p y ≫ (RegularCoefficient.action F a).app (op ⦋n⦌) =
      F.map (arrow a p) ≫ singleLabel F (a*p) y := by
  dsimp only [singleLabel]
  rw [←eqToHom_map F (rightEq p y).symm,←eqToHom_map F (rightEq (a*p) y).symm]
  erw [Category.assoc,RegularCoefficient.single_action]
  erw [←F.map_comp_assoc,←F.map_comp_assoc]
  apply weighted_eq F (shift_lift a p (ofLabels y))
  apply Subtype.ext
  repeat (first | erw [CategoryOfElements.comp_val] | erw [RegularTranslation.eqToHom_val])
  repeat (first | erw [SingleObj.comp_as_mul] | erw [one_mul] | erw [mul_one])
  rfl
end RegularLabels

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RegularBlockFaces
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial SimplicialObject Opposite HomologicalComplex AlgebraicTopology
namespace MonoidNerveCoordinates
open CoefficientNerve

variable {P:Type} [CommMonoid P]
lemma trunc_ofLabels {n:ℕ} (k:Fin (n+2)) (x:Fin (n+1)→P) :
    trunc (SimplexCategory.δ k) (ofLabels x)=ofLabels (faceLabels k x) := by
  rw [←ofLabels_labels (trunc (SimplexCategory.δ k) (ofLabels x))]
  congr 1
  exact (labels_face (ofLabels x) k).trans (congrArg (faceLabels k) (labels_ofLabels x))
end MonoidNerveCoordinates
namespace RegularLabels
open CoefficientNerve RegularCoordinates MonoidNerveCoordinates FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
@[reassoc] lemma inj_horizontalFace {h v:ℕ} (k:Fin (h+2)) (y:Fin v→P) (p:P) (x:Fin (h+1)→P) :
    inj F (y,p,x) ≫ ((chainSimplicial (RegularCoefficient.coeffComplex F)).δ k).f v =
      F.map (arrow (faceWeight k x) p) ≫ inj F (y,faceWeight k x*p,faceLabels k x) := by
  change singleLabel F p y ≫ single ((RegularCoefficient.coeffComplex F).X v) (ofLabels x) ≫
      map ((RegularCoefficient.coeffComplex F).X v) (SimplexCategory.δ k) = _
  erw [single_map,tail_face,trunc_ofLabels]
  change singleLabel F p y ≫ (RegularCoefficient.action F (faceWeight k x)).app (op ⦋v⦌) ≫
      single ((RegularCoefficient.coeffComplex F).X v) (ofLabels (faceLabels k x)) = _
  erw [←Category.assoc,singleLabel_action,Category.assoc]
@[reassoc] lemma inj_dV {h v:ℕ} (y:Fin (v+1)→P) (p:P) (x:Fin h→P) :
    inj F (y,p,x) ≫ ((RegularCoefficient.double F).X h).d (v+1) v =
      ∑k:Fin (v+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k y) p) ≫
        inj F (faceLabels k y,faceWeight k y*p,x)) := by
  change singleLabel F p y ≫ single ((RegularCoefficient.coeffComplex F).X (v+1)) (ofLabels x) ≫
    (mapNat ((RegularCoefficient.coeffComplex F).d (v+1) v)).app (op ⦋h⦌) = _
  erw [single_mapNat]
  change singleLabel F p y ≫ (complex F).d (v+1) v ≫
    single ((RegularCoefficient.coeffComplex F).X v) (ofLabels x) = _
  have hd : (complex F).d (v+1) v = ∑k:Fin (v+2),(-1:ℤ)^k.val • (simplicial F).δ k :=
    AlternatingFaceMapComplex.obj_d_eq (simplicial F) v
  rw [hd]
  erw [Preadditive.sum_comp,Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro index _
  erw [Preadditive.zsmul_comp,Preadditive.comp_zsmul,←Category.assoc,singleLabel_face,Category.assoc]
  rfl
@[reassoc] lemma inj_dH {h v:ℕ} (y:Fin v→P) (p:P) (x:Fin (h+1)→P) :
    inj F (y,p,x) ≫ ((RegularCoefficient.double F).d (h+1) h).f v =
      ∑k:Fin (h+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k x) p) ≫
        inj F (y,faceWeight k x*p,faceLabels k x)) := by
  change inj F (y,p,x) ≫ ((AlternatingFaceMapComplex.obj
    (chainSimplicial (RegularCoefficient.coeffComplex F))).d (h+1) h).f v = _
  rw [AlternatingFaceMapComplex.obj_d_eq]
  change inj F (y,p,x) ≫ (HomologicalComplex.Hom.fAddMonoidHom v)
    (∑i:Fin (h+2),(-1:ℤ)^i.val • (chainSimplicial (RegularCoefficient.coeffComplex F)).δ i) = _
  erw [map_sum,Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro index _
  erw [map_zsmul,Preadditive.comp_zsmul,inj_horizontalFace]
  rfl
end RegularLabels

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularTotalDifferential
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
@[reassoc] lemma totalInj_d_parts {n:ℕ} (s:DoubleCoordinates.Index P (n+1)) :
    totalInj F s ≫ ((RegularCoefficient.double F).total c).d (n+1) n =
      inj F s.2 ≫ (RegularCoefficient.double F).d₁ c s.1.val.1 s.1.val.2 n +
      inj F s.2 ≫ (RegularCoefficient.double F).d₂ c s.1.val.1 s.1.val.2 n := by
  dsimp only [totalInj]
  rw [Category.assoc,HomologicalComplex₂.total_d,Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁,HomologicalComplex₂.ι_D₂,Preadditive.comp_add]
@[reassoc] lemma totalInj_d_hor (h:ℕ) (y:Fin 0→P) (p:P) (x:Fin (h+1)→P) :
    totalInj F ⟨⟨(h+1,0),rfl⟩,y,p,x⟩ ≫ ((RegularCoefficient.double F).total c).d (h+1) h =
      ∑k:Fin (h+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k x) p) ≫
        totalInj F ⟨⟨(h,0),rfl⟩,y,faceWeight k x*p,faceLabels k x⟩) := by
  rw [totalInj_d_parts]
  rw [HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp)]
  rw [HomologicalComplex₂.d₁_eq _ _ (show c.Rel (h+1) h from rfl) 0 h rfl]
  simp only [comp_zero,add_zero,show c.ε₁ c c (h+1,0) = 1 from rfl,one_smul]
  change inj F (y,p,x) ≫ ((RegularCoefficient.double F).d (h+1) h).f 0 ≫
    (RegularCoefficient.double F).ιTotal c h 0 h rfl = _
  rw [inj_dH_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc,totalInj]
  rfl
@[reassoc] lemma totalInj_d_ver (v:ℕ) (y:Fin (v+1)→P) (p:P) (x:Fin 0→P) :
    totalInj F ⟨⟨(0,v+1),by omega⟩,y,p,x⟩ ≫ ((RegularCoefficient.double F).total c).d (v+1) v =
      ∑k:Fin (v+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k y) p) ≫
        totalInj F ⟨⟨(0,v),by omega⟩,faceLabels k y,faceWeight k y*p,x⟩) := by
  rw [totalInj_d_parts]
  rw [HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp)]
  rw [HomologicalComplex₂.d₂_eq _ _ 0 (show c.Rel (v+1) v from rfl) v (by change 0+v=v; omega)]
  simp only [comp_zero,zero_add,show c.ε₂ c c (0,v+1) = 1 from rfl,one_smul]
  change inj F (y,p,x) ≫ ((RegularCoefficient.double F).X 0).d (v+1) v ≫
    (RegularCoefficient.double F).ιTotal c 0 v v (by change 0+v=v; omega) = _
  rw [inj_dV_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc,totalInj]
@[reassoc] lemma totalInj_d_both (h v:ℕ) (y:Fin (v+1)→P) (p:P) (x:Fin (h+1)→P) :
    totalInj F ⟨⟨(h+1,v+1),by omega⟩,y,p,x⟩ ≫
      ((RegularCoefficient.double F).total c).d (h+v+2) (h+v+1) =
      (∑k:Fin (h+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k x) p) ≫
        totalInj F ⟨⟨(h,v+1),by omega⟩,y,faceWeight k x*p,faceLabels k x⟩)) +
      (-1:ℤ)^(h+1) • (∑k:Fin (v+2),(-1:ℤ)^k.val • (F.map (arrow (faceWeight k y) p) ≫
        totalInj F ⟨⟨(h+1,v),by omega⟩,faceLabels k y,faceWeight k y*p,x⟩)) := by
  rw [totalInj_d_parts]
  rw [HomologicalComplex₂.d₁_eq _ _ (show c.Rel (h+1) h from rfl) (v+1) (h+v+1) (by change h+(v+1)=h+v+1; omega)]
  rw [HomologicalComplex₂.d₂_eq _ _ (h+1) (show c.Rel (v+1) v from rfl) (h+v+1) (by change (h+1)+v=h+v+1; omega)]
  simp only [show c.ε₁ c c (h+1,v+1) = 1 from rfl,one_smul]
  change inj F (y,p,x) ≫ ((RegularCoefficient.double F).d (h+1) h).f (v+1) ≫
      (RegularCoefficient.double F).ιTotal c h (v+1) (h+v+1) (by change h+(v+1)=h+v+1; omega) +
    inj F (y,p,x) ≫ ((ComplexShape.ε₂ c c c (h+1,v+1)) •
      (((RegularCoefficient.double F).X (h+1)).d (v+1) v ≫
        (RegularCoefficient.double F).ιTotal c (h+1) v (h+v+1) (by change (h+1)+v=h+v+1; omega))) = _
  rw [Units.smul_def]
  change _ + inj F (y,p,x) ≫ ((-1:ℤ)^(h+1) • _) = _
  rw [Preadditive.comp_zsmul,inj_dH_assoc,inj_dV_assoc]
  simp only [Preadditive.sum_comp,Preadditive.zsmul_comp,Category.assoc,totalInj]
end RegularLabels

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains RegularCoordinates MonoidNerveCoordinates

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
lemma totalInj_transport {h v n:ℕ} (hn:h+v=n) (y:Fin v→P) (x:Fin h→P) {p q:P} (e:p=q) :
    eqToHom (congrArg (fiber F) e) ≫ totalInj F ⟨⟨(h,v),hn⟩,y,q,x⟩ =
      totalInj F ⟨⟨(h,v),hn⟩,y,p,x⟩ := by
  subst q
  simp
@[reassoc] lemma one_totalInj {h v n:ℕ} (hn:h+v=n) (y:Fin v→P) (p:P) (x:Fin h→P) :
    F.map (arrow 1 p) ≫ totalInj F ⟨⟨(h,v),hn⟩,y,1*p,x⟩ =
      totalInj F ⟨⟨(h,v),hn⟩,y,p,x⟩ := by
  rw [arrow_one,eqToHom_map]
  exact totalInj_transport F hn y x (one_mul p).symm
end RegularLabels
namespace RegularFiniteFaces
open RegularLabels RegularCoordinates MonoidNerveCoordinates
variable {P:Type} [CommMonoid P]
@[simp] lemma labels1_0 (a:P) : faceLabels (0:Fin 2) ![a]=![] := by
  funext j
  fin_cases j
@[simp] lemma weight1_0 (a:P) : faceWeight (0:Fin 2) ![a]=1 := by
  simp [faceWeight]
@[simp] lemma labels1_1 (a:P) : faceLabels (1:Fin 2) ![a]=![] := by
  funext j
  fin_cases j
@[simp] lemma weight1_1 (a:P) : faceWeight (1:Fin 2) ![a]=a := by
  simp [faceWeight]
@[simp] lemma labels2_0 (a b:P) : faceLabels (0:Fin 3) ![a,b]=![b] := by
  funext j
  fin_cases j
  rfl
@[simp] lemma weight2_0 (a b:P) : faceWeight (0:Fin 3) ![a,b]=1 := by
  simp [faceWeight]
@[simp] lemma labels2_1 (a b:P) : faceLabels (1:Fin 3) ![a,b]=![(a*b)] := by
  funext j
  fin_cases j
  rfl
@[simp] lemma weight2_1 (a b:P) : faceWeight (1:Fin 3) ![a,b]=1 := by
  simp [faceWeight]
@[simp] lemma labels2_2 (a b:P) : faceLabels (2:Fin 3) ![a,b]=![a] := by
  funext j
  fin_cases j
  rfl
@[simp] lemma weight2_2 (a b:P) : faceWeight (2:Fin 3) ![a,b]=b := by
  simp [faceWeight]
@[simp] lemma labels3_0 (a b d:P) : faceLabels (0:Fin 4) ![a,b,d]=![b,d] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_0 (a b d:P) : faceWeight (0:Fin 4) ![a,b,d]=1 := by
  simp [faceWeight]
@[simp] lemma labels3_1 (a b d:P) : faceLabels (1:Fin 4) ![a,b,d]=![(a*b),d] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_1 (a b d:P) : faceWeight (1:Fin 4) ![a,b,d]=1 := by
  simp [faceWeight]
@[simp] lemma labels3_2 (a b d:P) : faceLabels (2:Fin 4) ![a,b,d]=![a,(b*d)] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_2 (a b d:P) : faceWeight (2:Fin 4) ![a,b,d]=1 := by
  simp [faceWeight]
@[simp] lemma labels3_3 (a b d:P) : faceLabels (3:Fin 4) ![a,b,d]=![a,b] := by
  funext j
  fin_cases j <;> rfl
@[simp] lemma weight3_3 (a b d:P) : faceWeight (3:Fin 4) ![a,b,d]=d := by
  simp [faceWeight]
end RegularFiniteFaces

end

section

namespace FilteredEdge
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
namespace Data
variable (K : Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
def current : FilteredFiniteness.Data (R:=R) (A:=A) (B:=B) (C:=C) :=
  ⟨K.d,K.e,K.ed,K.FA,K.FB,K.FC,K.monoB⟩
def previous : FilteredFiniteness.Data (R:=R) (A:=D) (B:=A) (C:=B) :=
  ⟨K.s,K.d,K.ds,K.FD,K.FA,K.FB,K.monoA⟩
variable (p : ℤ)
def boundaryCycle (k : ℤ) : K.inputs p k →ₗ[R] K.current.Z₂ p :=
  (K.d.comp (K.inputs p k).subtype).codRestrict _ (fun x => by
    refine ⟨x.property.2,?_⟩
    change K.e (K.d x.val) ∈ K.FC (p-2)
    have he : K.e (K.d x.val)=0 := congrArg (fun f : A →ₗ[R] C => f x.val) K.ed
    rw [he]; exact Submodule.zero_mem _)
def boundaryMap (k : ℤ) : K.inputs p k →ₗ[R] K.current.E₂ p :=
  ((K.current.B₂ p).comap (K.current.Z₂ p).subtype).mkQ.comp (K.boundaryCycle p k)
def tower (k : ℤ) : Submodule R (K.current.E₂ p) := LinearMap.range (K.boundaryMap p k)
def inputLeading (k : ℤ) (hk : p≤k-2) : K.inputs p k →ₗ[R] K.previous.E₂ k :=
  ((K.previous.B₂ k).comap (K.previous.Z₂ k).subtype).mkQ.comp
    (((K.inputs p k).subtype).codRestrict _ (fun x =>
      ⟨x.property.1,K.monoB hk x.property.2⟩))
end Data
end FilteredEdge

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FilteredEdgeReturn
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace FilteredEdge.Data
open FilteredFiniteness

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {D A B C : Type u} [AddCommGroup D] [Module R D]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
variable (K : FilteredEdge.Data (R:=R) (D:=D) (A:=A) (B:=B) (C:=C))
variable (p : ℤ) (hp : K.FC (p-2)=⊥)
def edgeCycles : K.current.Z₂ p →ₗ[R] LinearMap.ker K.current.e :=
  (K.current.Z₂ p).subtype.codRestrict _ (fun x => by
    have hx := x.property.2
    change K.e x.val∈K.FC (p-2) at hx
    rw [hp] at hx
    exact hx)
def edgeLift : K.current.Z₂ p →ₗ[R] K.current.H ⧸ K.current.filtration (p-1) :=
  (K.current.filtration (p-1)).mkQ.comp (K.current.π.comp (K.edgeCycles p hp))
omit [IsNoetherianRing R] in
lemma boundary_in_edge_kernel :
    (K.current.B₂ p).comap (K.current.Z₂ p).subtype ≤ LinearMap.ker (K.edgeLift p hp) := by
  intro x hx
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a,ha,haz⟩ := hz.1
  change y+z=x.val at hyz
  change K.d a=z at haz
  have hez : K.e z=0 := by
    rw [←haz]; exact congrArg (fun f : A →ₗ[R] C => f a) K.ed
  have hex : K.e x.val=0 := (K.edgeCycles p hp x).property
  have hey : K.e y=0 := by
    rw [←hyz,map_add,hez,add_zero] at hex
    exact hex
  change K.edgeLift p hp x=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨⟨⟨y,hey⟩,hy.1⟩,?_⟩
  change K.current.π ⟨y,hey⟩=K.current.π (K.edgeCycles p hp x)
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨-a,?_⟩
  apply Subtype.ext
  change K.d (-a)=y-x.val
  rw [map_neg,haz,←hyz]
  abel
def edgeMap : K.current.E₂ p →ₗ[R] K.current.H ⧸ K.current.filtration (p-1) :=
  ((K.current.B₂ p).comap (K.current.Z₂ p).subtype).liftQ
    (K.edgeLift p hp) (K.boundary_in_edge_kernel p hp)
end FilteredEdge.Data

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Descend
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace E2Leading
open TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
lemma boundary_top_cycle (p q : ℕ) (w : (K.total c).X (p+q+1))
    (hw : w∈filtration K (p+q+1) (p+2))
    (hdw : (K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) (p+1)) :
    (K.X (p+1)).d q (q-1) (projection K (p+1) q (p+q+1) w)=0 := by
  cases q with
  | zero => rw [(K.X (p+1)).shape 0 (0-1) (by decide)]; rfl
  | succ q =>
    rw [Nat.add_sub_cancel]
    have hd := d_entry' K (p+1) q (p+(q+1)+1) (p+(q+1)) (by omega) (by omega) w
    have hz : projection K (p+1) q (p+(q+1)) ((K.total c).d (p+(q+1)+1) (p+(q+1)) w)=0 :=
      entry_zero K hdw (by omega)
    have hf : projection K (p+1+1) q (p+(q+1)+1) w=0 := entry_zero K hw (by omega)
    rw [hz,hf,map_zero,zero_add] at hd
    have hh := congrArg (fun z => (((-1 : ℤˣ)^(p+1))⁻¹) • z) hd.symm
    rw [inv_smul_smul,smul_zero] at hh
    exact hh
lemma boundary_lead_zero (p q : ℕ) (w : (K.total c).X (p+q+1))
    (hw : w∈filtration K (p+q+1) (p+2))
    (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1))
    (hx : x.val=(K.total c).d (p+q+1) (p+q) w) : lead K p q x=0 := by
  have hdw : (K.total c).d (p+q+1) (p+q) w∈filtration K (p+q) (p+1) := hx ▸ x.property.1
  let y : ConcreteHomology.Cycles (K.X (p+1)) q :=
    ⟨projection K (p+1) q (p+q+1) w,boundary_top_cycle K p q w hw hdw⟩
  apply (ConcreteHomology.π_eq_zero (row K q) p (topRowCycle K p q x)).mpr
  refine ⟨ConcreteHomology.π (K.X (p+1)) q y,?_⟩
  apply Subtype.ext
  change ((ConcreteHomology.functor q).map (K.d (p+1) p)).hom
    (ConcreteHomology.π (K.X (p+1)) q y) = ConcreteHomology.π (K.X p) q (topCycle K p q x)
  rw [ConcreteHomology.map_π]
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨- (((-1 : ℤˣ)^p) • projection K p (q+1) (p+q+1) w),?_⟩
  apply Subtype.ext
  change (K.X p).d (q+1) q (- (((-1 : ℤˣ)^p) • projection K p (q+1) (p+q+1) w))=
    (ConcreteHomology.cyclesMap (K.d (p+1) p) q y).val - (topCycle K p q x).val
  rw [ConcreteHomology.cyclesMap_val]
  change _ = (K.d (p+1) p).f q (projection K (p+1) q (p+q+1) w) - projection K p q (p+q) x.val
  rw [hx,d_entry,map_neg,linear_units_smul]
  abel
lemma boundary_lead (p q : ℕ) (x : (filteredData K (p+q)).Z₂ ((p:ℤ)+1))
    (hx : x.val∈(filteredData K (p+q)).B₂ ((p:ℤ)+1)) : lead K p q x=0 := by
  obtain ⟨y,hy,z,hz,hyz⟩ := Submodule.mem_sup.mp hx
  have hz' := (filteredData K (p+q)).B₂_le_Z₂ ((p:ℤ)+1)
    (show z∈(filteredData K (p+q)).B₂ ((p:ℤ)+1) from Submodule.mem_sup_right hz)
  let z' : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) := ⟨z,hz'⟩
  let y' : (filteredData K (p+q)).Z₂ ((p:ℤ)+1) := x-z'
  have hy' : y'.val=y := by change x.val-z=y; rw [←hyz]; abel
  have hly : lead K p q y'=0 := by
    have ht : projection K p q (p+q) y'.val=0 := by
      rw [hy']
      exact entry_zero K hy.1 (by omega)
    have hc : topCycle K p q y'=0 := by apply Subtype.ext; exact ht
    change ConcreteHomology.π (row K q) p (topRowCycle K p q y')=0
    have hr : topRowCycle K p q y'=0 := by
      apply Subtype.ext
      change ConcreteHomology.π (K.X p) q (topCycle K p q y')=0
      rw [hc,map_zero]
    rw [hr,map_zero]
  have hlz : lead K p q z'=0 := by
    obtain ⟨w,hw,hwe⟩ := hz.1
    apply boundary_lead_zero K p q w _ z' hwe.symm
    change w∈filtration K (p+q+1) (((p:ℤ)+1)+1) at hw
    simpa only [Int.add_assoc,Int.reduceAdd] using hw
  rw [show x=y'+z' by dsimp [y']; abel,map_add,hly,hlz,add_zero]
noncomputable def descendedLead (p q : ℕ) :
    (filteredData K (p+q)).E₂ ((p:ℤ)+1) →ₗ[R] ConcreteHomology.H (row K q) p :=
  (((filteredData K (p+q)).B₂ ((p:ℤ)+1)).comap
    ((filteredData K (p+q)).Z₂ ((p:ℤ)+1)).subtype).liftQ (lead K p q)
      (fun x hx => boundary_lead K p q x hx)
end E2Leading

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEdge
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def interval {n:ℕ} (i j:Fin (n+1)) (h:i≤j) : Diagram C (Fin (n+1)) ⥤ C where
  obj D := D.obj i j h
  map f := f.app i j h
lemma interval_congr {n:ℕ} {i j i' j':Fin (n+1)} {h:i≤j} {h':i'≤j'} (hi:i=i') (hj:j=j') :
    interval (C:=C) i j h=interval i' j' h' := by subst i'; subst j'; rfl
lemma faceEdge_left {n:ℕ} (k:Fin (n+2)) (j:Fin n) (h:j.val+1<k.val) :
    reindex (C:=C) (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j =
      eval (n+1) ⋙ Pi.eval _ j.castSucc := by
  apply interval_congr
  · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val<k.val; omega)
  · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val+1<k.val; exact h)
lemma faceEdge_right {n:ℕ} (k:Fin (n+2)) (j:Fin n) (h:k.val≤j.val) :
    reindex (C:=C) (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j =
      eval (n+1) ⋙ Pi.eval _ j.succ := by
  apply interval_congr
  · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val≤j.val; exact h)
  · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val≤j.val+1; omega)
noncomputable def faceEdge_middle {n:ℕ} (k:Fin (n+2)) (j:Fin n) (h:j.val+1=k.val) :
    eval (C:=C) (n+1) ⋙ pairAt j.castSucc j.succ ≅
      reindex (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j := by
  have he:reindex (C:=C) (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j =
      interval j.castSucc.castSucc j.succ.succ (by change j.val≤j.val+2; omega) := by
    apply interval_congr
    · exact Fin.succAbove_of_castSucc_lt _ _ (by change j.val<k.val; omega)
    · exact Fin.succAbove_of_le_castSucc _ _ (by change k.val≤j.val+1; omega)
  let e : eval (C:=C) (n+1) ⋙ pairAt j.castSucc j.succ ≅
      interval j.castSucc.castSucc j.succ.succ (by change j.val≤j.val+2; omega) :=
    NatIso.ofComponents (fun D=>D.cut j.castSucc.castSucc j.succ.castSucc j.succ.succ
      (Fin.castSucc_le_castSucc_iff.mpr (Fin.castSucc_le_succ _)) (Fin.castSucc_le_succ _))
        (by intro D E f; exact f.cut _ _ _ _ _)
  exact e ≪≫ (eqToIso he).symm
noncomputable def faceEdgeIso {n:ℕ} (k:Fin (n+2)) (j:Fin n) :
    eval (C:=C) (n+1) ⋙ faceEdge k j ≅
      reindex (SimplexCategory.δ k).toOrderHom ⋙ eval n ⋙ Pi.eval _ j := by
  dsimp only [faceEdge]
  split_ifs with h h'
  · exact (eqToIso (faceEdge_left k j h)).symm
  · exact faceEdge_middle k j h'
  · exact (eqToIso (faceEdge_right k j (by omega))).symm
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveHomology
open FreeChains

variable {C D E:Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
noncomputable abbrev map (F:C⥤D) (q:ℕ) := SSet.homologyMap (nerveMap F) Z q
lemma comp (F:C⥤D) (G:D⥤E) (q:ℕ) : map (F⋙G) q=map F q ≫ map G q := by
  change SSet.homologyMap (nerveMap F ≫ nerveMap G) Z q=_
  rw [SSet.homologyMap_comp]
lemma iso {F G:C⥤D} (e:F≅G) (q:ℕ) : map F q=map G q :=
  (NerveHomotopy.ofNatTrans e.hom).congr_homologyMap Z q
lemma const (U:D) (q:ℕ) (hq:q≠0) : map ((Functor.const C).obj U) q=0 := by
  have h : nerveMap ((Functor.const C).obj U)=SSet.const (nerveEquiv.symm U) := by ext n x; rfl
  rw [map,h]
  exact ConnectedProduct.const_homology_zero (X:=nerve C) (Y:=nerve D) (nerveEquiv.symm U) q hq
end NerveHomology
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram NerveHomology

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma primitive_eval {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    primitive p i ≫ NerveHomology.map (eval n) 1=NerveHomology.map (wordInclude p i) 1 := by
  rw [primitive_eq,←NerveHomology.comp]
  exact NerveHomology.iso (Functor.isoWhiskerLeft (wordInclude p i) (eval n).asEquivalence.counitIso) 1
omit [SymmetricCategory C] in
lemma recognition {D:Type} [Category.{0} D] {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n)
    (F:D⥤IntervalBar.Diagram C (Fin (n+1))) (T:D⥤Fiber (p i))
    (e:F⋙eval n≅T⋙wordInclude p i) :
    NerveHomology.map F 1=NerveHomology.map T 1 ≫ primitive p i := by
  have := NerveHomotopy.homologyMap_isIso (eval (C:=C) n) Z 1
  apply (cancel_mono (NerveHomology.map (eval n) 1)).mp
  rw [Category.assoc,primitive_eval,←NerveHomology.comp,←NerveHomology.comp]
  exact NerveHomology.iso e 1
omit [SymmetricCategory C] in
lemma recognition_const {D:Type} [Category.{0} D] {n:ℕ} (F:D⥤IntervalBar.Diagram C (Fin (n+1)))
    (U:Fin n→C) (e:F⋙eval n≅(Functor.const D).obj U) : NerveHomology.map F 1=0 := by
  have := NerveHomotopy.homologyMap_isIso (eval (C:=C) n) Z 1
  apply (cancel_mono (NerveHomology.map (eval n) 1)).mp
  rw [zero_comp,←NerveHomology.comp,NerveHomology.iso e 1]
  exact NerveHomology.const U 1 (by decide)
noncomputable def wordDiagram_eval {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) :
    wordDiagram p i ⋙ eval n ≅ wordInclude p i :=
  Functor.isoWhiskerLeft (wordInclude p i) (eval n).asEquivalence.counitIso
noncomputable def primitiveFace_eval {n:ℕ} (p:Fin (n+1)→Skeleton C) (i:Fin (n+1))
    (k:Fin (n+2)) (j:Fin n) :
    (wordDiagram p i ⋙ reindex (SimplexCategory.δ k).toOrderHom) ⋙ eval n ⋙ Pi.eval _ j ≅
      wordInclude p i ⋙ faceEdge k j :=
  Functor.isoWhiskerLeft (wordDiagram p i) (faceEdgeIso k j).symm ≪≫
    Functor.isoWhiskerRight (wordDiagram_eval p i) (faceEdge k j)
noncomputable def wordPair_left {n:ℕ} (p:Fin n→Skeleton C) (i j:Fin n) (h:i≠j) :
    wordInclude p i ⋙ pairAt i j ≅ (property (p i)).ι ⋙ tensorRight (repr (p j)) := by
  classical
  change ((wordInclude p i ⋙ Pi.eval _ i).prod' (wordInclude p i ⋙ Pi.eval _ j)) ⋙ tensor C ≅ _
  rw [wordInclude_proj,wordInclude_proj,ite_eq_left rfl,ite_eq_right h]
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro X Y f; simp)
noncomputable def wordPair_right {n:ℕ} (p:Fin n→Skeleton C) (i j:Fin n) (h:i≠j) :
    wordInclude p j ⋙ pairAt i j ≅ (property (p j)).ι ⋙ tensorLeft (repr (p i)) := by
  classical
  change ((wordInclude p j ⋙ Pi.eval _ i).prod' (wordInclude p j ⋙ Pi.eval _ j)) ⋙ tensor C ≅ _
  rw [wordInclude_proj,wordInclude_proj,ite_eq_right h.symm,ite_eq_left rfl]
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro X Y f; simp)
noncomputable def wordPair_other {n:ℕ} (p:Fin n→Skeleton C) (i j k:Fin n) (hi:k≠i) (hj:k≠j) :
    wordInclude p k ⋙ pairAt i j ≅ (Functor.const _).obj (repr (p i) ⊗ repr (p j)) := by
  classical
  change ((wordInclude p k ⋙ Pi.eval _ i).prod' (wordInclude p k ⋙ Pi.eval _ j)) ⋙ tensor C ≅ _
  rw [wordInclude_proj,wordInclude_proj,ite_eq_right hi,ite_eq_right hj]
  exact NatIso.ofComponents (fun _=>Iso.refl _) (by intro X Y f; simp)
omit [SymmetricCategory C] in
lemma face_recognition {n:ℕ} (p:Fin (n+1)→Skeleton C) (i:Fin (n+1)) (k:Fin (n+2))
    (p':Fin n→Skeleton C) (i':Fin n) (T:Fiber (p i)⥤Fiber (p' i'))
    (e:∀j:Fin n,wordInclude p i ⋙ faceEdge k j ≅ (T⋙wordInclude p' i') ⋙ Pi.eval _ j) :
    primitive p i ≫ NerveHomology.map (reindex (SimplexCategory.δ k).toOrderHom) 1 =
      NerveHomology.map T 1 ≫ primitive p' i' := by
  rw [primitive_eq,←NerveHomology.comp]
  apply recognition p' i' _ T
  exact NatIso.pi' (fun j=>primitiveFace_eval p i k j ≪≫ e j)
omit [SymmetricCategory C] in
lemma face_recognition_const {n:ℕ} (p:Fin (n+1)→Skeleton C) (i:Fin (n+1)) (k:Fin (n+2))
    (U:Fin n→C)
    (e:∀j:Fin n,wordInclude p i ⋙ faceEdge k j ≅ (Functor.const (Fiber (p i))).obj (U j)) :
    primitive p i ≫ NerveHomology.map (reindex (SimplexCategory.δ k).toOrderHom) 1 =0 := by
  rw [primitive_eq,←NerveHomology.comp]
  apply recognition_const _ U
  exact NatIso.pi' (fun j=>primitiveFace_eval p i k j ≪≫ e j)
end MarkedH1

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_Id
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace NerveHomology
open FreeChains
@[simp] lemma id {D:Type} [Category.{0} D] (q:ℕ) : map (𝟭 D) q=𝟙 _ := by
  change SSet.homologyMap (𝟙 _) Z q=𝟙 _
  exact SSet.homologyMap_id _ _ _
end NerveHomology

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_Face200
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram NerveHomology

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_0_0 (a b:Skeleton C) :
    primitive ![a,b] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b] 0 0 (fun j=>repr (![b] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b] 0 ⋙ (Pi.eval _ (1:Fin 2)) ≅ (Functor.const (Fiber a)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
@[reassoc] lemma face_2_0_1 (a b:Skeleton C) :
    primitive ![a,b] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom) 1 =
      NerveHomology.map (translate b a (a*b) (mul_comm _ _)) 1 ≫ primitive ![(a*b)] 0 := by
  have hh := face_recognition ![a,b] 0 1 ![(a*b)] 0 (translate b a (a*b) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 0 ⋙ (pairAt (0:Fin 2) (1:Fin 2)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b)] 0 ⋙ Pi.eval _ (0:Fin 1))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b] 0 1 (by decide) ≪≫
        Functor.isoWhiskerLeft (property a).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr b)).symm
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_0_2 (a b:Skeleton C) :
    primitive ![a,b] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom) 1 =
      primitive ![a] 0 := by
  have hh := face_recognition ![a,b] 0 2 ![a] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 0 ⋙ (Pi.eval _ (0:Fin 2)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a] 0 ⋙ Pi.eval _ (0:Fin 1))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_1_0 (a b:Skeleton C) :
    primitive ![a,b] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom) 1 =
      primitive ![b] 0 := by
  have hh := face_recognition ![a,b] 1 0 ![b] 0 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 1 ⋙ (Pi.eval _ (1:Fin 2)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b] 0 ⋙ Pi.eval _ (0:Fin 1))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_1_1 (a b:Skeleton C) :
    primitive ![a,b] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom) 1 =
      NerveHomology.map (translate a b (a*b) rfl) 1 ≫ primitive ![(a*b)] 0 := by
  have hh := face_recognition ![a,b] 1 1 ![(a*b)] 0 (translate a b (a*b) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 1 ⋙ (pairAt (0:Fin 2) (1:Fin 2)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b)] 0 ⋙ Pi.eval _ (0:Fin 1))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b] 0 1 (by decide)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_1_2 (a b:Skeleton C) :
    primitive ![a,b] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b] 1 2 (fun j=>repr (![a] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b] 1 ⋙ (Pi.eval _ (0:Fin 2)) ≅ (Functor.const (Fiber b)).obj (repr a)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_0_0 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 4)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d] 0 0 (fun j=>repr (![b,d] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (1:Fin 3)) ≅ (Functor.const (Fiber a)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (2:Fin 3)) ≅ (Functor.const (Fiber a)).obj (repr d)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
@[reassoc] lemma face_3_0_1 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate b a (a*b) (mul_comm _ _)) 1 ≫ primitive ![(a*b),d] 0 := by
  have hh := face_recognition ![a,b,d] 0 1 ![(a*b),d] 0 (translate b a (a*b) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (pairAt (0:Fin 3) (1:Fin 3)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (0:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d] 0 1 (by decide) ≪≫
        Functor.isoWhiskerLeft (property a).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr b)).symm
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_0_2 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 4)).toOrderHom) 1 =
      primitive ![a,(b*d)] 0 := by
  have hh := face_recognition ![a,b,d] 0 2 ![a,(b*d)] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d)] 0 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (pairAt (1:Fin 3) (2:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d)] 0 ⋙ Pi.eval _ (1:Fin 2))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d] 1 2 0 (by decide) (by decide) ≪≫
        (Functor.const (Fiber a)).mapIso (reprMul b d)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_0_3 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 4)).toOrderHom) 1 =
      primitive ![a,b] 0 := by
  have hh := face_recognition ![a,b,d] 0 3 ![a,b] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b] 0 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_1_0 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 4)).toOrderHom) 1 =
      primitive ![b,d] 0 := by
  have hh := face_recognition ![a,b,d] 1 0 ![b,d] 0 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d] 0 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_1_1 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate a b (a*b) rfl) 1 ≫ primitive ![(a*b),d] 0 := by
  have hh := face_recognition ![a,b,d] 1 1 ![(a*b),d] 0 (translate a b (a*b) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (pairAt (0:Fin 3) (1:Fin 3)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (0:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d] 0 1 (by decide)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  exact hh
@[reassoc] lemma face_3_1_2 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate d b (b*d) (mul_comm _ _)) 1 ≫ primitive ![a,(b*d)] 1 := by
  have hh := face_recognition ![a,b,d] 1 2 ![a,(b*d)] 1 (translate d b (b*d) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (pairAt (1:Fin 3) (2:Fin 3)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (1:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d] 1 2 (by decide) ≪≫
        Functor.isoWhiskerLeft (property b).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr d)).symm
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_1_3 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 4)).toOrderHom) 1 =
      primitive ![a,b] 1 := by
  have hh := face_recognition ![a,b,d] 1 3 ![a,b] 1 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b] 1 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_0 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 4)).toOrderHom) 1 =
      primitive ![b,d] 1 := by
  have hh := face_recognition ![a,b,d] 2 0 ![b,d] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d] 1 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_1 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 4)).toOrderHom) 1 =
      primitive ![(a*b),d] 1 := by
  have hh := face_recognition ![a,b,d] 2 1 ![(a*b),d] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (pairAt (0:Fin 3) (1:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d] 1 ⋙ Pi.eval _ (0:Fin 2))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d] 0 1 2 (by decide) (by decide) ≪≫
        (Functor.const (Fiber d)).mapIso (reprMul a b)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d] 1 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_2 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate b d (b*d) rfl) 1 ≫ primitive ![a,(b*d)] 1 := by
  have hh := face_recognition ![a,b,d] 2 2 ![a,(b*d)] 1 (translate b d (b*d) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (pairAt (1:Fin 3) (2:Fin 3)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (1:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d] 1 2 (by decide)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_3 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 4)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d] 2 3 (fun j=>repr (![a,b] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (0:Fin 3)) ≅ (Functor.const (Fiber d)).obj (repr a)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (1:Fin 3)) ≅ (Functor.const (Fiber d)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d,e] 0 0 (fun j=>repr (![b,d,e] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (1:Fin 4)) ≅ (Functor.const (Fiber a)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (2:Fin 4)) ≅ (Functor.const (Fiber a)).obj (repr d)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (3:Fin 4)) ≅ (Functor.const (Fiber a)).obj (repr e)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
@[reassoc] lemma face_4_0_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate b a (a*b) (mul_comm _ _)) 1 ≫ primitive ![(a*b),d,e] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 1 ![(a*b),d,e] 0 (translate b a (a*b) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d,e] 0 1 (by decide) ≪≫
        Functor.isoWhiskerLeft (property a).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr b)).symm
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (1:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (2:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      primitive ![a,(b*d),e] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 2 ![a,(b*d),e] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d),e] 0 ⋙ Pi.eval _ (0:Fin 3))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d),e] 0 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 1 2 0 (by decide) (by decide) ≪≫
        (Functor.const (Fiber a)).mapIso (reprMul b d)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d),e] 0 ⋙ Pi.eval _ (2:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,(d*e)] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 3 ![a,b,(d*e)] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,(d*e)] 0 ⋙ Pi.eval _ (0:Fin 3))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,(d*e)] 0 ⋙ Pi.eval _ (1:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,(d*e)] 0 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 2 3 0 (by decide) (by decide) ≪≫
        (Functor.const (Fiber a)).mapIso (reprMul d e)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,d] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 4 ![a,b,d] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,d] 0 ⋙ Pi.eval _ (0:Fin 3))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,d] 0 ⋙ Pi.eval _ (1:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,d] 0 ⋙ Pi.eval _ (2:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)

end MarkedH1
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_Face410
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram NerveHomology
variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      primitive ![b,d,e] 0 := by
  have hh := face_recognition ![a,b,d,e] 1 0 ![b,d,e] 0 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d,e] 0 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d,e] 0 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d,e] 0 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate a b (a*b) rfl) 1 ≫ primitive ![(a*b),d,e] 0 := by
  have hh := face_recognition ![a,b,d,e] 1 1 ![(a*b),d,e] 0 (translate a b (a*b) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d,e] 0 1 (by decide)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  exact hh
@[reassoc] lemma face_4_1_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate d b (b*d) (mul_comm _ _)) 1 ≫ primitive ![a,(b*d),e] 1 := by
  have hh := face_recognition ![a,b,d,e] 1 2 ![a,(b*d),e] 1 (translate d b (b*d) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d,e] 1 2 (by decide) ≪≫
        Functor.isoWhiskerLeft (property b).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr d)).symm
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,(d*e)] 1 := by
  have hh := face_recognition ![a,b,d,e] 1 3 ![a,b,(d*e)] 1 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,(d*e)] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,(d*e)] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,(d*e)] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 2 3 1 (by decide) (by decide) ≪≫
        (Functor.const (Fiber b)).mapIso (reprMul d e)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,d] 1 := by
  have hh := face_recognition ![a,b,d,e] 1 4 ![a,b,d] 1 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,d] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,d] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,d] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      primitive ![b,d,e] 1 := by
  have hh := face_recognition ![a,b,d,e] 2 0 ![b,d,e] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d,e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d,e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d,e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      primitive ![(a*b),d,e] 1 := by
  have hh := face_recognition ![a,b,d,e] 2 1 ![(a*b),d,e] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d,e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 0 1 2 (by decide) (by decide) ≪≫
        (Functor.const (Fiber d)).mapIso (reprMul a b)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d,e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d,e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate b d (b*d) rfl) 1 ≫ primitive ![a,(b*d),e] 1 := by
  have hh := face_recognition ![a,b,d,e] 2 2 ![a,(b*d),e] 1 (translate b d (b*d) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d,e] 1 2 (by decide)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  exact hh
@[reassoc] lemma face_4_2_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate e d (d*e) (mul_comm _ _)) 1 ≫ primitive ![a,b,(d*e)] 2 := by
  have hh := face_recognition ![a,b,d,e] 2 3 ![a,b,(d*e)] 2 (translate e d (d*e) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate e d (d*e) (mul_comm _ _)) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (translate e d (d*e) (mul_comm _ _)) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (translate e d (d*e) (mul_comm _ _)) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d,e] 2 3 (by decide) ≪≫
        Functor.isoWhiskerLeft (property d).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr e)).symm
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,d] 2 := by
  have hh := face_recognition ![a,b,d,e] 2 4 ![a,b,d] 2 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![a,b,d] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![a,b,d] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![a,b,d] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      primitive ![b,d,e] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 0 ![b,d,e] 2 (𝟭 (Fiber e)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![b,d,e] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![b,d,e] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![b,d,e] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber e)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      primitive ![(a*b),d,e] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 1 ![(a*b),d,e] 2 (𝟭 (Fiber e)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![(a*b),d,e] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 0 1 3 (by decide) (by decide) ≪≫
        (Functor.const (Fiber e)).mapIso (reprMul a b)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![(a*b),d,e] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![(a*b),d,e] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber e)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      primitive ![a,(b*d),e] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 2 ![a,(b*d),e] 2 (𝟭 (Fiber e)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![a,(b*d),e] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![a,(b*d),e] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 1 2 3 (by decide) (by decide) ≪≫
        (Functor.const (Fiber e)).mapIso (reprMul b d)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![a,(b*d),e] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber e)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate d e (d*e) rfl) 1 ≫ primitive ![a,b,(d*e)] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 3 ![a,b,(d*e)] 2 (translate d e (d*e) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate d e (d*e) rfl) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (translate d e (d*e) rfl) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (translate d e (d*e) rfl) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d,e] 2 3 (by decide)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d,e] 3 4 (fun j=>repr (![a,b,d] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (0:Fin 4)) ≅ (Functor.const (Fiber e)).obj (repr a)
    exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (1:Fin 4)) ≅ (Functor.const (Fiber e)).obj (repr b)
    exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (2:Fin 4)) ≅ (Functor.const (Fiber e)).obj (repr d)
    exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
end MarkedH1

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedSigns
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable abbrev H (p:Skeleton C) : A := (nerve (Fiber p)).homology Z 1
noncomputable def isColimit (n:ℕ) :
    IsColimit (Cofan.mk _ (fun s:Σ_:Fin n,Fin n→Skeleton C => primitive s.2 s.1)) :=
  Cofan.IsColimit.mk _ (fun t=>desc (fun p i=>t.inj ⟨i,p⟩))
    (fun _ s=>primitive_desc _ s.2 s.1)
    (fun t _ hh=>hom_ext (fun p i=>(hh ⟨i,p⟩).trans (primitive_desc (fun p i=>t.inj ⟨i,p⟩) p i).symm))
noncomputable def signIso (h v:ℕ) (M:A) : M≅M where
  hom := (-1:ℤ)^(MarkedSigns.exponent h v) • 𝟙 M
  inv := (-1:ℤ)^(MarkedSigns.exponent h v) • 𝟙 M
  hom_inv_id := by simp only [Preadditive.zsmul_comp,Preadditive.comp_zsmul,Category.id_comp,
    smul_smul,MarkedSigns.square,one_smul]
  inv_hom_id := by simp only [Preadditive.zsmul_comp,Preadditive.comp_zsmul,Category.id_comp,
    smul_smul,MarkedSigns.square,one_smul]
noncomputable def labelIso {n:ℕ} (s:DoubleCoordinates.Index (Skeleton C) n) :
    H s.2.2.1 ≅ H ((DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1) :=
  signIso s.1.val.1 s.1.val.2 _ ≪≫ eqToIso (congrArg H (DoubleCoordinates.center s).symm)
noncomputable def labelDiagramIso (n:ℕ) :
    Discrete.functor (fun s:DoubleCoordinates.Index (Skeleton C) n=>H s.2.2.1) ≅
    Discrete.functor (fun s:DoubleCoordinates.Index (Skeleton C) n=>
      H ((DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1)) :=
  Discrete.natIso (fun s=>labelIso s.as)
noncomputable def reindexedCofan (n:ℕ) := Cofan.mk _
  (fun s:DoubleCoordinates.Index (Skeleton C) n => primitive
    (DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1)
noncomputable def labelledCofan (n:ℕ) := (Cocone.precompose (labelDiagramIso (C:=C) n).hom).obj (reindexedCofan n)
noncomputable def labelledIsColimit (n:ℕ) : IsColimit (labelledCofan (C:=C) n) :=
  (IsColimit.precomposeHomEquiv (labelDiagramIso n) (reindexedCofan n)).symm
    ((Cofan.isColimitEquivOfEquiv (DoubleCoordinates.words (Skeleton C) n) _)
      (isColimit (C:=C) (n+1)))
noncomputable def gradedIso (n:ℕ) :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).X n ≅
      (nerve (IntervalBar.Diagram C (Fin (n+1+1)))).homology Z 1 :=
  (RegularLabels.totalIsColimit (homologyDiagram (C:=C) 1) n).coconePointUniqueUpToIso
    (labelledIsColimit n)
@[reassoc] lemma totalInj_gradedIso {n:ℕ} (s:DoubleCoordinates.Index (Skeleton C) n) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) s ≫ (gradedIso n).hom =
      (labelIso s).hom ≫ primitive (DoubleCoordinates.words _ _ s).2 (DoubleCoordinates.words _ _ s).1 :=
  (RegularLabels.totalIsColimit (homologyDiagram (C:=C) 1) n).comp_coconePointUniqueUpToIso_hom
    (labelledIsColimit n) ⟨s⟩
end MarkedH1

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedGradedFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma primitive_transport {n:ℕ} {a b:Σ_:Fin n,Fin n→Skeleton C} (e:a=b) :
    eqToHom (congrArg (fun z:Σ_:Fin n,Fin n→Skeleton C=>H (z.2 z.1)) e.symm) ≫
      primitive a.2 a.1 = primitive b.2 b.1 := by
  subst b
  simp
def s00 (a:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 0 := ⟨⟨(0,0),rfl⟩,![],a,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words00 (a:Skeleton C) : DoubleCoordinates.words _ 0 (s00 a)=⟨0,![a]⟩ := by
  dsimp [s00,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j
  rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label00 (a:Skeleton C) : (labelIso (s00 a)).hom = (-1:ℤ)^0 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s00]
  rw [show MarkedSigns.exponent 0 0=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive00 (a:Skeleton C) :
    primitive (DoubleCoordinates.words _ 0 (s00 a)).2 (DoubleCoordinates.words _ 0 (s00 a)).1 =
      primitive ![a] 0 := by
  have hh:=primitive_transport (words00 a)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image00 (a:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,0),rfl⟩,![],a,![]⟩ ≫
      (gradedIso 0).hom = primitive ![a] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s00 a) ≫ _ = _
  rw [totalInj_gradedIso,label00,primitive00]
  norm_num
  try exact Category.id_comp _
def s10 (a b:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 1 := ⟨⟨(1,0),rfl⟩,![],a,![b]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words10 (a b:Skeleton C) : DoubleCoordinates.words _ 1 (s10 a b)=⟨0,![a,b]⟩ := by
  dsimp [s10,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label10 (a b:Skeleton C) : (labelIso (s10 a b)).hom = (-1:ℤ)^2 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s10]
  rw [show MarkedSigns.exponent 1 0=2 from by decide]
  change ((-1:ℤ)^2 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive10 (a b:Skeleton C) :
    primitive (DoubleCoordinates.words _ 1 (s10 a b)).2 (DoubleCoordinates.words _ 1 (s10 a b)).1 =
      primitive ![a,b] 0 := by
  have hh:=primitive_transport (words10 a b)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image10 (a b:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫
      (gradedIso 1).hom = primitive ![a,b] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s10 a b) ≫ _ = _
  rw [totalInj_gradedIso,label10,primitive10]
  norm_num
  try exact Category.id_comp _
def s01 (a b:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 1 := ⟨⟨(0,1),rfl⟩,![a],b,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words01 (a b:Skeleton C) : DoubleCoordinates.words _ 1 (s01 a b)=⟨1,![a,b]⟩ := by
  dsimp [s01,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label01 (a b:Skeleton C) : (labelIso (s01 a b)).hom = (-1:ℤ)^0 • 𝟙 (H b) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s01]
  rw [show MarkedSigns.exponent 0 1=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H b)) ≫ eqToHom (rfl: H b=H b) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive01 (a b:Skeleton C) :
    primitive (DoubleCoordinates.words _ 1 (s01 a b)).2 (DoubleCoordinates.words _ 1 (s01 a b)).1 =
      primitive ![a,b] 1 := by
  have hh:=primitive_transport (words01 a b)
  change (𝟙 (H b)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image01 (a b:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫
      (gradedIso 1).hom = primitive ![a,b] 1 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s01 a b) ≫ _ = _
  rw [totalInj_gradedIso,label01,primitive01]
  norm_num
  try exact Category.id_comp _
def s20 (a b d:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 2 := ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words20 (a b d:Skeleton C) : DoubleCoordinates.words _ 2 (s20 a b d)=⟨0,![a,b,d]⟩ := by
  dsimp [s20,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label20 (a b d:Skeleton C) : (labelIso (s20 a b d)).hom = (-1:ℤ)^5 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s20]
  rw [show MarkedSigns.exponent 2 0=5 from by decide]
  change ((-1:ℤ)^5 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive20 (a b d:Skeleton C) :
    primitive (DoubleCoordinates.words _ 2 (s20 a b d)).2 (DoubleCoordinates.words _ 2 (s20 a b d)).1 =
      primitive ![a,b,d] 0 := by
  have hh:=primitive_transport (words20 a b d)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image20 (a b d:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫
      (gradedIso 2).hom = -primitive ![a,b,d] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s20 a b d) ≫ _ = _
  rw [totalInj_gradedIso,label20,primitive20]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s11 (a b d:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 2 := ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words11 (a b d:Skeleton C) : DoubleCoordinates.words _ 2 (s11 a b d)=⟨1,![a,b,d]⟩ := by
  dsimp [s11,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label11 (a b d:Skeleton C) : (labelIso (s11 a b d)).hom = (-1:ℤ)^3 • 𝟙 (H b) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s11]
  rw [show MarkedSigns.exponent 1 1=3 from by decide]
  change ((-1:ℤ)^3 • 𝟙 (H b)) ≫ eqToHom (rfl: H b=H b) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive11 (a b d:Skeleton C) :
    primitive (DoubleCoordinates.words _ 2 (s11 a b d)).2 (DoubleCoordinates.words _ 2 (s11 a b d)).1 =
      primitive ![a,b,d] 1 := by
  have hh:=primitive_transport (words11 a b d)
  change (𝟙 (H b)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image11 (a b d:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫
      (gradedIso 2).hom = -primitive ![a,b,d] 1 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s11 a b d) ≫ _ = _
  rw [totalInj_gradedIso,label11,primitive11]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s02 (a b d:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 2 := ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words02 (a b d:Skeleton C) : DoubleCoordinates.words _ 2 (s02 a b d)=⟨2,![a,b,d]⟩ := by
  dsimp [s02,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label02 (a b d:Skeleton C) : (labelIso (s02 a b d)).hom = (-1:ℤ)^0 • 𝟙 (H d) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s02]
  rw [show MarkedSigns.exponent 0 2=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H d)) ≫ eqToHom (rfl: H d=H d) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive02 (a b d:Skeleton C) :
    primitive (DoubleCoordinates.words _ 2 (s02 a b d)).2 (DoubleCoordinates.words _ 2 (s02 a b d)).1 =
      primitive ![a,b,d] 2 := by
  have hh:=primitive_transport (words02 a b d)
  change (𝟙 (H d)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image02 (a b d:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫
      (gradedIso 2).hom = primitive ![a,b,d] 2 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s02 a b d) ≫ _ = _
  rw [totalInj_gradedIso,label02,primitive02]
  norm_num
  try exact Category.id_comp _
def s30 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words30 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s30 a b d e)=⟨0,![a,b,d,e]⟩ := by
  dsimp [s30,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label30 (a b d e:Skeleton C) : (labelIso (s30 a b d e)).hom = (-1:ℤ)^9 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s30]
  rw [show MarkedSigns.exponent 3 0=9 from by decide]
  change ((-1:ℤ)^9 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive30 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s30 a b d e)).2 (DoubleCoordinates.words _ 3 (s30 a b d e)).1 =
      primitive ![a,b,d,e] 0 := by
  have hh:=primitive_transport (words30 a b d e)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image30 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫
      (gradedIso 3).hom = -primitive ![a,b,d,e] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s30 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label30,primitive30]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s21 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words21 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s21 a b d e)=⟨1,![a,b,d,e]⟩ := by
  dsimp [s21,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label21 (a b d e:Skeleton C) : (labelIso (s21 a b d e)).hom = (-1:ℤ)^7 • 𝟙 (H b) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s21]
  rw [show MarkedSigns.exponent 2 1=7 from by decide]
  change ((-1:ℤ)^7 • 𝟙 (H b)) ≫ eqToHom (rfl: H b=H b) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive21 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s21 a b d e)).2 (DoubleCoordinates.words _ 3 (s21 a b d e)).1 =
      primitive ![a,b,d,e] 1 := by
  have hh:=primitive_transport (words21 a b d e)
  change (𝟙 (H b)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image21 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫
      (gradedIso 3).hom = -primitive ![a,b,d,e] 1 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s21 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label21,primitive21]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s12 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words12 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s12 a b d e)=⟨2,![a,b,d,e]⟩ := by
  dsimp [s12,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label12 (a b d e:Skeleton C) : (labelIso (s12 a b d e)).hom = (-1:ℤ)^4 • 𝟙 (H d) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s12]
  rw [show MarkedSigns.exponent 1 2=4 from by decide]
  change ((-1:ℤ)^4 • 𝟙 (H d)) ≫ eqToHom (rfl: H d=H d) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive12 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s12 a b d e)).2 (DoubleCoordinates.words _ 3 (s12 a b d e)).1 =
      primitive ![a,b,d,e] 2 := by
  have hh:=primitive_transport (words12 a b d e)
  change (𝟙 (H d)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image12 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫
      (gradedIso 3).hom = primitive ![a,b,d,e] 2 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s12 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label12,primitive12]
  norm_num
  try exact Category.id_comp _
def s03 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words03 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s03 a b d e)=⟨3,![a,b,d,e]⟩ := by
  dsimp [s03,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label03 (a b d e:Skeleton C) : (labelIso (s03 a b d e)).hom = (-1:ℤ)^0 • 𝟙 (H e) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s03]
  rw [show MarkedSigns.exponent 0 3=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H e)) ≫ eqToHom (rfl: H e=H e) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive03 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s03 a b d e)).2 (DoubleCoordinates.words _ 3 (s03 a b d e)).1 =
      primitive ![a,b,d,e] 3 := by
  have hh:=primitive_transport (words03 a b d e)
  change (𝟙 (H e)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image03 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫
      (gradedIso 3).hom = primitive ![a,b,d,e] 3 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s03 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label03,primitive03]
  norm_num
  try exact Category.id_comp _
end MarkedH1

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FinitePowerGeneral
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram StageProductColimit SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] (κ:Type)
noncomputable def singleProject (n:ℕ) :
    Diagram (κ→C) (Fin (n+1)) ⥤ (κ→Diagram C (Fin (n+1))) :=
  Functor.pi' (fun k => map (I:=Fin (n+1)) (project κ k))
lemma singleProject_eval (n:ℕ) :
    singleProject (C:=C) κ n ⋙ powerMap κ (eval n) = eval n ⋙ swap (Fin n) κ := rfl
noncomputable instance instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject (n:ℕ) : (singleProject (C:=C) κ n).IsEquivalence := by
  have : (singleProject (C:=C) κ n ⋙ powerMap κ (eval n)).IsEquivalence := by
    rw [singleProject_eval]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (powerMap κ (eval n))
noncomputable def singlePowerComparison : bar (C:=κ→C) ⟶ (power κ).obj (bar (C:=C)) :=
  lift κ (fun k => barMap (project κ k))
noncomputable def doublePowerComparison : bar₂ (C:=κ→C) ⟶ (power κ).obj (bar₂ (C:=C)) :=
  lift κ (fun k => bar₂Map (project κ k))
lemma singleDegree_homology_isIso (p q:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k=>nerveMap (map (I:=Fin (p+1)) (project (C:=C) κ k)))) DiagonalResolution.Z q) := by
  have : (Functor.pi' (fun k=>map (I:=Fin (p+1)) (project (C:=C) κ k))).IsEquivalence :=
    inferInstanceAs (singleProject (C:=C) κ p).IsEquivalence
  exact lift_nerve_homology_isIso κ (fun k=>map (I:=Fin (p+1)) (project (C:=C) κ k)) q
lemma singleRow_homology_isIso (p:SimplexCategoryᵒᵖ) (q:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k =>
      (Functor.whiskerRight (simplicialMap (project (C:=C) κ k)) nerveFunctor).app p)) DiagonalResolution.Z q) := by
  exact singleDegree_homology_isIso κ p.unop.len q
lemma single_power_diagonal_eq : singlePowerComparison (C:=C) κ =
    lift κ (fun k => diagonal.map (Functor.whiskerRight (simplicialMap (project (C:=C) κ k)) nerveFunctor)) := rfl
lemma singlePowerComparison_homology_isIso (n:ℕ) :
    IsIso (SSet.homologyMap (singlePowerComparison (C:=C) κ) DiagonalResolution.Z n) := by
  rw [single_power_diagonal_eq]
  apply homologyLiftDiagonal_isIso
  intro p q
  exact singleRow_homology_isIso (C:=C) κ p q
lemma doubleFirst_homology_isIso (p q:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k=>barMap (map (I:=Fin (p+1)) (project (C:=C) κ k)))) DiagonalResolution.Z q) := by
  apply homologyLiftDiagonal_isIso κ (fun k => Functor.whiskerRight
    (simplicialMap (map (I:=Fin (p+1)) (project (C:=C) κ k))) nerveFunctor)
  intro l r
  exact doubleDegree_homology_isIso κ l.unop.len p r
lemma doublePowerComparison_homology_isIso (n:ℕ) :
    IsIso (SSet.homologyMap (doublePowerComparison (C:=C) κ) DiagonalResolution.Z n) := by
  apply homologyLiftDiagonal_isIso κ (fun k => rows₂Map (project (C:=C) κ k))
  intro p q
  exact doubleFirst_homology_isIso κ p.unop.len q
end BarFinitePower

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedTensorFinite
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains

attribute [local instance 1200] Submodule.module
variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
noncomputable def redProjection (n:ℕ) :
    ((X⊗Y).homology Z n : A) ⟶
      (((ConstantSplit.sc X).X₁)⊗((ConstantSplit.sc Y).X₁)).homology n :=
  (homologyIsoN X Y n).hom ≫ homologyMap
    ((ConstantSplit.splitting X (point X)).r⊗ₘ(ConstantSplit.splitting Y (point Y)).r) n
end ConnectedProduct

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_LowerBarComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower
noncomputable def powerTwoIso (X:SSet) : (power (Fin 2)).obj X ≅ X⊗X where
  hom := { app _ := ↾fun x => (x 0,x 1)
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun x=>![x.1,x.2]
           naturality _ _ _ := by apply ConcreteCategory.hom_ext; intro x; funext i; fin_cases i <;> rfl }
  hom_inv_id := by apply NatTrans.ext;funext p;apply ConcreteCategory.hom_ext;intro x;funext i;fin_cases i <;> rfl
  inv_hom_id := by ext p x <;> rfl
noncomputable def powerOneIso (X:SSet) : (power (Fin 1)).obj X ≅ X where
  hom := evaluate _ _ 0
  inv := { app _ := ↾fun x _=>x
           naturality _ _ _ := rfl }
  hom_inv_id := by apply NatTrans.ext;funext p;apply ConcreteCategory.hom_ext;intro x;funext i;exact congrArg x (Subsingleton.elim _ _)
  inv_hom_id := by ext p x; rfl
end BarFinitePower

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.mapEssSurj _root_.OAI.IntervalBar.Diagram.mapFaithful _root_.OAI.IntervalBar.Diagram.mapFull _root_.OAI.IntervalBar.Diagram.mapIsEquivalence _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_nerve_connected _root_.OAI.IntervalBar.Diagram.zero_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory
namespace RestrictedNerve

section

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
noncomputable instance inclusionMonoidal : (inclusion W).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by intros; simp
    μIso_hom_natural_right := by intros; simp
    associativity := by intros; simp
    left_unitality := by intros; simp
    right_unitality := by intros; simp }
noncomputable instance inclusionBraided : (inclusion W).Braided where
  braided _ _ := by
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
end

open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable (I : Type) [Preorder I]
noncomputable abbrev diagramInclusion := Diagram.map (I:=I) (inclusion W)
abbrev PosDiagrams := InducedCategory (Diagram C I) (diagramInclusion W I).obj
def diagramProperty : MorphismProperty (PosDiagrams W I) :=
  fun _ _ f => ∀ i j h, W (f.hom.app i j h)
instance diagramProperty_multiplicative : (diagramProperty W I).IsMultiplicative where
  id_mem object first last ordered := W.id_mem ((diagramInclusion W I).obj object |>.obj first last ordered)
  comp_mem first second hfirst hsecond start finish ordered :=
    W.comp_mem (first.hom.app start finish ordered) (second.hom.app start finish ordered)
      (hfirst start finish ordered) (hsecond start finish ordered)

variable {I}
noncomputable def stringVertex {n : ℕ} (A : Diagram (Strings W n) I) (t : Fin (n+1)) :
    PosDiagrams W I where
  obj i j h := ⟨(A.obj i j h).obj.obj t⟩
  unit i := {
    hom := ⟨(A.unit i).hom.hom.app t,(A.unit i).hom.property t⟩
    inv := ⟨(A.unit i).inv.hom.app t,(A.unit i).inv.property t⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.unit i).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.unit i).inv_hom_id }
  cut i j k hij hjk := {
    hom := ⟨(A.cut i j k hij hjk).hom.hom.app t,(A.cut i j k hij hjk).hom.property t⟩
    inv := ⟨(A.cut i j k hij hjk).inv.hom.app t,(A.cut i j k hij hjk).inv.property t⟩
    hom_inv_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.cut i j k hij hjk).hom_inv_id
    inv_hom_id := by
      apply WideSubcategory.hom_ext
      exact congrArg (fun f => f.hom.app t) (A.cut i j k hij hjk).inv_hom_id }
  left_unit i j h := by
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.hom.app t) (A.left_unit i j h)
  right_unit i j h := by
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.hom.app t) (A.right_unit i j h)
  associativity i j k l hij hjk hkl := by
    apply WideSubcategory.hom_ext
    exact congrArg (fun f => f.hom.app t) (A.associativity i j k l hij hjk hkl)
noncomputable def stringVertexMap {n : ℕ} (A : Diagram (Strings W n) I)
    {t s : Fin (n+1)} (f : t ⟶ s) :
    stringVertex W A t ⟶ stringVertex W A s :=
  InducedCategory.homMk {
    app i j h := (A.obj i j h).obj.map f
    unit i := by
      change (A.obj i i le_rfl).obj.map f ≫ ((A.unit i).hom.hom.app s ≫ 𝟙 _) =
        (A.unit i).hom.hom.app t ≫ 𝟙 _
      simp
    cut i j k hij hjk := by
      change ((A.obj i j hij).obj.map f ⊗ₘ (A.obj j k hjk).obj.map f) ≫
          (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app s) =
        (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app t) ≫ (A.obj i k _).obj.map f
      erw [Category.id_comp, Category.id_comp]
      exact (A.cut i j k hij hjk).hom.hom.naturality f }
noncomputable def transposeDiagramObj {n : ℕ} (A : Diagram (Strings W n) I) :
    Strings (diagramProperty W I) n := ⟨{
  obj := stringVertex W A
  map := stringVertexMap W A
  map_id t := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (A.obj i j h).obj.map_id t
  map_comp f g := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (A.obj i j h).obj.map_comp f g }⟩
noncomputable def transposeDiagramHom {n : ℕ} {A B : Diagram (Strings W n) I} (f : A ⟶ B) :
    transposeDiagramObj W A ⟶ transposeDiagramObj W B := ⟨{
  app t := InducedCategory.homMk {
    app i j h := (f.app i j h).hom.app t
    unit i := by
      change (f.app i i le_rfl).hom.app t ≫ ((B.unit i).hom.hom.app t ≫ 𝟙 _) =
        (A.unit i).hom.hom.app t ≫ 𝟙 _
      simpa using congrArg (fun f => f.hom.app t) (f.unit i)
    cut i j k hij hjk := by
      change ((f.app i j hij).hom.app t ⊗ₘ (f.app j k hjk).hom.app t) ≫
          (𝟙 _ ≫ (B.cut i j k hij hjk).hom.hom.app t) =
        (𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app t) ≫ (f.app i k _).hom.app t
      erw [Category.id_comp, Category.id_comp]
      exact congrArg (fun f => f.hom.app t) (f.cut i j k hij hjk) }
  naturality s t g := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    exact (f.app i j h).hom.naturality g },
    fun t i j h => (f.app i j h).property t⟩
noncomputable def transposeDiagram (n : ℕ) : Diagram (Strings W n) I ⥤ Strings (diagramProperty W I) n where
  obj := transposeDiagramObj W
  map := transposeDiagramHom W
  map_id A := by
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intros; rfl
  map_comp f g := by
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intros; rfl
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_InducedMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.mapEssSurj _root_.OAI.IntervalBar.Diagram.mapFaithful _root_.OAI.IntervalBar.Diagram.mapFull _root_.OAI.IntervalBar.Diagram.mapIsEquivalence _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_nerve_connected _root_.OAI.IntervalBar.Diagram.zero_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory MonoidalCategory
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable (I : Type) [Preorder I]
noncomputable instance posDiagramIsIso {X Y : PosDiagrams W I} (f : X ⟶ Y) : IsIso f := by
  refine ⟨⟨InducedCategory.homMk (inv f.hom),?_,?_⟩⟩
  · apply InducedCategory.hom_ext; exact IsIso.hom_inv_id f.hom
  · apply InducedCategory.hom_ext; exact IsIso.inv_hom_id f.hom
noncomputable instance posDiagramGroupoid : Groupoid (PosDiagrams W I) :=
  Groupoid.ofIsIso (fun _ => inferInstance)
noncomputable instance posDiagramMonoidal : MonoidalCategory (PosDiagrams W I) :=
  InducedMonoidal.monoidal (diagramInclusion W I)
noncomputable instance posDiagramBraided : BraidedCategory (PosDiagrams W I) :=
  InducedMonoidal.braided (diagramInclusion W I)
noncomputable instance posDiagramSymmetric : SymmetricCategory (PosDiagrams W I) :=
  InducedMonoidal.symmetric (diagramInclusion W I)
instance diagramPropertyInverse : Fact (diagramProperty W I).StableUnderInverse where
  out _ _ e h i j hij := by
    let he : _ ≅ _ := {
      hom := e.hom.hom.app i j hij
      inv := e.inv.hom.app i j hij
      hom_inv_id := congrArg (fun f => f.hom.app i j hij) e.hom_inv_id
      inv_hom_id := congrArg (fun f => f.hom.app i j hij) e.inv_hom_id }
    exact (Fact.out : W.StableUnderInverse) he (h i j hij)
open Functor.LaxMonoidal Functor.OplaxMonoidal
@[simp] lemma diagram_μ_app (A B : Diagram (WideSubcategory W) I) (i j : I) (h:i≤j) :
    (μ (diagramInclusion W I) A B).app i j h = 𝟙 _ := rfl
@[simp] lemma diagram_δ_app (A B : Diagram (WideSubcategory W) I) (i j : I) (h:i≤j) :
    (δ (diagramInclusion W I) A B).app i j h = 𝟙 _ := by
  change (CategoryTheory.inv (mapμHom (inclusion W) A B)).app i j h = 𝟙 _
  rw [inv_app]
  change CategoryTheory.inv (𝟙 _) = 𝟙 _
  simp
@[simp] lemma posTensor_app {A B A' B' : PosDiagrams W I} (f : A ⟶ B) (g : A' ⟶ B')
    (i j:I) (h:i≤j) : (f ⊗ₘ g).hom.app i j h = f.hom.app i j h ⊗ₘ g.hom.app i j h := by
  change (δ (diagramInclusion W I) A A' ≫ (f.hom ⊗ₘ g.hom) ≫ μ (diagramInclusion W I) B B').app i j h = _
  simp only [comp_app,diagram_δ_app,diagram_μ_app,tensor_app]
  erw [Category.id_comp, Category.comp_id]
@[simp] lemma posWhiskerLeft_app (A : PosDiagrams W I) {B D : PosDiagrams W I} (f : B ⟶ D)
    (i j:I) (h:i≤j) : (A ◁ f).hom.app i j h = ((diagramInclusion W I).obj A).obj i j h ◁ f.hom.app i j h := by
  change (δ (diagramInclusion W I) A B ≫ _ ◁ f.hom ≫ μ (diagramInclusion W I) A D).app i j h = _
  simp only [comp_app,diagram_δ_app,diagram_μ_app,whiskerLeft_app]
  erw [Category.id_comp, Category.comp_id]
@[simp] lemma posWhiskerRight_app {A B : PosDiagrams W I} (f : A ⟶ B) (D : PosDiagrams W I)
    (i j:I) (h:i≤j) : (f ▷ D).hom.app i j h = f.hom.app i j h ▷ ((diagramInclusion W I).obj D).obj i j h := by
  change (δ (diagramInclusion W I) A D ≫ f.hom ▷ _ ≫ μ (diagramInclusion W I) B D).app i j h = _
  simp only [comp_app,diagram_δ_app,diagram_μ_app,whiskerRight_app]
  erw [Category.id_comp, Category.comp_id]
@[simp] lemma posAssoc_app (A B D : PosDiagrams W I) (i j:I) (h:i≤j) :
    (α_ A B D).hom.hom.app i j h =
      (α_ ((diagramInclusion W I).obj A |>.obj i j h)
        ((diagramInclusion W I).obj B |>.obj i j h) ((diagramInclusion W I).obj D |>.obj i j h)).hom := rfl
@[simp] lemma posLeft_app (A : PosDiagrams W I) (i j:I) (h:i≤j) :
    (λ_ A).hom.hom.app i j h = (λ_ ((diagramInclusion W I).obj A |>.obj i j h)).hom := rfl
@[simp] lemma posRight_app (A : PosDiagrams W I) (i j:I) (h:i≤j) :
    (ρ_ A).hom.hom.app i j h = (ρ_ ((diagramInclusion W I).obj A |>.obj i j h)).hom := rfl
@[simp] lemma posBraiding_app (A B : PosDiagrams W I) (i j:I) (h:i≤j) :
    (β_ A B).hom.hom.app i j h =
      (β_ ((diagramInclusion W I).obj A |>.obj i j h) ((diagramInclusion W I).obj B |>.obj i j h)).hom := rfl
instance diagramPropertyMonoidal : (diagramProperty W I).IsMonoidalStable where
  whiskerLeft A _ _ f hf i j h := by
    change W ((δ (diagramInclusion W I) A _ ≫ _ ◁ f.hom ≫ μ (diagramInclusion W I) A _).app i j h)
    simp only [comp_app,whiskerLeft_app,diagram_δ_app,diagram_μ_app]
    erw [Category.id_comp, Category.comp_id]
    exact W.whiskerLeft_mem _ _ (hf i j h)
  whiskerRight f hf B i j h := by
    change W ((δ (diagramInclusion W I) _ B ≫ f.hom ▷ _ ≫ μ (diagramInclusion W I) _ B).app i j h)
    simp only [comp_app,whiskerRight_app,diagram_δ_app,diagram_μ_app]
    erw [Category.id_comp, Category.comp_id]
    exact W.whiskerRight_mem _ (hf i j h) _
  associator_hom_mem first second third lower upper bound := W.associator_hom_mem
    (((diagramInclusion W I).obj first).obj lower upper bound)
    (((diagramInclusion W I).obj second).obj lower upper bound)
    (((diagramInclusion W I).obj third).obj lower upper bound)
  associator_inv_mem first second third :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (α_ first second third)
      (fun lower upper bound => W.associator_hom_mem
        (((diagramInclusion W I).obj first).obj lower upper bound)
        (((diagramInclusion W I).obj second).obj lower upper bound)
        (((diagramInclusion W I).obj third).obj lower upper bound))
  leftUnitor_hom_mem diagram lower upper bound := W.leftUnitor_hom_mem
    (((diagramInclusion W I).obj diagram).obj lower upper bound)
  leftUnitor_inv_mem diagram :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (λ_ diagram)
      (fun lower upper bound => W.leftUnitor_hom_mem
        (((diagramInclusion W I).obj diagram).obj lower upper bound))
  rightUnitor_hom_mem diagram lower upper bound := W.rightUnitor_hom_mem
    (((diagramInclusion W I).obj diagram).obj lower upper bound)
  rightUnitor_inv_mem diagram :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (ρ_ diagram)
      (fun lower upper bound => W.rightUnitor_hom_mem
        (((diagramInclusion W I).obj diagram).obj lower upper bound))
instance diagramPropertyBraided : (diagramProperty W I).IsStableUnderBraiding where
  braiding_hom_mem first second lower upper bound := W.braiding_hom_mem
    (((diagramInclusion W I).obj first).obj lower upper bound)
    (((diagramInclusion W I).obj second).obj lower upper bound)
  braiding_inv_mem first second :=
    (Fact.out : (diagramProperty W I).StableUnderInverse) (β_ first second)
      (fun lower upper bound => W.braiding_hom_mem
        (((diagramInclusion W I).obj first).obj lower upper bound)
        (((diagramInclusion W I).obj second).obj lower upper bound))
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidalTranspose
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I : Type} [Preorder I] (n : ℕ)
noncomputable def transposeε : (𝟙_ (Strings (diagramProperty W I) n)) ⟶
    (transposeDiagram W n).obj (𝟙_ (Diagram (Strings W n) I)) := ⟨{
  app t := InducedCategory.homMk {
    app i j h := 𝟙 _
    unit i := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [Category.id_comp]
      rfl
    cut i j k hij hjk := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [id_tensorHom_id, Category.id_comp, Category.comp_id]
      rfl }
  naturality t s f := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    simp [transposeDiagram,transposeDiagramObj,stringVertexMap,diagramInclusion]
    change (𝟙 (𝟙_ C)) = 𝟙 _ ≫ 𝟙 _
    exact (Category.id_comp _).symm },
  by intro t i j h; exact W.id_mem _⟩
noncomputable def transposeμ (A B : Diagram (Strings W n) I) :
    (transposeDiagram W n).obj A ⊗ (transposeDiagram W n).obj B ⟶
    (transposeDiagram W n).obj (A ⊗ B) := ⟨{
  app t := InducedCategory.homMk {
    app i j h := 𝟙 _
    unit i := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [Category.id_comp]
      rfl
    cut i j k hij hjk := by
      simp [transposeDiagram,transposeDiagramObj,stringVertex,diagramInclusion,mapObj]
      erw [id_tensorHom_id, Category.id_comp, Category.comp_id]
      rfl }
  naturality t s f := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    change (stringVertexMap W A f ⊗ₘ stringVertexMap W B f).hom.app i j h ≫ 𝟙 _ =
      𝟙 _ ≫ ((A.obj i j h).obj.map f ⊗ₘ (B.obj i j h).obj.map f)
    erw [posTensor_app]
    change ((A.obj i j h).obj.map f ⊗ₘ (B.obj i j h).obj.map f) ≫ 𝟙 _ =
      𝟙 _ ≫ ((A.obj i j h).obj.map f ⊗ₘ (B.obj i j h).obj.map f)
    simp only [Category.comp_id, Category.id_comp] },
  by intro t i j h; exact W.id_mem _⟩
lemma transposeμ_natural_left {A B : Diagram (Strings W n) I}
    (f : A ⟶ B) (D : Diagram (Strings W n) I) :
    ((transposeDiagram W n).map f ▷ (transposeDiagram W n).obj D) ≫ transposeμ W n B D =
      transposeμ W n A D ≫ (transposeDiagram W n).map (f ▷ D) := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  change ((transposeDiagramHom W f).hom.app t ▷ (transposeDiagramObj W D).obj.obj t).hom.app i j h ≫ 𝟙 _ =
    𝟙 _ ≫ ((transposeDiagramHom W (f ▷ D)).hom.app t).hom.app i j h
  erw [posWhiskerRight_app]
  change ((f.app i j h).hom.app t ▷ (D.obj i j h).obj.obj t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((f ▷ D).app i j h).hom.app t
  erw [Diagram.whiskerRight_app]
  change ((f.app i j h).hom.app t ▷ (D.obj i j h).obj.obj t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((f.app i j h).hom.app t ▷ (D.obj i j h).obj.obj t)
  simp only [Category.comp_id, Category.id_comp]

lemma transposeμ_natural_right {A B : Diagram (Strings W n) I}
    (D : Diagram (Strings W n) I) (f : A ⟶ B) :
    ((transposeDiagram W n).obj D ◁ (transposeDiagram W n).map f) ≫ transposeμ W n D B =
      transposeμ W n D A ≫ (transposeDiagram W n).map (D ◁ f) := by
  apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
  apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
  change ((transposeDiagramObj W D).obj.obj t ◁ (transposeDiagramHom W f).hom.app t).hom.app i j h ≫ 𝟙 _ =
    𝟙 _ ≫ ((transposeDiagramHom W (D ◁ f)).hom.app t).hom.app i j h
  erw [posWhiskerLeft_app]
  change ((D.obj i j h).obj.obj t ◁ (f.app i j h).hom.app t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((D ◁ f).app i j h).hom.app t
  erw [Diagram.whiskerLeft_app]
  change ((D.obj i j h).obj.obj t ◁ (f.app i j h).hom.app t) ≫ 𝟙 _ =
    𝟙 _ ≫ ((D.obj i j h).obj.obj t ◁ (f.app i j h).hom.app t)
  simp only [Category.comp_id, Category.id_comp]

noncomputable instance transposeMonoidal : (transposeDiagram (I:=I) W n).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso (transposeε W n)
    μIso A B := asIso (transposeμ W n A B)
    μIso_hom_natural_left := by
      intro A B f D
      exact transposeμ_natural_left W n f D
    μIso_hom_natural_right := by
      intro A B D f
      exact transposeμ_natural_right W n D f
    associativity := by
      intro A B D
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      change (((transposeμ W n A B).hom.app t ▷ (transposeDiagramObj W D).obj.obj t).hom.app i j h) ≫
          ((transposeμ W n (A ⊗ B) D).hom.app t).hom.app i j h ≫
          ((transposeDiagramHom W (α_ A B D).hom).hom.app t).hom.app i j h =
        (α_ (stringVertex W A t) (stringVertex W B t) (stringVertex W D t)).hom.hom.app i j h ≫
          ((stringVertex W A t ◁ (transposeμ W n B D).hom.app t).hom.app i j h) ≫
          ((transposeμ W n A (B ⊗ D)).hom.app t).hom.app i j h
      erw [posWhiskerRight_app, posWhiskerLeft_app, posAssoc_app]
      change (𝟙 _ ▷ (D.obj i j h).obj.obj t) ≫ 𝟙 _ ≫
          (α_ ((A.obj i j h).obj.obj t) ((B.obj i j h).obj.obj t) ((D.obj i j h).obj.obj t)).hom =
        (α_ ((A.obj i j h).obj.obj t) ((B.obj i j h).obj.obj t) ((D.obj i j h).obj.obj t)).hom ≫
          ((A.obj i j h).obj.obj t ◁ 𝟙 _) ≫ 𝟙 _
      simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
    left_unitality := by
      intro A
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      change (λ_ ((A.obj i j h).obj.obj t)).hom =
        (((transposeε W n).hom.app t ▷ stringVertex W A t).hom.app i j h) ≫
          𝟙 _ ≫ (λ_ ((A.obj i j h).obj.obj t)).hom
      erw [posWhiskerRight_app]
      change (λ_ ((A.obj i j h).obj.obj t)).hom =
        (𝟙 _ ▷ (A.obj i j h).obj.obj t) ≫ 𝟙 _ ≫ (λ_ ((A.obj i j h).obj.obj t)).hom
      simp only [id_whiskerRight, Category.id_comp]
    right_unitality := by
      intro A
      apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      change (ρ_ ((A.obj i j h).obj.obj t)).hom =
        ((stringVertex W A t ◁ (transposeε W n).hom.app t).hom.app i j h) ≫
          𝟙 _ ≫ (ρ_ ((A.obj i j h).obj.obj t)).hom
      erw [posWhiskerLeft_app]
      change (ρ_ ((A.obj i j h).obj.obj t)).hom =
        ((A.obj i j h).obj.obj t ◁ 𝟙 _) ≫ 𝟙 _ ≫ (ρ_ ((A.obj i j h).obj.obj t)).hom
      simp only [whiskerLeft_id, Category.id_comp] }
noncomputable instance transposeBraided : (transposeDiagram (I:=I) W n).Braided where
  braided A B := by
    change transposeμ W n A B ≫ (transposeDiagram W n).map (β_ A B).hom =
      (β_ ((transposeDiagram W n).obj A) ((transposeDiagram W n).obj B)).hom ≫ transposeμ W n B A
    apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    simp [transposeμ,transposeDiagram,transposeDiagramHom]
    erw [InducedCategory.comp_hom, comp_app, comp_app, posBraiding_app]
    erw [Category.id_comp, Category.comp_id]
    rfl
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Functor.LaxMonoidal
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
instance inclusionEssSurj : (inclusion W).EssSurj where
  mem_essImage X := ⟨⟨X⟩,⟨Iso.refl X⟩⟩
noncomputable abbrev posDiagramInclusion (I : Type) [Preorder I] :=
  InducedMonoidal.inclusion (diagramInclusion W I)
noncomputable instance posDiagramInclusionBraided (I : Type) [Preorder I] :
    (posDiagramInclusion W I).Braided := InducedMonoidal.inclusionBraided (diagramInclusion W I)
end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I : Type} [Preorder I]
@[simp] lemma eqToHom_transposed_app {n : ℕ} {A B : Strings (diagramProperty W I) n}
    (e : A=B) (t : Fin (n+1)) (i j : I) (h : i≤j) :
    ((eqToHom e).hom.app t).hom.app i j h =
      eqToHom (congrArg (fun A : Strings (diagramProperty W I) n => ((diagramInclusion W I).obj (A.obj.obj t)).obj i j h) e) := by
  cases e; rfl
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedFunctorial
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]

noncomputable def posReindex (u:I→oJ) : PosDiagrams W J ⥤ PosDiagrams W I where
  obj A := (Diagram.reindex (C:=WideSubcategory W) u).obj A
  map f := InducedCategory.homMk {
    app i j h := f.hom.app (u i) (u j) (u.monotone h)
    unit i := f.hom.unit (u i)
    cut i j k hij hjk := f.hom.cut (u i) (u j) (u k) (u.monotone hij) (u.monotone hjk) }
lemma posReindex_property (u:I→oJ) {A B:PosDiagrams W J} (f:A⟶B)
    (hf:diagramProperty W J f) : diagramProperty W I ((posReindex W u).map f) :=
  fun i j h=>hf (u i) (u j) (u.monotone h)
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_DiagramResolutionNatural
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J:Type} [Preorder I] [Preorder J]

noncomputable instance posReindexMonoidal (u:I→oJ) : (posReindex W u).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      simp [posReindex,posWhiskerRight_app]
      rfl
    μIso_hom_natural_right := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      simp [posReindex,posWhiskerLeft_app]
      rfl
    associativity := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      rfl
    left_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      rfl
    right_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
      rfl }
noncomputable instance posReindexBraided (u:I→oJ) : (posReindex W u).Braided where
  braided A B := by
    apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
noncomputable def widePosReindex (u:I→oJ) :
    WideSubcategory (diagramProperty W J) ⥤ WideSubcategory (diagramProperty W I) where
  obj A := ⟨(posReindex W u).obj A.obj⟩
  map f := ⟨(posReindex W u).map f.hom,posReindex_property W u f.hom f.property⟩
  map_id A := by apply WideSubcategory.hom_ext; exact (posReindex W u).map_id _
  map_comp f g := by apply WideSubcategory.hom_ext; exact (posReindex W u).map_comp _ _
noncomputable instance widePosReindexMonoidal (u:I→oJ) : (widePosReindex W u).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso _ _ := Iso.refl _
    μIso_hom_natural_left := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h
      simp [widePosReindex,posReindex,posWhiskerRight_app]
      rfl
    μIso_hom_natural_right := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h
      simp [widePosReindex,posReindex,posWhiskerLeft_app]
      rfl
    associativity := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h; rfl
    left_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h; rfl
    right_unitality := by
      intros
      simp only [Iso.refl_hom]
      repeat' first | erw [id_whiskerRight] | erw [whiskerLeft_id] | erw [Category.comp_id] | erw [Category.id_comp]
      apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext
      apply Hom.ext; intro i j h; rfl }
noncomputable instance widePosReindexBraided (u:I→oJ) : (widePosReindex W u).Braided where
  braided A B := by
    apply WideSubcategory.hom_ext; apply InducedCategory.hom_ext; apply Hom.ext; intro i j h
    change 𝟙 _ ≫ (β_ _ _).hom = (β_ _ _).hom ≫ 𝟙 _
    simp
end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_MonoidalCongruence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve
open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I:Type} [Preorder I]
@[simp] lemma transpose_ε (n:ℕ) :
    Functor.LaxMonoidal.ε (transposeDiagram (I:=I) W n)=transposeε W n := rfl
@[simp] lemma transpose_μ (n:ℕ) (A B:Diagram (Strings W n) I) :
    Functor.LaxMonoidal.μ (transposeDiagram W n) A B=transposeμ W n A B := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma reindex_ε {n m:ℕ} (u:Fin (n+1)⥤Fin (m+1)) :
    Functor.LaxMonoidal.ε (reindex W u)=𝟙 _ := rfl
@[simp] lemma map_reindex_ε {n m:ℕ} (u:Fin (n+1)⥤Fin (m+1)) :
    Functor.LaxMonoidal.ε (Diagram.map (I:=I) (reindex W u))=Diagram.mapεHom (reindex W u) := rfl
@[simp] lemma map_reindex_μ {n m:ℕ} (u:Fin (n+1)⥤Fin (m+1)) (A B:Diagram (Strings W m) I) :
    Functor.LaxMonoidal.μ (Diagram.map (reindex W u)) A B=Diagram.mapμHom (reindex W u) A B := rfl
end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_NestedPosReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
omit [Fact W.StableUnderInverse] in
@[simp] lemma inclusion_η : Functor.OplaxMonoidal.η (inclusion W) = 𝟙 _ := rfl
omit [Fact W.StableUnderInverse] in
@[simp] lemma inclusion_μ (A B:WideSubcategory W) :
    Functor.LaxMonoidal.μ (inclusion W) A B = 𝟙 _ := rfl
@[simp] lemma widePosReindex_η (u:I→oJ) :
    Functor.OplaxMonoidal.η (widePosReindex W u) = 𝟙 _ := rfl
@[simp] lemma widePosReindex_μ (u:I→oJ) (A B:WideSubcategory (diagramProperty W J)) :
    Functor.LaxMonoidal.μ (widePosReindex W u) A B = 𝟙 _ := rfl
@[simp] lemma posReindex_η (u:I→oJ) :
    Functor.OplaxMonoidal.η (posReindex W u) = 𝟙 _ := rfl
@[simp] lemma posReindex_μ (u:I→oJ) (A B:PosDiagrams W J) :
    Functor.LaxMonoidal.μ (posReindex W u) A B = 𝟙 _ := rfl
@[simp] lemma eqToHom_pos_app {A B:PosDiagrams W I} (e:A=B) (i j:I) (h:i≤j) :
    (eqToHom e).hom.app i j h =
      eqToHom (congrArg (fun A:PosDiagrams W I=>((diagramInclusion W I).obj A).obj i j h) e) := by
  cases e; rfl

@[simp] lemma transpose_η_app (n:ℕ) (t:Fin (n+1)) (i j:I) (h:i≤j) :
    ((Functor.OplaxMonoidal.η (transposeDiagram (I:=I) W n)).hom.app t).hom.app i j h = 𝟙 _ := by
  have he := congrArg (fun z=> (z.hom.app t).hom.app i j h)
    (Functor.Monoidal.ε_η (transposeDiagram (I:=I) W n))
  change 𝟙 (𝟙_ C) ≫ ((Functor.OplaxMonoidal.η (transposeDiagram (I:=I) W n)).hom.app t).hom.app i j h = 𝟙 (𝟙_ C) at he
  change ((Functor.OplaxMonoidal.η (transposeDiagram (I:=I) W n)).hom.app t).hom.app i j h = 𝟙 (𝟙_ C)
  exact (Category.id_comp _).symm.trans he
@[simp] lemma transpose_obj (n:ℕ) (A:Diagram (Strings W n) I) :
    (transposeDiagram W n).obj A=transposeDiagramObj W A := rfl
@[simp] lemma transpose_map (n:ℕ) {A B:Diagram (Strings W n) I} (f:A⟶B) :
    (transposeDiagram W n).map f=transposeDiagramHom W f := rfl
@[simp] lemma diagramReindex_η (u:I→oJ) :
    Functor.OplaxMonoidal.η (Diagram.reindex (C:=C) u)=𝟙 _ := rfl
@[simp] lemma diagramReindex_μ (u:I→oJ) (A B:Diagram C J) :
    Functor.LaxMonoidal.μ (Diagram.reindex u) A B=𝟙 _ := rfl

end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
@[simp] lemma map_ε (F:C⥤D) [F.Braided] :
    Functor.LaxMonoidal.ε (map (I:=I) F)=mapεHom F := rfl
@[simp] lemma map_μ (F:C⥤D) [F.Braided] (A B:Diagram C I) :
    Functor.LaxMonoidal.μ (map F) A B=mapμHom F A B := rfl
@[simp] lemma reindex_ε (u:I→oJ) :
    Functor.LaxMonoidal.ε (reindex (C:=C) u)=𝟙 _ := rfl
@[simp] lemma reindex_μ (u:I→oJ) (A B:Diagram C J) :
    Functor.LaxMonoidal.μ (reindex u) A B=𝟙 _ := rfl
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PositionalInclusionMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
open IntervalBar IntervalBar.Diagram


variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
@[simp] lemma posInclusion_ε : Functor.LaxMonoidal.ε (posDiagramInclusion W I)=mapεHom (inclusion W) := rfl
@[simp] lemma posInclusion_μ (A B:PosDiagrams W I) :
    Functor.LaxMonoidal.μ (posDiagramInclusion W I) A B=mapμHom (inclusion W) A B := rfl
@[simp] lemma posReindex_ε (u:I→oJ) : Functor.LaxMonoidal.ε (posReindex W u)=𝟙 _ := rfl
end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarRowFiniteness
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def singleRowComparison (p:ℕ) :
    bar (C:=Diagram C (Fin (p+1))) ⟶ (power (Fin p)).obj (bar (C:=C)) :=
  barMap (eval p) ≫ singlePowerComparison (Fin p)
lemma singleRowComparison_isIso (p n:ℕ) :
    IsIso (SSet.homologyMap (singleRowComparison (C:=C) p) Z n) := by
  rw [singleRowComparison,SSet.homologyMap_comp]
  have := barMap_homology_isIso (eval (C:=C) p) n
  have := singlePowerComparison_homology_isIso (C:=C) (Fin p) n
  infer_instance
noncomputable def doubleRowComparison (p:ℕ) :
    bar₂ (C:=Diagram C (Fin (p+1))) ⟶ (power (Fin p)).obj (bar₂ (C:=C)) :=
  bar₂Map (eval p) ≫ doublePowerComparison (Fin p)
lemma doubleRowComparison_isIso (p n:ℕ) :
    IsIso (SSet.homologyMap (doubleRowComparison (C:=C) p) Z n) := by
  rw [doubleRowComparison,SSet.homologyMap_comp]
  have := bar₂Map_homology_isIso (eval (C:=C) p) n
  have := doublePowerComparison_homology_isIso (C:=C) (Fin p) n
  infer_instance
noncomputable def firstRowHomologyIso (n:ℕ) :
    ((bar (C:=Diagram C (Fin 2))).homology Z n : A) ≅ (bar (C:=C)).homology Z n := by
  haveI := singleRowComparison_isIso (C:=C) 1 n
  exact asIso (SSet.homologyMap (singleRowComparison (C:=C) 1) Z n) ≪≫
    (SSet.homologyFunctor Z n).mapIso (powerOneIso (bar (C:=C)))
noncomputable def firstDoubleRowHomologyIso (n:ℕ) :
    ((bar₂ (C:=Diagram C (Fin 2))).homology Z n : A) ≅ (bar₂ (C:=C)).homology Z n := by
  haveI := doubleRowComparison_isIso (C:=C) 1 n
  exact asIso (SSet.homologyMap (doubleRowComparison (C:=C) 1) Z n) ≪≫
    (SSet.homologyFunctor Z n).mapIso (powerOneIso (bar₂ (C:=C)))
end BarFinitePower

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace NerveComponents
open FreeChains

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
noncomputable def zeroIso : (nerve C).homology Z 0 ≅ (ModuleCat.free ℤ).obj (Skeleton C) :=
  (nerve C).homology₀Iso Z ≪≫ FreeChains.iso _ ≪≫ (ModuleCat.free ℤ).mapIso (Equiv.toIso componentEquiv)
noncomputable def vertex (x:C) : Z ⟶ (nerve C).homology Z 0 :=
  ( (nerve C).chainComplex Z).liftCycles ((nerve C).ιChainComplex (nerveEquiv.symm x)) 0 (by simp) (by simp) ≫
    ((nerve C).chainComplex Z).homologyπ 0
@[reassoc (attr:=simp)] lemma vertex_zeroIso (x:C) : vertex x ≫ (zeroIso (C:=C)).hom =
    ModuleCat.ofHom (Finsupp.lsingle (toSkeleton x)) := by
  dsimp only [vertex,zeroIso,Iso.trans_hom]
  simp only [Category.assoc]
  erw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom_assoc]
  change Sigma.ι (fun _:(nerve C).π₀=>Z) (SSet.π₀.mk (nerveEquiv.symm x)) ≫
    FreeChains.forward _ ≫ (ModuleCat.free ℤ).map (↾componentEquiv)=_
  rw [FreeChains.ι_forward_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  exact ModuleCat.free_map_apply _ _
end NerveComponents

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarComponents
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

section
open NerveComponents FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def componentSimplex {n:ℕ} (D:Diagram C (Fin (n+1))) :
    ComposableArrows (SingleObj (Skeleton C)) n where
  obj _ := SingleObj.star _
  map {i j} f := toSkeleton (D.obj i j (leOfHom f))
  map_id i := congr_toSkeleton_of_iso (D.unit i)
  map_comp {i j k} f g := by
    change toSkeleton (D.obj i k _) = toSkeleton (D.obj j k _) * toSkeleton (D.obj i j _)
    rw [mul_comm,←Skeleton.toSkeleton_tensorObj]
    exact (congr_toSkeleton_of_iso (D.cut i j k (leOfHom f) (leOfHom g))).symm
lemma componentSimplex_iso {n:ℕ} {D E:Diagram C (Fin (n+1))} (e:D≅E) :
    componentSimplex D=componentSimplex E := by
  apply ComposableArrows.ext (F:=componentSimplex D) (G:=componentSimplex E) (fun _=>rfl)
  intro i hi
  simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]
  exact congr_toSkeleton_of_iso (asIso (e.hom.app _ _ _))
noncomputable def skeletonSimplex (n:ℕ) : Skeleton (Diagram C (Fin (n+1))) →
    ComposableArrows (SingleObj (Skeleton C)) n :=
  Quotient.lift componentSimplex (by rintro D E ⟨e⟩; exact componentSimplex_iso e)
@[simp] lemma skeletonSimplex_mk {n:ℕ} (D:Diagram C (Fin (n+1))) :
    skeletonSimplex n (toSkeleton D)=componentSimplex D := rfl
end

open NerveComponents FreeChains AlgebraicTopology

end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace FilteredNerve
open FreeChains

variable (C:Type) [Category.{0} C]
lemma terminal_acyclic {D:Type} [Category.{0} D] (d:D) (hd:IsTerminal d)
    (n:ℕ) (hn:n≠0) : IsZero ((nerve D).homology Z n) := by
  let α : 𝟭 D ⟶ (Functor.const D).obj d :=
    { app x := hd.from x
      naturality x y f := hd.hom_ext _ _ }
  have h := (NerveHomotopy.ofNatTrans α).congr_homologyMap Z n
  change SSet.homologyMap (𝟙 (nerve D)) Z n = SSet.homologyMap (nerveMap ((Functor.const D).obj d)) Z n at h
  rw [SSet.homologyMap_id,CategoryTheory.nerve.const_map] at h
  erw [ConnectedProduct.const_homology_zero _ n hn] at h
  exact (IsZero.iff_id_eq_zero _).mpr h
lemma positive_acyclic [IsFiltered C] (n:ℕ) (hn:n≠0) : IsZero ((nerve C).homology Z n) := by
  let h:=isColimitOfPreserves (SSet.homologyFunctor Z n) (isColimit C)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply h.hom_ext
  intro x
  have hz : IsZero ((nerve (Over x)).homology Z n) :=
    terminal_acyclic (Over.mk (𝟙 x)) Over.mkIdTerminal n hn
  exact hz.eq_of_src _ _
end FilteredNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarComponentsFinite
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace IntervalBar.Diagram
open FreeChains SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable abbrev homologyRow (q:ℕ) : ChainComplex A ℕ :=
  AlternatingFaceMapComplex.obj (simplicial (C:=C) ⋙ nerveFunctor ⋙ SSet.homologyFunctor Z q)
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedPrimitiveFaces
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def T (r p s:Skeleton C) (h:r*p=s) : H p ⟶ H s := NerveHomology.map (translate r p s h) 1
noncomputable def R (n:ℕ) (k:Fin (n+2)) : (homologyRow (C:=C) 1).X (n+1) ⟶ (homologyRow (C:=C) 1).X n :=
  NerveHomology.map (reindex (SimplexCategory.δ k).toOrderHom) 1
noncomputable def P10 (a:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 1 := primitive ![a] 0
noncomputable def P20 (a b:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 2 := primitive ![a,b] 0
noncomputable def P21 (a b:Skeleton C) : H b ⟶ (homologyRow (C:=C) 1).X 2 := primitive ![a,b] 1
noncomputable def P30 (a b d:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 3 := primitive ![a,b,d] 0
noncomputable def P31 (a b d:Skeleton C) : H b ⟶ (homologyRow (C:=C) 1).X 3 := primitive ![a,b,d] 1
noncomputable def P32 (a b d:Skeleton C) : H d ⟶ (homologyRow (C:=C) 1).X 3 := primitive ![a,b,d] 2
noncomputable def P40 (a b d e:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 0
noncomputable def P41 (a b d e:Skeleton C) : H b ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 1
noncomputable def P42 (a b d e:Skeleton C) : H d ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 2
noncomputable def P43 (a b d e:Skeleton C) : H e ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 3
@[reassoc] lemma Pface_2_0_0 (a b:Skeleton C) :
    P20 a b ≫ R 1 0 = 0 :=
  face_2_0_0 a b
@[reassoc] lemma Pface_2_0_1 [SymmetricCategory C] (a b:Skeleton C) :
    P20 a b ≫ R 1 1 = T b a (a*b) (mul_comm _ _) ≫ P10 (a*b) :=
  face_2_0_1 a b
@[reassoc] lemma Pface_2_0_2 (a b:Skeleton C) :
    P20 a b ≫ R 1 2 = P10 a :=
  face_2_0_2 a b
@[reassoc] lemma Pface_2_1_0 (a b:Skeleton C) :
    P21 a b ≫ R 1 0 = P10 b :=
  face_2_1_0 a b
@[reassoc] lemma Pface_2_1_1 (a b:Skeleton C) :
    P21 a b ≫ R 1 1 = T a b (a*b) rfl ≫ P10 (a*b) :=
  face_2_1_1 a b
@[reassoc] lemma Pface_2_1_2 (a b:Skeleton C) :
    P21 a b ≫ R 1 2 = 0 :=
  face_2_1_2 a b
@[reassoc] lemma Pface_3_0_0 (a b d:Skeleton C) :
    P30 a b d ≫ R 2 0 = 0 :=
  face_3_0_0 a b d
@[reassoc] lemma Pface_3_0_1 [SymmetricCategory C] (a b d:Skeleton C) :
    P30 a b d ≫ R 2 1 = T b a (a*b) (mul_comm _ _) ≫ P20 (a*b) d :=
  face_3_0_1 a b d
@[reassoc] lemma Pface_3_0_2 (a b d:Skeleton C) :
    P30 a b d ≫ R 2 2 = P20 a (b*d) :=
  face_3_0_2 a b d
@[reassoc] lemma Pface_3_0_3 (a b d:Skeleton C) :
    P30 a b d ≫ R 2 3 = P20 a b :=
  face_3_0_3 a b d
@[reassoc] lemma Pface_3_1_0 (a b d:Skeleton C) :
    P31 a b d ≫ R 2 0 = P20 b d :=
  face_3_1_0 a b d
@[reassoc] lemma Pface_3_1_1 (a b d:Skeleton C) :
    P31 a b d ≫ R 2 1 = T a b (a*b) rfl ≫ P20 (a*b) d :=
  face_3_1_1 a b d
@[reassoc] lemma Pface_3_1_2 [SymmetricCategory C] (a b d:Skeleton C) :
    P31 a b d ≫ R 2 2 = T d b (b*d) (mul_comm _ _) ≫ P21 a (b*d) :=
  face_3_1_2 a b d
@[reassoc] lemma Pface_3_1_3 (a b d:Skeleton C) :
    P31 a b d ≫ R 2 3 = P21 a b :=
  face_3_1_3 a b d
@[reassoc] lemma Pface_3_2_0 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 0 = P21 b d :=
  face_3_2_0 a b d
@[reassoc] lemma Pface_3_2_1 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 1 = P21 (a*b) d :=
  face_3_2_1 a b d
@[reassoc] lemma Pface_3_2_2 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 2 = T b d (b*d) rfl ≫ P21 a (b*d) :=
  face_3_2_2 a b d
@[reassoc] lemma Pface_3_2_3 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 3 = 0 :=
  face_3_2_3 a b d
@[reassoc] lemma Pface_4_0_0 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 0 = 0 :=
  face_4_0_0 a b d e
@[reassoc] lemma Pface_4_0_1 [SymmetricCategory C] (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 1 = T b a (a*b) (mul_comm _ _) ≫ P30 (a*b) d e :=
  face_4_0_1 a b d e
@[reassoc] lemma Pface_4_0_2 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 2 = P30 a (b*d) e :=
  face_4_0_2 a b d e
@[reassoc] lemma Pface_4_0_3 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 3 = P30 a b (d*e) :=
  face_4_0_3 a b d e
@[reassoc] lemma Pface_4_0_4 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 4 = P30 a b d :=
  face_4_0_4 a b d e
@[reassoc] lemma Pface_4_1_0 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 0 = P30 b d e :=
  face_4_1_0 a b d e
@[reassoc] lemma Pface_4_1_1 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 1 = T a b (a*b) rfl ≫ P30 (a*b) d e :=
  face_4_1_1 a b d e
@[reassoc] lemma Pface_4_1_2 [SymmetricCategory C] (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 2 = T d b (b*d) (mul_comm _ _) ≫ P31 a (b*d) e :=
  face_4_1_2 a b d e
@[reassoc] lemma Pface_4_1_3 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 3 = P31 a b (d*e) :=
  face_4_1_3 a b d e
@[reassoc] lemma Pface_4_1_4 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 4 = P31 a b d :=
  face_4_1_4 a b d e
@[reassoc] lemma Pface_4_2_0 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 0 = P31 b d e :=
  face_4_2_0 a b d e
@[reassoc] lemma Pface_4_2_1 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 1 = P31 (a*b) d e :=
  face_4_2_1 a b d e
@[reassoc] lemma Pface_4_2_2 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 2 = T b d (b*d) rfl ≫ P31 a (b*d) e :=
  face_4_2_2 a b d e
@[reassoc] lemma Pface_4_2_3 [SymmetricCategory C] (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 3 = T e d (d*e) (mul_comm _ _) ≫ P32 a b (d*e) :=
  face_4_2_3 a b d e
@[reassoc] lemma Pface_4_2_4 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 4 = P32 a b d :=
  face_4_2_4 a b d e
@[reassoc] lemma Pface_4_3_0 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 0 = P32 b d e :=
  face_4_3_0 a b d e
@[reassoc] lemma Pface_4_3_1 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 1 = P32 (a*b) d e :=
  face_4_3_1 a b d e
@[reassoc] lemma Pface_4_3_2 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 2 = P32 a (b*d) e :=
  face_4_3_2 a b d e
@[reassoc] lemma Pface_4_3_3 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 3 = T d e (d*e) rfl ≫ P32 a b (d*e) :=
  face_4_3_3 a b d e
@[reassoc] lemma Pface_4_3_4 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 4 = 0 :=
  face_4_3_4 a b d e
end MarkedH1

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
@[reassoc] lemma Pd_2_0 [SymmetricCategory C] (a b:Skeleton C) :
    P20 a b ≫ (homologyRow (C:=C) 1).d 2 1 = -(T b a (a*b) (mul_comm _ _) ≫ P10 (a*b)) + (P10 a) := by
  have hd : (homologyRow (C:=C) 1).d 2 1 = (R 1 0) + -(R 1 1) + (R 1 2) := by
    calc
      _ = ∑k:Fin 3,(-1:ℤ)^k.val • R 1 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_2_0_0,Pface_2_0_1,Pface_2_0_2]
  try abel
@[reassoc] lemma Pd_2_1 (a b:Skeleton C) :
    P21 a b ≫ (homologyRow (C:=C) 1).d 2 1 = (P10 b) + -(T a b (a*b) rfl ≫ P10 (a*b)) := by
  have hd : (homologyRow (C:=C) 1).d 2 1 = (R 1 0) + -(R 1 1) + (R 1 2) := by
    calc
      _ = ∑k:Fin 3,(-1:ℤ)^k.val • R 1 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_2_1_0,Pface_2_1_1,Pface_2_1_2]
  try abel
@[reassoc] lemma Pd_3_0 [SymmetricCategory C] (a b d:Skeleton C) :
    P30 a b d ≫ (homologyRow (C:=C) 1).d 3 2 = -(T b a (a*b) (mul_comm _ _) ≫ P20 (a*b) d) + (P20 a (b*d)) + -(P20 a b) := by
  have hd : (homologyRow (C:=C) 1).d 3 2 = (R 2 0) + -(R 2 1) + (R 2 2) + -(R 2 3) := by
    calc
      _ = ∑k:Fin 4,(-1:ℤ)^k.val • R 2 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_3_0_0,Pface_3_0_1,Pface_3_0_2,Pface_3_0_3]
  try abel
@[reassoc] lemma Pd_3_1 [SymmetricCategory C] (a b d:Skeleton C) :
    P31 a b d ≫ (homologyRow (C:=C) 1).d 3 2 = (P20 b d) + -(T a b (a*b) rfl ≫ P20 (a*b) d) + (T d b (b*d) (mul_comm _ _) ≫ P21 a (b*d)) + -(P21 a b) := by
  have hd : (homologyRow (C:=C) 1).d 3 2 = (R 2 0) + -(R 2 1) + (R 2 2) + -(R 2 3) := by
    calc
      _ = ∑k:Fin 4,(-1:ℤ)^k.val • R 2 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_3_1_0,Pface_3_1_1,Pface_3_1_2,Pface_3_1_3]
  try abel
@[reassoc] lemma Pd_3_2 (a b d:Skeleton C) :
    P32 a b d ≫ (homologyRow (C:=C) 1).d 3 2 = (P21 b d) + -(P21 (a*b) d) + (T b d (b*d) rfl ≫ P21 a (b*d)) := by
  have hd : (homologyRow (C:=C) 1).d 3 2 = (R 2 0) + -(R 2 1) + (R 2 2) + -(R 2 3) := by
    calc
      _ = ∑k:Fin 4,(-1:ℤ)^k.val • R 2 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_3_2_0,Pface_3_2_1,Pface_3_2_2,Pface_3_2_3]
  try abel
@[reassoc] lemma Pd_4_0 [SymmetricCategory C] (a b d e:Skeleton C) :
    P40 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = -(T b a (a*b) (mul_comm _ _) ≫ P30 (a*b) d e) + (P30 a (b*d) e) + -(P30 a b (d*e)) + (P30 a b d) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_0_0,Pface_4_0_1,Pface_4_0_2,Pface_4_0_3,Pface_4_0_4]
  try abel
@[reassoc] lemma Pd_4_1 [SymmetricCategory C] (a b d e:Skeleton C) :
    P41 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = (P30 b d e) + -(T a b (a*b) rfl ≫ P30 (a*b) d e) + (T d b (b*d) (mul_comm _ _) ≫ P31 a (b*d) e) + -(P31 a b (d*e)) + (P31 a b d) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_1_0,Pface_4_1_1,Pface_4_1_2,Pface_4_1_3,Pface_4_1_4]
  try abel
@[reassoc] lemma Pd_4_2 [SymmetricCategory C] (a b d e:Skeleton C) :
    P42 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = (P31 b d e) + -(P31 (a*b) d e) + (T b d (b*d) rfl ≫ P31 a (b*d) e) + -(T e d (d*e) (mul_comm _ _) ≫ P32 a b (d*e)) + (P32 a b d) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_2_0,Pface_4_2_1,Pface_4_2_2,Pface_4_2_3,Pface_4_2_4]
  try abel
@[reassoc] lemma Pd_4_3 (a b d e:Skeleton C) :
    P43 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = (P32 b d e) + -(P32 (a*b) d e) + (P32 a (b*d) e) + -(T d e (d*e) rfl ≫ P32 a b (d*e)) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_3_0,Pface_4_3_1,Pface_4_3_2,Pface_4_3_3,Pface_4_3_4]
  try abel
end MarkedH1

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularTotalFiniteDifferentials
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
@[reassoc] lemma block_d01 (a b:P) :
    totalInj F ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ ((RegularCoefficient.double F).total c).d 1 0 =
      (totalInj F ⟨⟨(0,0),rfl⟩,![],b,![]⟩) + -(F.map (arrow a b) ≫ totalInj F ⟨⟨(0,0),rfl⟩,![],(a*b),![]⟩) := by
  rw [totalInj_d_ver]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 a]
  try erw [labels1_1 a]
  try erw [weight1_0 a]
  try erw [weight1_1 a]
  try erw [one_totalInj F (h:=0) (v:=0) rfl ![] b ![]]
  try abel
@[reassoc] lemma block_d10 (a b:P) :
    totalInj F ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ ((RegularCoefficient.double F).total c).d 1 0 =
      (totalInj F ⟨⟨(0,0),rfl⟩,![],a,![]⟩) + -(F.map (arrow b a) ≫ totalInj F ⟨⟨(0,0),rfl⟩,![],(b*a),![]⟩) := by
  rw [totalInj_d_hor]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 b]
  try erw [labels1_1 b]
  try erw [weight1_0 b]
  try erw [weight1_1 b]
  try erw [one_totalInj F (h:=0) (v:=0) rfl ![] a ![]]
  try abel
@[reassoc] lemma block_d02 (a b d:P) :
    totalInj F ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ ((RegularCoefficient.double F).total c).d 2 1 =
      (totalInj F ⟨⟨(0,1),rfl⟩,![b],d,![]⟩) + -(totalInj F ⟨⟨(0,1),rfl⟩,![(a*b)],d,![]⟩) + (F.map (arrow b d) ≫ totalInj F ⟨⟨(0,1),rfl⟩,![a],(b*d),![]⟩) := by
  rw [totalInj_d_ver]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels2_0 a b]
  try erw [labels2_1 a b]
  try erw [labels2_2 a b]
  try erw [weight2_0 a b]
  try erw [weight2_1 a b]
  try erw [weight2_2 a b]
  try erw [one_totalInj F (h:=0) (v:=1) rfl ![b] d ![]]
  try erw [one_totalInj F (h:=0) (v:=1) rfl ![(a*b)] d ![]]
  try abel
@[reassoc] lemma block_d11 (a b d:P) :
    totalInj F ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ ((RegularCoefficient.double F).total c).d 2 1 =
      (totalInj F ⟨⟨(0,1),rfl⟩,![a],b,![]⟩) + -(F.map (arrow d b) ≫ totalInj F ⟨⟨(0,1),rfl⟩,![a],(d*b),![]⟩) + -(totalInj F ⟨⟨(1,0),rfl⟩,![],b,![d]⟩) + (F.map (arrow a b) ≫ totalInj F ⟨⟨(1,0),rfl⟩,![],(a*b),![d]⟩) := by
  rw [totalInj_d_both]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 d]
  try erw [labels1_1 d]
  try erw [labels1_0 a]
  try erw [labels1_1 a]
  try erw [weight1_0 d]
  try erw [weight1_1 d]
  try erw [weight1_0 a]
  try erw [weight1_1 a]
  try erw [one_totalInj F (h:=0) (v:=1) rfl ![a] b ![]]
  try erw [one_totalInj F (h:=1) (v:=0) rfl ![] b ![d]]
  try abel
@[reassoc] lemma block_d20 (a b d:P) :
    totalInj F ⟨⟨(2,0),rfl⟩,![],a,![b,d]⟩ ≫ ((RegularCoefficient.double F).total c).d 2 1 =
      (totalInj F ⟨⟨(1,0),rfl⟩,![],a,![d]⟩) + -(totalInj F ⟨⟨(1,0),rfl⟩,![],a,![(b*d)]⟩) + (F.map (arrow d a) ≫ totalInj F ⟨⟨(1,0),rfl⟩,![],(d*a),![b]⟩) := by
  rw [totalInj_d_hor]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels2_0 b d]
  try erw [labels2_1 b d]
  try erw [labels2_2 b d]
  try erw [weight2_0 b d]
  try erw [weight2_1 b d]
  try erw [weight2_2 b d]
  try erw [one_totalInj F (h:=1) (v:=0) rfl ![] a ![d]]
  try erw [one_totalInj F (h:=1) (v:=0) rfl ![] a ![(b*d)]]
  try abel
@[reassoc] lemma block_d03 (a b d e:P) :
    totalInj F ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(0,2),rfl⟩,![b,d],e,![]⟩) + -(totalInj F ⟨⟨(0,2),rfl⟩,![(a*b),d],e,![]⟩) + (totalInj F ⟨⟨(0,2),rfl⟩,![a,(b*d)],e,![]⟩) + -(F.map (arrow d e) ≫ totalInj F ⟨⟨(0,2),rfl⟩,![a,b],(d*e),![]⟩) := by
  rw [totalInj_d_ver]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels3_0 a b d]
  try erw [labels3_1 a b d]
  try erw [labels3_2 a b d]
  try erw [labels3_3 a b d]
  try erw [weight3_0 a b d]
  try erw [weight3_1 a b d]
  try erw [weight3_2 a b d]
  try erw [weight3_3 a b d]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![b,d] e ![]]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![(a*b),d] e ![]]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![a,(b*d)] e ![]]
  try abel
@[reassoc] lemma block_d12 (a b d e:P) :
    totalInj F ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩) + -(F.map (arrow e d) ≫ totalInj F ⟨⟨(0,2),rfl⟩,![a,b],(e*d),![]⟩) + -(totalInj F ⟨⟨(1,1),rfl⟩,![b],d,![e]⟩) + (totalInj F ⟨⟨(1,1),rfl⟩,![(a*b)],d,![e]⟩) + -(F.map (arrow b d) ≫ totalInj F ⟨⟨(1,1),rfl⟩,![a],(b*d),![e]⟩) := by
  rw [totalInj_d_both]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 e]
  try erw [labels1_1 e]
  try erw [labels2_0 a b]
  try erw [labels2_1 a b]
  try erw [labels2_2 a b]
  try erw [weight1_0 e]
  try erw [weight1_1 e]
  try erw [weight2_0 a b]
  try erw [weight2_1 a b]
  try erw [weight2_2 a b]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![a,b] d ![]]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![b] d ![e]]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![(a*b)] d ![e]]
  try abel
@[reassoc] lemma block_d21 (a b d e:P) :
    totalInj F ⟨⟨(2,1),rfl⟩,![a],b,![d,e]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(1,1),rfl⟩,![a],b,![e]⟩) + -(totalInj F ⟨⟨(1,1),rfl⟩,![a],b,![(d*e)]⟩) + (F.map (arrow e b) ≫ totalInj F ⟨⟨(1,1),rfl⟩,![a],(e*b),![d]⟩) + (totalInj F ⟨⟨(2,0),rfl⟩,![],b,![d,e]⟩) + -(F.map (arrow a b) ≫ totalInj F ⟨⟨(2,0),rfl⟩,![],(a*b),![d,e]⟩) := by
  rw [totalInj_d_both]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels2_0 d e]
  try erw [labels2_1 d e]
  try erw [labels2_2 d e]
  try erw [labels1_0 a]
  try erw [labels1_1 a]
  try erw [weight2_0 d e]
  try erw [weight2_1 d e]
  try erw [weight2_2 d e]
  try erw [weight1_0 a]
  try erw [weight1_1 a]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![a] b ![e]]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![a] b ![(d*e)]]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] b ![d,e]]
  try abel
@[reassoc] lemma block_d30 (a b d e:P) :
    totalInj F ⟨⟨(3,0),rfl⟩,![],a,![b,d,e]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(2,0),rfl⟩,![],a,![d,e]⟩) + -(totalInj F ⟨⟨(2,0),rfl⟩,![],a,![(b*d),e]⟩) + (totalInj F ⟨⟨(2,0),rfl⟩,![],a,![b,(d*e)]⟩) + -(F.map (arrow e a) ≫ totalInj F ⟨⟨(2,0),rfl⟩,![],(e*a),![b,d]⟩) := by
  rw [totalInj_d_hor]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels3_0 b d e]
  try erw [labels3_1 b d e]
  try erw [labels3_2 b d e]
  try erw [labels3_3 b d e]
  try erw [weight3_0 b d e]
  try erw [weight3_1 b d e]
  try erw [weight3_2 b d e]
  try erw [weight3_3 b d e]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] a ![d,e]]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] a ![(b*d),e]]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] a ![b,(d*e)]]
  try abel
end RegularLabels

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedBlockDifferentials
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
@[reassoc] lemma imageP00 (a:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,0),rfl⟩,![],a,![]⟩ ≫ (gradedIso 0).hom = P10 a := image00 a
@[reassoc] lemma imageP01 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ (gradedIso 1).hom = P21 a b := image01 a b
@[reassoc] lemma imageP10 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ (gradedIso 1).hom = P20 a b := image10 a b
@[reassoc] lemma imageP02 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ (gradedIso 2).hom = P32 a b d := image02 a b d
@[reassoc] lemma imageP11 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ (gradedIso 2).hom = -P31 a b d := image11 a b d
@[reassoc] lemma imageP20 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫ (gradedIso 2).hom = -P30 a b d := image20 a b d
@[reassoc] lemma imageP03 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ (gradedIso 3).hom = P43 a b d e := image03 a b d e
@[reassoc] lemma imageP12 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ (gradedIso 3).hom = P42 a b d e := image12 a b d e
@[reassoc] lemma imageP21 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫ (gradedIso 3).hom = -P41 a b d e := image21 a b d e
@[reassoc] lemma imageP30 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫ (gradedIso 3).hom = -P40 a b d e := image30 a b d e
@[reassoc] lemma map_arrow_T (r p:Skeleton C) :
    (homologyDiagram (C:=C) 1).map (arrow r p) = T r p (r*p) rfl := rfl
end MarkedH1

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedLowHomology
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Opposite
namespace CommMonoidOpposite
open FreeChains

variable (P:Type) [CommMonoid P]
noncomputable def homologyIso (n:ℕ) :
    (nerve (SingleObj P)ᵒᵖ).homology Z n ≅ (nerve (SingleObj P)).homology Z n := by
  haveI:=NerveHomotopy.homologyMap_isIso (functor P) Z n
  exact asIso (SSet.homologyMap (nerveMap (functor P)) Z n)
end CommMonoidOpposite

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedTensorTwo
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.leftAdditive _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.ChainTensor.rightAdditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimplicialAugment.flat _root_.OAI.SimplicialAugment.homology_aug_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ReducedTensorTwo

section
open FreeChains

variable (K L:ChainComplex A ℕ) (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0))
noncomputable abbrev inc (p q n:ℕ) (h:p+q=n) : K.X p ⊗ L.X q ⟶ (K⊗L).X n :=
  ιMapBifunctor K L (curriedTensor A) c p q n h
include hK hL
lemma total_one_zero : IsZero ((K⊗L).X 1) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply total.hom_ext
  intro p q hpq
  change inc K L p q 1 hpq ≫ 𝟙 _ = inc K L p q 1 hpq ≫ 0
  have hpq':p+q=1:=hpq
  by_cases hp:p=0
  · subst p
    exact (Functor.map_isZero (tensorRight (L.X q)) hK).eq_of_src _ _
  · have hq:q=0:=by omega
    subst q
    exact (Functor.map_isZero (tensorLeft (K.X p)) hL).eq_of_src _ _
lemma d21_zero : (K⊗L).d 2 1=0 := (total_one_zero K L hK hL).eq_of_tgt _ _
noncomputable def raw : K.X 1⊗L.X 1 ⟶ (K⊗L).homology 2 :=
  inc K L 1 1 2 rfl ≫ ChainComplex.positiveπ (K⊗L) 1 (d21_zero K L hK hL)
omit hK in
lemma inc21_d : inc K L 2 1 3 rfl ≫ (K⊗L).d 3 2 =
    (K.d 2 1 ▷ L.X 1) ≫ inc K L 1 1 2 rfl := by
  change ιMapBifunctor K L (curriedTensor A) c _ _ _ _ ≫ (mapBifunctor K L (curriedTensor A) c).d 3 2 = _
  rw [mapBifunctor.d_eq,Preadditive.comp_add,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq K L (curriedTensor A) c (show c.Rel 2 1 from rfl) 1 2 rfl,
    mapBifunctor.d₂_eq K L (curriedTensor A) c 2 (show c.Rel 1 0 from rfl) 2 rfl]
  have h:L.d 1 0=0:=hL.eq_of_tgt _ _
  simp [h,ComplexShape.ε₁,ComplexShape.ε₂]
omit hL in
lemma inc12_d : inc K L 1 2 3 rfl ≫ (K⊗L).d 3 2 =
    -((K.X 1 ◁ L.d 2 1) ≫ inc K L 1 1 2 rfl) := by
  change ιMapBifunctor K L (curriedTensor A) c _ _ _ _ ≫ (mapBifunctor K L (curriedTensor A) c).d 3 2 = _
  rw [mapBifunctor.d_eq,Preadditive.comp_add,mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq K L (curriedTensor A) c (show c.Rel 1 0 from rfl) 2 2 rfl,
    mapBifunctor.d₂_eq K L (curriedTensor A) c 1 (show c.Rel 2 1 from rfl) 2 rfl]
  have h:K.d 1 0=0:=hK.eq_of_tgt _ _
  simp [h,ComplexShape.ε₁,ComplexShape.ε₂]
lemma d_left_raw : (K.d 2 1 ▷ L.X 1) ≫ raw K L hK hL=0 := by
  rw [raw,←Category.assoc,←inc21_d K L hL,Category.assoc,ChainComplex.d_positiveπ,comp_zero]
lemma d_right_raw : (K.X 1 ◁ L.d 2 1) ≫ raw K L hK hL=0 := by
  have h:=congrArg (fun f=>f≫ChainComplex.positiveπ (K⊗L) 1 (d21_zero K L hK hL)) (inc12_d K L hK)
  simpa only [raw,Category.assoc,ChainComplex.d_positiveπ,comp_zero,Preadditive.neg_comp,neg_eq_zero] using h.symm
end

open FreeChains

variable (K L:ChainComplex A ℕ) (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0))
noncomputable abbrev πK := ChainComplex.positiveπ K 0 (hK.eq_of_tgt (K.d 1 0) 0)
noncomputable abbrev πL := ChainComplex.positiveπ L 0 (hL.eq_of_tgt (L.d 1 0) 0)
noncomputable def leftColimit := isColimitCoforkMapOfIsColimit' (tensorRight (L.X 1))
  (ChainComplex.d_positiveπ K 0 (hK.eq_of_tgt (K.d 1 0) 0))
  (ChainComplex.positiveIsCokernel K 0 (hK.eq_of_tgt (K.d 1 0) 0))
noncomputable def leftDesc : K.homology 1⊗L.X 1 ⟶ (K⊗L).homology 2 :=
  (leftColimit K L hK).desc (CokernelCofork.ofπ (raw K L hK hL) (d_left_raw K L hK hL))
@[reassoc] lemma π_leftDesc : (πK K hK ▷ L.X 1) ≫ leftDesc K L hK hL=raw K L hK hL :=
  (leftColimit K L hK).fac _ WalkingParallelPair.one
lemma d_leftDesc : (K.homology 1 ◁ L.d 2 1) ≫ leftDesc K L hK hL=0 := by
  have : Epi (πK K hK ▷ L.X 2) := Cofork.IsColimit.epi
    (isColimitCoforkMapOfIsColimit' (tensorRight (L.X 2))
      (ChainComplex.d_positiveπ K 0 (hK.eq_of_tgt (K.d 1 0) 0))
      (ChainComplex.positiveIsCokernel K 0 (hK.eq_of_tgt (K.d 1 0) 0)))
  apply (cancel_epi (πK K hK ▷ L.X 2)).mp
  rw [comp_zero,←Category.assoc,←MonoidalCategory.whisker_exchange,Category.assoc,π_leftDesc,d_right_raw]
noncomputable def rightColimit := isColimitCoforkMapOfIsColimit' (tensorLeft (K.homology 1))
  (ChainComplex.d_positiveπ L 0 (hL.eq_of_tgt (L.d 1 0) 0))
  (ChainComplex.positiveIsCokernel L 0 (hL.eq_of_tgt (L.d 1 0) 0))
noncomputable def generator : K.homology 1⊗L.homology 1 ⟶ (K⊗L).homology 2 :=
  (rightColimit K L hL).desc (CokernelCofork.ofπ (leftDesc K L hK hL) (d_leftDesc K L hK hL))
@[reassoc] lemma π_generator : (πK K hK ⊗ₘ πL L hL) ≫ generator K L hK hL=raw K L hK hL := by
  rw [MonoidalCategory.tensorHom_def,Category.assoc]
  have h : (K.homology 1 ◁ πL L hL) ≫ generator K L hK hL=leftDesc K L hK hL :=
    (rightColimit K L hL).fac _ WalkingParallelPair.one
  rw [h,π_leftDesc]
end ReducedTensorTwo

end

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex HomologicalComplex₂
namespace ReducedTensorTwo
open FreeChains

variable {K L K' L':ChainComplex A ℕ} (f:K⟶K') (g:L⟶L')
variable (hK:IsZero (K.X 0)) (hL:IsZero (L.X 0)) (hK':IsZero (K'.X 0)) (hL':IsZero (L'.X 0))
@[reassoc] lemma inc_natural (p q n:ℕ) (h:p+q=n) :
    inc K L p q n h ≫ (f⊗ₘg).f n=(f.f p ⊗ₘg.f q) ≫ inc K' L' p q n h := by
  change ιMapBifunctor K L (curriedTensor A) c p q n h ≫
    (mapBifunctorMap f g (curriedTensor A) c).f n=_
  rw [ι_mapBifunctorMap]
  change (f.f p ▷ L.X q) ≫ (K'.X p ◁ g.f q) ≫ _ = _
  rw [←Category.assoc,←MonoidalCategory.tensorHom_def]
@[reassoc] lemma raw_natural : raw K L hK hL ≫ homologyMap (f⊗ₘg) 2=
    (f.f 1⊗ₘg.f 1) ≫ raw K' L' hK' hL' := by
  rw [raw,Category.assoc,ChainComplex.positiveπ_natural,←Category.assoc,inc_natural,Category.assoc]
  rfl
end ReducedTensorTwo

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ReducedNatural
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.connected_one _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConstantSplit
open FreeChains ProductChains

variable {X Y:SSet}
@[reassoc] lemma aug_natural (f:X⟶Y) : chainMap f ≫ aug Y=aug X := by
  rw [aug,←chainMap_comp]
  congr 1
noncomputable def redMap (f:X⟶Y) : (sc X).X₁ ⟶ (sc Y).X₁ :=
  kernel.map (aug X) (aug Y) (chainMap f) (𝟙 _) (by simp [aug_natural])
@[reassoc (attr:=simp)] lemma redMap_inclusion (f:X⟶Y) : redMap f ≫ (sc Y).f=(sc X).f ≫ chainMap f :=
  kernel.lift_ι _ _ _
lemma one_positive (n:ℕ) (hn:n≠0) : IsZero ((complex one).homology n) := by
  exact IsZero.of_iso (ConnectedProduct.one_homology_zero n hn)
    ((homologyFunctor A c n).mapIso (complexIso one)).symm
noncomputable def inclusionIso (X:SSet) (x:X.obj (op ⦋0⦌)) (n:ℕ) (hn:n≠0) :
    ((sc X).X₁).homology n ≅ (complex X).homology n where
  hom := homologyMap (sc X).f n
  inv := homologyMap (splitting X x).r n
  hom_inv_id := by erw [←homologyMap_comp,(splitting X x).f_r,homologyMap_id]
  inv_hom_id := by
    have h:=congrArg (fun f=>homologyMap f n) (splitting X x).id
    rw [homologyMap_add,homologyMap_comp,homologyMap_comp,homologyMap_id] at h
    have hz : homologyMap (sc X).g n=0 := (one_positive n hn).eq_of_tgt _ _
    rw [hz,zero_comp,add_zero] at h
    exact h
end ConstantSplit

end

section
open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite
namespace ConnectedProduct
open FreeChains ProductChains ConstantSplit

variable (X Y:SSet) [X.IsConnected] [Y.IsConnected]
noncomputable def redInclusion (n:ℕ) :
    (((sc X).X₁)⊗((sc Y).X₁)).homology n ⟶ ((X⊗Y).homology Z n : A) :=
  homologyMap ((sc X).f⊗ₘ(sc Y).f) n ≫ (homologyIsoN X Y n).inv
@[reassoc (attr:=simp)] lemma redInclusion_redProjection (n:ℕ) :
    redInclusion X Y n ≫ redProjection X Y n=𝟙 _ := by
  simp only [redInclusion,redProjection,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id_assoc]
  erw [←homologyMap_comp,tensorHom_comp_tensorHom,(splitting X (point X)).f_r,
    (splitting Y (point Y)).f_r,id_tensorHom_id,homologyMap_id]
omit [X.IsConnected] [Y.IsConnected] in
@[reassoc] lemma redInclusion_fst (n:ℕ) :
    redInclusion X Y n ≫ SSet.homologyMap (CartesianMonoidalCategory.fst X Y) Z n=0 := by
  let f:=SSet.const (X:=Y) (Y:=one) PUnit.unit
  have h:=(homology_natural (𝟙 X) f n)
  have he : (𝟙 X)⊗ₘf=CartesianMonoidalCategory.fst X Y ≫ pairLeft X one PUnit.unit := by ext d z <;> rfl
  rw [he,SSet.homologyMap_comp,chainMap_id] at h
  have ht : ((sc X).f⊗ₘ(sc Y).f) ≫ (𝟙 (complex X)⊗ₘchainMap f)=0 := by
    change ((sc X).f⊗ₘ(sc Y).f) ≫ (𝟙 (sc X).X₂⊗ₘ(sc Y).g)=0
    rw [tensorHom_comp_tensorHom,Category.comp_id]
    rw [(sc Y).zero]; simp
  have hh:=congrArg (fun k=>redInclusion X Y n≫k) h
  simp only [redInclusion,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id_assoc] at hh
  erw [←homologyMap_comp,ht,homologyMap_zero] at hh
  have : Mono (SSet.homologyMap (pairLeft X one PUnit.unit) Z n) := by
    have he : pairLeft X one PUnit.unit ≫ CartesianMonoidalCategory.fst X one=𝟙 X := by ext d z; rfl
    exact (SplitMono.mk _ (by rw [←SSet.homologyMap_comp,he,SSet.homologyMap_id])).mono
  have : Mono (SSet.homologyMap (pairLeft X one PUnit.unit) Z n ≫ (homologyIsoN X one n).hom) := inferInstance
  apply (cancel_mono (SSet.homologyMap (pairLeft X one PUnit.unit) Z n ≫ (homologyIsoN X one n).hom)).mp
  erw [zero_comp]
  simp only [redInclusion,ConstantSplit.sc,Category.assoc]
  exact hh
omit [X.IsConnected] [Y.IsConnected] in
@[reassoc] lemma redInclusion_snd (n:ℕ) :
    redInclusion X Y n ≫ SSet.homologyMap (CartesianMonoidalCategory.snd X Y) Z n=0 := by
  let f:=SSet.const (X:=X) (Y:=one) PUnit.unit
  have h:=(homology_natural f (𝟙 Y) n)
  have he : f⊗ₘ(𝟙 Y)=CartesianMonoidalCategory.snd X Y ≫ pairRight one Y PUnit.unit := by ext d z <;> rfl
  rw [he,SSet.homologyMap_comp,chainMap_id] at h
  have ht : ((sc X).f⊗ₘ(sc Y).f) ≫ (chainMap f⊗ₘ𝟙 (complex Y))=0 := by
    change ((sc X).f⊗ₘ(sc Y).f) ≫ ((sc X).g⊗ₘ𝟙 (sc Y).X₂)=0
    rw [tensorHom_comp_tensorHom,Category.comp_id]
    rw [(sc X).zero]; simp
  have hh:=congrArg (fun k=>redInclusion X Y n≫k) h
  simp only [redInclusion,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id_assoc] at hh
  erw [←homologyMap_comp,ht,homologyMap_zero] at hh
  have : Mono (SSet.homologyMap (pairRight one Y PUnit.unit) Z n) := by
    have he : pairRight one Y PUnit.unit ≫ CartesianMonoidalCategory.snd one Y=𝟙 Y := by ext d z; rfl
    exact (SplitMono.mk _ (by rw [←SSet.homologyMap_comp,he,SSet.homologyMap_id])).mono
  have : Mono (SSet.homologyMap (pairRight one Y PUnit.unit) Z n ≫ (homologyIsoN one Y n).hom) := inferInstance
  apply (cancel_mono (SSet.homologyMap (pairRight one Y PUnit.unit) Z n ≫ (homologyIsoN one Y n).hom)).mp
  erw [zero_comp]
  simp only [redInclusion,ConstantSplit.sc,Category.assoc]
  exact hh
omit [X.IsConnected] [Y.IsConnected] in
@[reassoc (attr:=simp)] lemma redInclusion_projection (n:ℕ) :
    redInclusion X Y n ≫ projection X Y n=0 := by
  apply biprod.hom_ext <;> simp [projection,redInclusion_fst,redInclusion_snd]
variable {X Y} {X' Y':SSet} [X'.IsConnected] [Y'.IsConnected]
omit [X.IsConnected] [Y.IsConnected] [X'.IsConnected] [Y'.IsConnected] in
@[reassoc] lemma redInclusion_natural (f:X⟶X') (g:Y⟶Y') (n:ℕ) :
    redInclusion X Y n ≫ SSet.homologyMap (f⊗ₘg) Z n =
      homologyMap (redMap f⊗ₘredMap g) n ≫ redInclusion X' Y' n := by
  apply (cancel_mono (homologyIsoN X' Y' n).hom).mp
  simp only [redInclusion,ConstantSplit.sc,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  erw [homology_natural, Iso.inv_hom_id_assoc,←homologyMap_comp,←homologyMap_comp,
    tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,redMap_inclusion,redMap_inclusion]
  rfl
end ConnectedProduct

end

end OAI
end


