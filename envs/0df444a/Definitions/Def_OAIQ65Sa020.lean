-- Prove2me | Definitions.Def_OAIQ65Sa020
-- name    : OAIQ65Sa020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:27:54.57051+00:00
-- url     : https://prove2.me/theorems/7ca3d240-0713-4832-bbc0-7d7b66c80c2e
-- title:
--   Definitions bundle OAIQ65Sa020 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 9 definitions and 16 theorems. The definitions and types are `OAI.SimpleAmenable.PolygonPlacement.Configuration.altBoundary`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.altFaceHom`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.alternatingOrbitHomologyIso`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.alternatingRestrict`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.alternatingStabilizerEquiv`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.standardStabilizerEquiv`, `OAI.SimpleAmenable.PolygonTracks.abelianKernelEquiv`, `OAI.SimpleAmenable.PolygonTracks.standardFiber`, `OAI.SimpleAmenable.PolygonTracks.successorStabilize`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`SimpleAmenable_CentralCovers_PolygonCommutingRepresentatives`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/PolygonCommutingRepresentatives.lean), [`SimpleAmenable_Configurations_AlternatingStability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/AlternatingStability.lean), [`SimpleAmenable_Configurations_PolygonAlternatingConfigurations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonAlternatingConfigurations.lean), [`SimpleAmenable_Configurations_PolygonComponentStable`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/PolygonComponentStable.lean), [`SimpleAmenable_Configurations_StabilizationComposition`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Configurations/StabilizationComposition.lean), [`SimpleAmenable_Homology_FullGroupStability`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/FullGroupStability.lean), [`SimpleAmenable_Homology_FullH2`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/FullH2.lean), [`SimpleAmenable_Homology_PolygonStableHomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/PolygonStableHomology.lean).
--
--   **Imports.** It imports the bundles `OAIQ65Sa017` and `OAIQ65Sa018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa021`, `OAIQ65Sa025`, `OAIQ65Sa026` and `OAIQ65Sa028`; the proof of `OAI.SimpleAmenable.PolygonTracks.finite_alternating_H2_of_full`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa017
import Definitions.Def_OAIQ65Sa018

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PolygonCommutingRepresentatives
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonCommutingRepresentatives

open Classical Set

attribute [local instance] OAI.SimpleAmenable.polygonFullNormal
theorem polygonFullGroup_quotient_commutative (a m : ℕ) (hm : 0 < m) :
    IsMulCommutative (polygonFullGroup a m ⧸ polygonAlternatingGroup a m) := by
  let q := QuotientGroup.mk' (polygonAlternatingGroup a m)
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨f,rfl⟩ := QuotientGroup.mk'_surjective (polygonAlternatingGroup a m) x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (polygonAlternatingGroup a m) y
  obtain ⟨u,v,⟨a₀,rfl⟩,⟨b₀,c,rfl⟩,hc⟩ := PolygonObject.BankEmbedding.commuting_representatives hm f g
  have ha : q a₀.val=1 := (QuotientGroup.eq_one_iff a₀.val).mpr a₀.property
  have hb : q b₀.val=1 := (QuotientGroup.eq_one_iff b₀.val).mpr b₀.property
  have hcc : q c.val=1 := (QuotientGroup.eq_one_iff c.val).mpr c.property
  have hh := hc.map q
  simpa only [map_mul,map_inv,ha,hb,hcc,one_mul,mul_one,inv_one] using hh.eq

theorem polygonFullGroup_commutator_eq (a m : ℕ) (hm : 5 ≤ m) :
    _root_.commutator (polygonFullGroup a m)=polygonAlternatingGroup a m := by
  apply le_antisymm
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (polygonFullGroup_quotient_commutative a m (by omega))
  · have hp := Subgroup.isPerfect_iff.mp (polygonAlternatingGroup_perfect a m hm)
    rw [←hp]
    exact Subgroup.commutator_mono le_top le_top

end PolygonCommutingRepresentatives

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonAlternatingConfigurations
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.empty_subsingleton _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonAlternatingConfigurations

open Classical _root_.CategoryTheory Set
namespace PolygonPlacement
variable {a m n : ℕ}

theorem alternating_disjoint_configurations (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j)))
    (hfg : ∀i j,Apart (f i) (g j)) (hm : 3*n+1 < m) :
    ∃c : polygonAlternatingGroup a m,∀i x,c.val.val (f i x)=g i x := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S n (by omega)
  have hwf (i j : Fin n) : Apart (w i) (f j) :=
    hws i (f j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hwg (i j : Fin n) : Apart (w i) (g j) :=
    hws i (g j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  obtain ⟨c,hc,_⟩ := PolygonObject.BankEmbedding.cycle_three
    (bankEmbedding f hf) (bankEmbedding g hg) (bankEmbedding w hw)
    (fun p q => (apart_iff _ _).mp (hfg p.val.1 q.val.1) p.val.2 q.val.2)
    (fun p q => (apart_iff _ _).mp (hwf q.val.1 p.val.1).symm p.val.2 q.val.2)
    (fun p q => (apart_iff _ _).mp (hwg q.val.1 p.val.1).symm p.val.2 q.val.2)
  exact ⟨c,fun i x => hc ⟨(i,x),by trivial⟩⟩

theorem alternating_configuration_transitive_sharp (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j))) (hm : 3*n+1 < m) :
    ∃c : polygonAlternatingGroup a m,∀i,c.val • f i=g i := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S n (by omega)
  have hwf (i j : Fin n) : Apart (w i) (f j) :=
    hws i (f j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hwg (i j : Fin n) : Apart (w i) (g j) :=
    hws i (g j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  obtain ⟨u,hu⟩ := alternating_disjoint_configurations f w hf hw (fun i j => (hwf j i).symm) hm
  obtain ⟨v,hv⟩ := alternating_disjoint_configurations w g hw hg hwg hm
  refine ⟨v*u,fun i => ?_⟩
  apply PolygonPlacement.ext
  intro x
  change v.val.val (u.val.val (f i x))=g i x
  rw [hu,hv]

namespace Configuration

theorem alternating_transitive {p : ℕ} (f g : Configuration a m p) (hm : 3*p+1 < m) :
    ∃c : polygonAlternatingGroup a m,c.val • f=g := by
  obtain ⟨c,hc⟩ := alternating_configuration_transitive_sharp f.val g.val f.property g.property hm
  exact ⟨c,ext hc⟩

theorem alternating_stabilizer_standard (a p n : ℕ) :
    MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)=
      (PolygonTracks.bankFixer a p n).comap (polygonAlternatingGroup a (p+n)).subtype := by
  ext c
  change c.val∈MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n) ↔
    c.val∈PolygonTracks.bankFixer a p n
  rw [stabilizer_standard]

noncomputable def alternatingOrbitHomologyIso (a p n : ℕ) (hm : 3*p+1 < p+n) (q : ℕ) :
    groupHomology (Rep.of (TransitiveInduction.permutationRep
      (G:=polygonAlternatingGroup a (p+n)) (X:=Configuration a (p+n) p))) q ≅
      groupHomology (Rep.trivial ℤ (MulAction.stabilizer (polygonAlternatingGroup a (p+n))
        (standard a p n)) ℤ) q :=
  TransitiveInduction.homologyIso (standard a p n) (fun f => alternating_transitive _ f hm) q

end Configuration
end PolygonPlacement
end PolygonAlternatingConfigurations

end SimpleAmenable

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FullGroupStability
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2

namespace PolygonPlacement.Configuration
lemma augmentation_pointMap {a m : ℕ} (f : Configuration a m 1) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype
      (TransitiveInduction.pointMap f) q ≫
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (boundary a m 0) ≫
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (emptyIso a m).hom =
    TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype q := by
  erw [← Functor.map_comp]
  erw [groupHomology.functor_map, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (emptyIso a m).hom.hom ((boundary a m 0).hom (single f z))=z
    rw [boundary_zero_eq_face]
    dsimp only [faceHom]
    rw [TransitiveInduction.equivariantMap_single, emptyIso_single]
lemma stabilizer_H1_isIso (a m : ℕ) (hm : 33 ≤ m) (f : Configuration a m 1) :
    IsIso (TrivialHomology.map (MulAction.stabilizer (polygonFullGroup a m) f).subtype 1) := by
  have first := TransitiveInduction.isIso_map_pointMap f (fun g => transitive f g (by omega)) 1
  have second := boundary_zero_H1_isIso a m hm
  have third : IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map
      (emptyIso a m).hom) := inferInstance
  rw [← augmentation_pointMap f 1]
  have composite := IsIso.comp_isIso' first (IsIso.comp_isIso' second third)
  exact composite

noncomputable def standardStabilizerEquiv (a p n : ℕ) :
    polygonFullGroup a n ≃* MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n) :=
  (PolygonTracks.stabilizerEquiv a p n).trans (MulEquiv.subgroupCongr (stabilizer_standard a p n).symm)

lemma standardStabilizerEquiv_subtype (a p n : ℕ) :
    (MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n)).subtype.comp
      (standardStabilizerEquiv a p n).toMonoidHom = PolygonTracks.stabilize a p n := rfl

lemma stabilize_H1_isIso (a n : ℕ) (hn : 32 ≤ n) :
    IsIso (TrivialHomology.map (PolygonTracks.stabilize a 1 n) 1) := by
  rw [← standardStabilizerEquiv_subtype a 1 n, TrivialHomology.map_comp]
  have := TrivialHomology.isIso_equiv (standardStabilizerEquiv a 1 n) 1
  have := stabilizer_H1_isIso a (1+n) (by omega) (standard a 1 n)
  infer_instance

end PolygonPlacement.Configuration
end SimpleAmenable

end

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StabilizationComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

namespace PolygonTracks
variable {a m n : ℕ}

lemma stabilize_add (a k l n : ℕ) : stabilize a (k+l) n =
    (castFull a (Nat.add_assoc k l n).symm).toMonoidHom.comp
      ((stabilize a k (l+n)).comp (stabilize a l n)) := by
  let h : k+(l+n)=(k+l)+n := (Nat.add_assoc k l n).symm
  apply MonoidHom.ext
  intro f
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨i,hi⟩ := (finCongr h).surjective x.1
  change (stabilize a (k+l) n f).val x =
    (castFull a h (stabilize a k (l+n) (stabilize a l n f))).val x
  have hx : x=(Fin.cast h i,x.2) := Prod.ext hi.symm rfl
  rw [hx, castFull_apply (x:=(i,x.2))]
  induction i using Fin.addCases with
  | left i =>
    have he : Fin.cast h (i.castAdd (l+n))=(i.castAdd l).castAdd n := Fin.ext rfl
    rw [he, stabilize_left (x:=((i.castAdd l),x.2)), stabilize_left (x:=(i,x.2))]
    exact Prod.ext he.symm rfl
  | right i =>
    rw [stabilize_right (x:=(i,x.2))]
    induction i using Fin.addCases with
    | left i =>
      have he : Fin.cast h ((i.castAdd n).natAdd k)=(i.natAdd k).castAdd n := Fin.ext rfl
      rw [he, stabilize_left (x:=(i.natAdd k,x.2)), stabilize_left (x:=(i,x.2))]
      exact Prod.ext he.symm rfl
    | right i =>
      have he : Fin.cast h ((i.natAdd l).natAdd k)=i.natAdd (k+l) := by
        apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd]
        omega
      rw [he, stabilize_right (x:=(i,x.2)), stabilize_right (x:=(i,x.2))]
      apply Prod.ext
      · apply Fin.ext
        simp only [Fin.val_cast,Fin.val_natAdd]
        omega
      · rfl

lemma stabilize_zero_bijective (a n : ℕ) : Function.Bijective (stabilize a 0 n) := by
  refine ⟨stabilize_injective,?_⟩
  intro f
  let g : bankFixer a 0 n := ⟨f,fun x => Fin.elim0 x.1⟩
  exact ⟨restrict g,stabilize_restrict g⟩

lemma stabilize_H1_isIso (a k n : ℕ) (hn : 32 ≤ n) :
    IsIso (TrivialHomology.map (stabilize a k n) 1) := by
  induction k with
  | zero =>
      exact TrivialHomology.isIso_equiv
        (MulEquiv.ofBijective (stabilize a 0 n) (stabilize_zero_bijective a n)) 1
  | succ k ih =>
    have he : IsIso (TrivialHomology.map (stabilize a (1+k) n) 1) := by
      rw [stabilize_add, TrivialHomology.map_comp, TrivialHomology.map_comp]
      have := TrivialHomology.isIso_equiv (castFull a (Nat.add_assoc 1 k n).symm) 1
      have := PolygonPlacement.Configuration.stabilize_H1_isIso a (k+n) (by omega)
      have := ih
      infer_instance
    rw [show k+1=1+k by omega]
    exact he

lemma stabilize_alternating_comap (a k n : ℕ) (hn : 32 ≤ n) :
    (polygonAlternatingGroup a (k+n)).comap (stabilize a k n)=polygonAlternatingGroup a n := by
  have := stabilize_H1_isIso a k n hn
  rw [← polygonFullGroup_commutator_eq a n (by omega),
    ← polygonFullGroup_commutator_eq a (k+n) (by omega)]
  exact TrivialHomology.commutator_comap_of_mono (stabilize a k n)

end PolygonTracks
end SimpleAmenable

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_AlternatingStability
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2
namespace PolygonPlacement.Configuration
variable {a m p n : ℕ}

lemma stabilizeAlternating_smul_standard (g : polygonAlternatingGroup a n) :
    PolygonTracks.stabilizeAlternating a p n g • standard a p n=standard a p n := by
  apply ext
  intro i
  apply PolygonPlacement.ext
  intro x
  exact PolygonTracks.stabilize_left g.val (i,x)

noncomputable def alternatingRestrict (a p n : ℕ) (hn : 32 ≤ n)
    (g : MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)) :
    polygonAlternatingGroup a n := by
  have hg : g.val.val∈PolygonTracks.bankFixer a p n := by
    have hh := g.property
    exact (show g.val ∈ (PolygonTracks.bankFixer a p n).comap
      (polygonAlternatingGroup a (p+n)).subtype from
        (alternating_stabilizer_standard a p n) ▸ hh)
  refine ⟨PolygonTracks.restrict ⟨g.val.val,hg⟩,?_⟩
  rw [← PolygonTracks.stabilize_alternating_comap a p n hn]
  change PolygonTracks.stabilize a p n (PolygonTracks.restrict _)∈polygonAlternatingGroup a (p+n)
  rw [PolygonTracks.stabilize_restrict]
  exact g.val.property

noncomputable def alternatingStabilizerEquiv (a p n : ℕ) (hn : 32 ≤ n) :
    polygonAlternatingGroup a n ≃*
      MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n) where
  toFun g := ⟨PolygonTracks.stabilizeAlternating a p n g,stabilizeAlternating_smul_standard g⟩
  invFun := alternatingRestrict a p n hn
  left_inv g := by
    apply Subtype.ext
    change PolygonTracks.restrict ⟨PolygonTracks.stabilize a p n g.val,_⟩=g.val
    exact PolygonTracks.restrict_stabilize g.val
  right_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    change PolygonTracks.stabilize a p n (PolygonTracks.restrict _) = g.val.val
    exact PolygonTracks.stabilize_restrict _
  map_mul' g h := Subtype.ext ((PolygonTracks.stabilizeAlternating a p n).map_mul g h)

noncomputable abbrev altFaceHom (a m p : ℕ) (i : Fin (p+1)) :
    altColumn a m (p+1) ⟶ altColumn a m p :=
  (Rep.resFunctor (polygonAlternatingGroup a m).subtype).map (faceHom a m p i)
noncomputable abbrev altBoundary (a m p : ℕ) : altColumn a m (p+1) ⟶ altColumn a m p :=
  (Rep.resFunctor (polygonAlternatingGroup a m).subtype).map (boundary a m p)

lemma altBoundary_square (a m p : ℕ) : altBoundary a m (p+1) ≫ altBoundary a m p=0 := by
  rw [← Functor.map_comp, boundary_square, Functor.map_zero]

end PolygonPlacement.Configuration
end SimpleAmenable

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FullH2
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable

attribute [local instance 1200] Rep.hV2

namespace PolygonTracks
noncomputable def abelianKernelEquiv (a m : ℕ) (hm : 5 ≤ m) :
    (Abelianization.of : polygonFullGroup a m →* Abelianization (polygonFullGroup a m)).ker ≃*
      polygonAlternatingGroup a m :=
  MulEquiv.subgroupCongr ((Abelianization.ker_of (polygonFullGroup a m)).trans (polygonFullGroup_commutator_eq a m hm))

end PolygonTracks
end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonStableHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable.PolygonTracks

attribute [local instance 1200] Rep.hV2

noncomputable def successorStabilize (a n : ℕ) :
    polygonFullGroup a n →* polygonFullGroup a (n+1) :=
  (castFull a (Nat.add_comm 1 n)).toMonoidHom.comp (stabilize a 1 n)

end SimpleAmenable.PolygonTracks

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalPropertyInverse _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonTracks
open FreeChains ComponentTranslation GroupoidComponentHomology

attribute [local instance 1200] Rep.hV2
noncomputable def standardFiber (a n:ℕ) : Fiber (componentGenerator a^n) :=
  ⟨PolygonObject.standard a n,PolygonObject.component_standard_pow n⟩
end SimpleAmenable.PolygonTracks

end

end OAI
end


