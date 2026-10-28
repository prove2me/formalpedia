-- Prove2me | Definitions.Def_OAIQ65Sa018
-- name    : OAIQ65Sa018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:25:54.320345+00:00
-- url     : https://prove2.me/theorems/dab1702e-347d-4ade-b477-f92100ce6905
-- title:
--   Definitions bundle OAIQ65Sa018 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 3 definitions and 15 theorems. The definitions and types are `OAI.SimpleAmenable.PolygonPlacement.Configuration.boundary`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.faceHom`, `OAI.SimpleAmenable.oneSlopeCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`SimpleAmenable_CentralCovers_FormalLaws`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/FormalLaws.lean), [`SimpleAmenable_CentralCovers_PolygonCommutingRepresentatives`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/CentralCovers/PolygonCommutingRepresentatives.lean), [`SimpleAmenable_Homology_HomologyAdditive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/SimpleAmenable/Homology/HomologyAdditive.lean).
--
--   **Imports.** It imports the bundles `OAIQ65Sa015` and `OAIQ65Sa016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa020`, `OAIQ65Sa023` and `OAIQ65Sa024`; the statements `OAI_SimpleAmenable_InitialCoverSystem_pair_actual_law` and `OAI_SimpleAmenable_polygon_alternating_H2_finite`; the proof of `OAI.SimpleAmenable.primitive_laws_eventually`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Definitions.Def_OAIQ65Sa016

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalLaws
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
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

section OneSlopeFormalTable
noncomputable def oneSlopeCoordinates {ι : Type*} (d : Fin 2) (u : CutRing × CutRing)
    (j : ι → Fin 2) (v : ι → CutRing × CutRing) : Option ι → Fin 5 × (CutRing × CutRing)
  | none => (slopeTestIndex d,u)
  | some i => (coordinateTestIndex (j i),v i)

end OneSlopeFormalTable

end SimpleAmenable
end
end

end OAI
end

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

local instance polygonFullNormal (a m : ℕ) : (polygonAlternatingGroup a m).Normal :=
  polygonAlternatingGroup_normal a m

end PolygonCommutingRepresentatives

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_HomologyAdditive
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.empty_subsingleton _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable

namespace PolygonPlacement.Configuration
attribute [local instance 1200] Rep.hV2
variable {a m p : ℕ}

noncomputable def faceHom (a m p : ℕ) (i : Fin (p+1)) :
    column a m (p+1) ⟶ column a m p :=
  TransitiveInduction.equivariantMap (face i) (face_smul i)

noncomputable def boundary (a m p : ℕ) : column a m (p+1) ⟶ column a m p :=
  (representationIso a m (p+1)).hom ≫
    ConfigurationChains.boundaryRep (fun g v w h => (apart_smul_iff g v w).mpr h) p ≫
    (representationIso a m p).inv

lemma boundary_chain (c : Configuration a m (p+1) →₀ ℤ) :
    chainEquiv a m p ((boundary a m p).hom c) =
      ConfigurationChains.degreeBoundary (@Apart a m) p (chainEquiv a m (p+1) c) := by
  change chainEquiv a m p ((chainEquiv a m p).symm _) = _
  exact (chainEquiv a m p).apply_symm_apply _

lemma boundary_sum (a m p : ℕ) : boundary a m p =
    ∑i : Fin (p+1), ((-1:ℤ)^i.val) • faceHom a m p i := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Finsupp.lhom_ext
  intro c z
  apply (chainEquiv a m p).injective
  change (chainEquiv a m p) ((boundary a m p).hom (Finsupp.single c z)) = _
  rw [boundary_chain]
  apply Subtype.ext
  change ConfigurationChains.boundary (chainEquiv a m (p+1) (Finsupp.single c z)).val = _
  rw [chainEquiv_single_val, ConfigurationChains.boundary_single,
    ConfigurationChains.faceSum_ofFn]
  simp only [Finset.smul_sum]
  change _ = (chainEquiv a m p
    ((∑i : Fin (p+1), ((-1:ℤ)^i.val) • faceHom a m p i).hom (Finsupp.single c z))).val
  simp only [Rep.sum_hom, Rep.smul_hom, Representation.IntertwiningMap.sum_apply,
    Representation.IntertwiningMap.smul_apply, map_sum, map_smul, Submodule.coe_sum,
    Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro i hi
  change z • Finsupp.single _ ((-1:ℤ)^i.val) =
    ((-1:ℤ)^i.val) • ((chainEquiv a m p)
      ((faceHom a m p i).hom (Finsupp.single c z))).val
  dsimp only [faceHom]
  rw [TransitiveInduction.equivariantMap_single]
  rw [chainEquiv_single_val]
  simp [Finsupp.smul_single, mul_comm, face]

lemma homology_face_eq (a m p : ℕ) (hm : 3*(p+1)+1 < m) (q : ℕ)
    (i j : Fin (p+1)) :
    (groupHomology.functor ℤ (polygonFullGroup a m) q).map (faceHom a m p i) =
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (faceHom a m p j) := by
  have hm' : p+1 ≤ m := by omega
  let f : Configuration a m (p+1) :=
    ⟨fun k => PolygonPlacement.standard (Fin.castLE hm' k),fun k l hkl =>
      standard_apart (fun he => hkl (Fin.castLE_injective hm' he))⟩
  exact TransitiveInduction.map_equivariant_eq_of_centralizer (face j) (face i)
    (face_smul j) (face_smul i) f (fun h => transitive f h hm)
    (permHom f.val f.property (facePermutation j i))
    (permHom_centralizes f _) (permHom_face f j i) q

lemma boundary_two (a m : ℕ) : boundary a m 1 = faceHom a m 1 0 - faceHom a m 1 1 := by
  rw [boundary_sum, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

lemma boundary_three (a m : ℕ) : boundary a m 2 =
    faceHom a m 2 0 - faceHom a m 2 1 + faceHom a m 2 2 := by
  rw [boundary_sum, Fin.sum_univ_succ, Fin.sum_univ_two]
  norm_num
  abel

lemma homology_boundary_two_zero (a m : ℕ) (hm : 7 < m) (q : ℕ) :
    (groupHomology.functor ℤ (polygonFullGroup a m) q).map (boundary a m 1)=0 := by
  rw [boundary_two, Functor.map_sub, homology_face_eq a m 1 hm q 1 0, sub_self]

lemma homology_boundary_three (a m : ℕ) (hm : 10 < m) (q : ℕ) :
    (groupHomology.functor ℤ (polygonFullGroup a m) q).map (boundary a m 2)=
      (groupHomology.functor ℤ (polygonFullGroup a m) q).map (faceHom a m 2 0) := by
  rw [boundary_three, Functor.map_add, Functor.map_sub,
    homology_face_eq a m 2 hm q 1 0, homology_face_eq a m 2 hm q 2 0, sub_self, zero_add]

lemma boundary_square (a m p : ℕ) : boundary a m (p+1) ≫ boundary a m p=0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  apply (chainEquiv a m p).injective
  change chainEquiv a m p ((boundary a m p).hom ((boundary a m (p+1)).hom c)) =
    chainEquiv a m p 0
  rw [boundary_chain, boundary_chain, ConfigurationChains.degreeBoundary_square, map_zero]

lemma boundary_exact (a m p : ℕ) (hm : 33 ≤ m) (hp : p ≤ 2) :
    (ShortComplex.mk (boundary a m (p+1)) (boundary a m p) (boundary_square a m p)).Exact := by
  apply (ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} ℤ (polygonFullGroup a m))
    (ModuleCat.{0} ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (boundary a m p).hom x=0 at hx
  have hc : ConfigurationChains.degreeBoundary (@Apart a m) p (chainEquiv a m (p+1) x)=0 := by
    erw [← boundary_chain, hx, map_zero]
  obtain ⟨y,hy⟩ := (configuration_lowDegree_exact hm hp _).mp hc
  refine ⟨(chainEquiv a m (p+2)).symm y,?_⟩
  apply (chainEquiv a m (p+1)).injective
  change chainEquiv a m (p+1) ((boundary a m (p+1)).hom _) = _
  rw [boundary_chain, LinearEquiv.apply_symm_apply, hy]

lemma boundary_zero_eq_face (a m : ℕ) : boundary a m 0=faceHom a m 0 0 := by
  rw [boundary_sum]
  simp

lemma boundary_zero_epi (a m : ℕ) (hm : 0 < m) : Epi (boundary a m 0) := by
  rw [boundary_zero_eq_face, Rep.epi_iff_surjective]
  change Function.Surjective (Finsupp.mapDomain (face (0:Fin 1)))
  apply Finsupp.mapDomain_surjective
  intro f
  refine ⟨standardLE a m 1 (by omega),?_⟩
  apply ext
  intro i
  exact Fin.elim0 i

lemma face_H0_isIso (a m p : ℕ) (hm : 3*(p+1)+1 < m) (i : Fin (p+1)) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 0).map (faceHom a m p i)) := by
  let f := standardLE a m (p+1) (by omega : p+1 ≤ m)
  exact TransitiveInduction.isIso_map_equivariant_H0 (face i) (face_smul i) f
    (fun h => transitive f h hm) (fun h => transitive _ h (by omega))

lemma boundary_two_H0_isIso (a m : ℕ) (hm : 10 < m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 0).map (boundary a m 2)) := by
  rw [homology_boundary_three a m hm 0]
  exact face_H0_isIso a m 2 hm 0
lemma boundary_zero_H1_isIso (a m : ℕ) (hm : 33 ≤ m) :
    IsIso ((groupHomology.functor ℤ (polygonFullGroup a m) 1).map (boundary a m 0)) := by
  let boundaryEpi := boundary_zero_epi a m (by omega)
  let boundaryIso : IsIso (BoundedHomologyEdge.Hmap 0 (boundary a m 2)) :=
    boundary_two_H0_isIso a m (by omega)
  exact BoundedHomologyEdge.chain_H1_isIso (boundary a m 0) (boundary a m 1)
    (boundary a m 2) (boundary_square a m 0) (boundary_square a m 1)
    (boundary_exact a m 0 hm (by omega)) (boundary_exact a m 1 hm (by omega))
    (homology_boundary_two_zero a m (by omega) 1)

end PolygonPlacement.Configuration
end SimpleAmenable

end OAI
end


