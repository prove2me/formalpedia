-- Prove2me | Definitions.Def_OAIQ65Sa017
-- name    : OAIQ65Sa017
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:23:38.179326+00:00
-- url     : https://prove2.me/theorems/46ef7082-1a8c-4928-8316-4795724ce3fa
-- title:
--   Definitions bundle OAIQ65Sa017 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 66 declarations of OpenAI's Lean: 20 definitions, 5 instances and 41 theorems. The definitions and types are `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.coefficient`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIso`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIso`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.fiber`, `OAI.SimpleAmenable.PolygonObject.Labelled.Cell.step`, `OAI.SimpleAmenable.PolygonObject.Labelled.tensorInitial`, `OAI.SimpleAmenable.PolygonObject.Labelled.tensorLadder`, `OAI.SimpleAmenable.PolygonObject.Labelled.unitLadder`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.degreeRowsCocone`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.middleRowsCocone`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineFiber`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.topRowsCocone`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.altColumn`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.altEmptyIso`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.emptyIso`, `OAI.SimpleAmenable.PolygonPlacement.bankEmbedding`, `OAI.SimpleAmenable.PolygonTracks.castAlternating`, `OAI.SimpleAmenable.PolygonTracks.castFull`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_CentralCovers_PolygonCommutingRepresentatives`, `SimpleAmenable_Configurations_AlternatingStability`, `SimpleAmenable_Configurations_CellFiber`, `SimpleAmenable_Configurations_PolygonAlternatingConfigurations`, `SimpleAmenable_Configurations_PolygonAlternatingExtension`, `SimpleAmenable_Configurations_StabilizationComposition`, `SimpleAmenable_Configurations_StageRefinement`, `SimpleAmenable_Homology_AlternatingH2`, `SimpleAmenable_Homology_FullGroupStability`, `SimpleAmenable_Homology_PointFiberHomology`, `SimpleAmenable_PolygonGeometry_PolygonBankEmbedding`, `SimpleAmenable_PolygonGeometry_PolygonPiecewiseSlots`, `SimpleAmenable_PolygonGeometry_PolygonSmallPartition`, `SimpleAmenable_Simplicial_StageCoordinateMaps`, `SimpleAmenable_Simplicial_StageRefinementMonoidal`, `SimpleAmenable_Simplicial_StageSimplicialColimit`, `SimpleAmenable_Simplicial_Supplemental`, `SimpleAmenable_Simplicial_TripleBarMaps`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa015` and `OAIQ65Sa016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa019`, `OAIQ65Sa020`, `OAIQ65Sa022`, `OAIQ65Sa023` and `OAIQ65Sa024`; the statement `OAI_SimpleAmenable_InitialCoverSystem_old_axis_bridge_control_cover_uniform`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Definitions.Def_OAIQ65Sa016

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonPiecewiseSlots
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonPiecewiseSlots

open Classical Set
namespace PolygonPiecewise
variable {a m n : ℕ}

theorem even_slots (U : PolygonObject a) (f : Fin n → U.Point → TrackPoint a m)
    (hf : Function.Injective (fun p : Fin n × U.Point => f p.1 p.2))
    (ht : ∀i, PolygonObject.HasTable
      (fun x => (⟨f i x,by trivial⟩ : (PolygonObject.whole a m).Point)))
    (σ : Equiv.Perm (Fin n)) (hσ : σ∈alternatingGroup (Fin n)) :
    ∃g : polygonAlternatingGroup a m,
      (∀i x,g.val.val (f i x)=f (σ i) x) ∧
      (∀y∉Set.range (fun p : Fin n × U.Point => f p.1 p.2),g.val.val y=y) := by
  change ∀i, ∃S : Finset (PolygonObject.Chart U.tracks m),
    (∀c∈S,c.Holds (fun x => (⟨f i x,by trivial⟩ : (PolygonObject.whole a m).Point))) ∧
      (∀x : U.Point, ∃c∈S,c.Contains (V:=PolygonObject.whole a m) x) at ht
  choose S hS hcover using ht
  let C := ∀i : Fin n,{c : PolygonObject.Chart U.tracks m // c∈S i}
  let D (r : Fin U.tracks) (c : C) : polygonAlgebra a :=
    U.cell r ⊓ Finset.univ.inf (fun i => if (c i).val.source=r then (c i).val.domain else ⊥)
  have memD (r : Fin U.tracks) (c : C) (x : GenericSquare a) :
      x∈(D r c).val ↔ x∈(U.cell r).val ∧ ∀i,(c i).val.source=r ∧ x∈(c i).val.domain.val := by
    simp only [D,BooleanSubalgebra.val_inf,PolygonArea.val_finset_inf]
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,fun i => ?_⟩
      have h := Set.mem_iInter₂.mp hc i (Finset.mem_univ i)
      split_ifs at h with hi
      · exact ⟨hi,h⟩
      · exact False.elim h
    · rintro ⟨hx,hc⟩
      exact ⟨hx,Set.mem_iInter₂.mpr (fun i _ => by simp only [(hc i).1,ite_true];exact (hc i).2)⟩
  have covD (r : Fin U.tracks) (x : GenericSquare a) (hx : x∈(U.cell r).val) :
      ∃c : C,x∈(D r c).val := by
    have hc (i : Fin n) : ∃c : {c : PolygonObject.Chart U.tracks m // c∈S i},
        c.val.source=r ∧ x∈c.val.domain.val := by
      obtain ⟨c,hc,hh⟩ := hcover i ⟨(r,x),hx⟩
      exact ⟨⟨c,hc⟩,hh.1.symm,hh.2⟩
    choose c hc using hc
    exact ⟨c,(memD r c x).mpr ⟨hx,hc⟩⟩
  have hp (r : Fin U.tracks) := Fintype.exists_disjointed_le (D r)
  choose P hP hSup hdis using hp
  have coverP (r : Fin U.tracks) (x : GenericSquare a) (hx : x∈(U.cell r).val) :
      ∃c : C,x∈(P r c).val := by
    obtain ⟨c,hc⟩ := covD r x hx
    have he := congrArg (fun Q : polygonAlgebra a => Q.val) (hSup r)
    simp only [PolygonArea.val_finset_sup,Finset.mem_univ,Set.iUnion_true] at he
    have hh : x∈⋃c,(D r c).val := Set.mem_iUnion.mpr ⟨c,hc⟩
    rw [←he] at hh
    exact Set.mem_iUnion.mp hh
  let J := Fin U.tracks × C
  let cell (j : J) := P j.1 j.2
  let member (j : J) (p : U.Point) : Prop := p.val.1=j.1 ∧ p.val.2∈(cell j).val
  have cell_sub (j : J) : (cell j).val⊆(U.cell j.1).val :=
    fun x hx => ((memD j.1 j.2 x).mp (hP j.1 j.2 hx)).1
  have member_unique (j l : J) (p : U.Point) (hj : member j p) (hl : member l p) : j=l := by
    have hr : j.1=l.1 := hj.1.symm.trans hl.1
    apply Prod.ext hr
    by_contra hc
    have h : Disjoint (P j.1 j.2) (P j.1 l.2) := hdis j.1 hc
    rw [disjoint_iff] at h
    have he := congrArg (fun Q : polygonAlgebra a => Q.val) h
    have hh : p.val.2∈(P j.1 j.2 ⊓ P j.1 l.2).val := ⟨hj.2,by simpa only [hr] using hl.2⟩
    rw [he] at hh
    exact hh
  let slots (j : J) (i : Fin n) : Fin m × (CutRing×CutRing) := ((j.2 i).val.target,(j.2 i).val.shift)
  have chart_eq (j : J) (i : Fin n) (x : (cell j).val) :
      f i ⟨(j.1,x.val),cell_sub j x.property⟩=SlotMap a m (cell j) (slots j) (i,x) := by
    have hd := (memD j.1 j.2 x.val).mp (hP j.1 j.2 x.property)
    obtain ⟨hu,he⟩ := hS i (j.2 i).val (j.2 i).property x.val (hd.2 i).2
    have hx : (⟨((j.2 i).val.source,x.val),hu⟩ : U.Point)=
        ⟨(j.1,x.val),cell_sub j x.property⟩ := Subtype.ext (Prod.ext (hd.2 i).1 rfl)
    change f i ⟨((j.2 i).val.source,x.val),hu⟩=SlotMap a m (cell j) (slots j) (i,x) at he
    rwa [hx] at he
  have slot_inj (j : J) : Function.Injective (SlotMap a m (cell j) (slots j)) := by
    rintro ⟨i,x⟩ ⟨l,y⟩ h
    rw [←chart_eq j i x,←chart_eq j l y] at h
    have hh := @hf (i,⟨(j.1,x.val),cell_sub j x.property⟩)
      (l,⟨(j.1,y.val),cell_sub j y.property⟩) h
    apply Prod.ext
    · exact congrArg (fun p : Fin n × U.Point => p.1) hh
    · exact Subtype.ext (congrArg (fun p : Fin n × U.Point => p.2.val.2) hh)
  let piece (j : J) : polygonAlternatingGroup a m :=
    ⟨slotHom (cell j) (slots j) (slot_inj j) σ,slotHom_alternating_mem _ _ _ hσ⟩
  have piece_on (j : J) (i : Fin n) (p : U.Point) :
      (piece j).val.val (f i p)=if member j p then f (σ i) p else f i p := by
    by_cases hp : member j p
    · rw [ite_eq_left hp]
      let x : (cell j).val := ⟨p.val.2,hp.2⟩
      have he : p=⟨(j.1,x.val),cell_sub j x.property⟩ := Subtype.ext (Prod.ext hp.1 rfl)
      rw [he,chart_eq j i x]
      exact (slotPerm_apply _ _ _ _ i x).trans (chart_eq j (σ i) x).symm
    · rw [ite_eq_right hp]
      apply slotPerm_apply_of_notMem
      rintro ⟨⟨l,x⟩,he⟩
      rw [←chart_eq j l x] at he
      have hh := @hf (l,⟨(j.1,x.val),cell_sub j x.property⟩) (i,p) he
      have he' : (⟨(j.1,x.val),cell_sub j x.property⟩ : U.Point)=p := congrArg Prod.snd hh
      exact hp ⟨(congrArg (fun p : U.Point => p.val.1) he').symm,
        by simpa only [←he'] using x.property⟩
  have piece_out (j : J) (y : TrackPoint a m)
      (hy : y∉Set.range (fun p : Fin n × U.Point => f p.1 p.2)) : (piece j).val.val y=y := by
    apply slotPerm_apply_of_notMem
    rintro ⟨⟨i,x⟩,he⟩
    exact hy ⟨(i,⟨(j.1,x.val),cell_sub j x.property⟩),(chart_eq j i x).trans he⟩
  have assemble (s : Finset J) : ∃g : polygonAlternatingGroup a m,
      (∀i p,g.val.val (f i p)=if ∃j∈s,member j p then f (σ i) p else f i p) ∧
      (∀y∉Set.range (fun p : Fin n × U.Point => f p.1 p.2),g.val.val y=y) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by simp,fun _ _ => rfl⟩
    | @insert j s hj ih =>
      obtain ⟨g,hg,hout⟩ := ih
      refine ⟨piece j*g,?_,?_⟩
      · intro i p
        change (piece j).val.val (g.val.val (f i p))=_
        rw [hg]
        by_cases hp : member j p
        · have hn : ¬∃l∈s,member l p := by
            rintro ⟨l,hl,hlp⟩
            exact hj ((member_unique j l p hp hlp).symm ▸ hl)
          rw [ite_eq_right hn,piece_on,ite_eq_left hp,ite_eq_left ⟨j,Finset.mem_insert_self _ _,hp⟩]
        · by_cases hs : ∃l∈s,member l p
          · rw [ite_eq_left hs,piece_on,ite_eq_right hp]
            rw [ite_eq_left (by obtain ⟨l,hl,hlp⟩ := hs;exact ⟨l,Finset.mem_insert_of_mem hl,hlp⟩)]
          · have hn : ¬∃l∈insert j s,member l p := by simpa only [Finset.mem_insert,exists_prop,
                or_and_right,exists_or,exists_eq_left] using not_or.mpr ⟨hp,hs⟩
            rw [ite_eq_right hs,piece_on,ite_eq_right hp,ite_eq_right hn]
      · intro y hy
        change (piece j).val.val (g.val.val y)=y
        rw [hout y hy,piece_out j y hy]
  obtain ⟨g,hg,hout⟩ := assemble Finset.univ
  refine ⟨g,?_,hout⟩
  intro i p
  rw [hg]
  obtain ⟨c,hc⟩ := coverP p.val.1 p.val.2 p.property
  exact ite_eq_left ⟨(p.val.1,c),Finset.mem_univ _,rfl,hc⟩

end PolygonPiecewise
end PolygonPiecewiseSlots

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonBankEmbedding
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonBankEmbedding

open Classical Set
namespace PolygonObject

namespace BankEmbedding
variable {a m : ℕ} {U : PolygonObject a}

theorem imageBank_area_le (f : BankEmbedding U m) :
    (∑i,PolygonArea.area (imageBank f i))≤∑r,PolygonArea.area (U.cell r) := by
  obtain ⟨S,hS,hcov⟩ := f.table
  change Finset (Chart (a:=a) U.tracks m) at S
  let D (r : Fin U.tracks) (c : S) : polygonAlgebra a :=
    if c.val.source=r then c.val.domain else ⊥
  have hD (r : Fin U.tracks) (c : S) (x : GenericSquare a) :
      x∈(D r c).val ↔ c.val.source=r ∧ x∈c.val.domain.val := by
    by_cases h : c.val.source=r <;> simp [D,h]
  have hd_sub (r : Fin U.tracks) (c : S) : D r c≤U.cell r := by
    intro x hx
    obtain ⟨hr,hx⟩ := (hD r c x).mp hx
    have hu := (hS c.val c.property x hx).1
    simpa only [hr] using hu
  have hd_cover (r : Fin U.tracks) (x : GenericSquare a) (hx : x∈(U.cell r).val) :
      ∃c : S,x∈(D r c).val := by
    obtain ⟨c,hc,hr,hd⟩ := hcov ⟨(r,x),hx⟩
    exact ⟨⟨c,hc⟩,(hD r ⟨c,hc⟩ x).mpr ⟨hr.symm,hd⟩⟩
  have ex (r : Fin U.tracks) := Fintype.exists_disjointed_le (D r)
  choose P hP hSup hdisP using ex
  have hcoverP (r : Fin U.tracks) : (U.cell r).val=⋃c,(P r c).val := by
    have hv := congrArg (fun A : polygonAlgebra a => A.val) (hSup r)
    simp only [PolygonArea.val_finset_sup,Finset.mem_univ,Set.iUnion_true] at hv
    rw [hv]
    ext x
    exact ⟨fun hx => Set.mem_iUnion.mpr (hd_cover r x hx),fun hx =>
      by obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx;exact hd_sub r c hc⟩
  have hsumP (r : Fin U.tracks) : (∑c,PolygonArea.area (P r c))=PolygonArea.area (U.cell r) := by
    symm
    apply PolygonArea.area_eq_sum _ (P r) (hcoverP r)
    intro c d hcd
    have h : Disjoint (P r c) (P r d) := hdisP r hcd
    rw [disjoint_iff] at h
    exact Set.disjoint_iff_inter_eq_empty.mpr (congrArg (fun A : polygonAlgebra a => A.val) h)
  let Q (i : Fin m) (r : Fin U.tracks) (c : S) : polygonAlgebra a :=
    if c.val.target=i then translatedPolygon c.val.shift (P r c) else ⊥
  have hbank (i : Fin m) : imageBank f i≤Finset.univ.sup (fun r => Finset.univ.sup (Q i r)) := by
    intro y hy
    obtain ⟨p,hpy⟩ := hy
    have hx : p.val.2∈⋃c,(P p.val.1 c).val := by rw [←hcoverP];exact p.property
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hr,hd⟩ := (hD p.val.1 c p.val.2).mp (hP p.val.1 c hc)
    obtain ⟨hu,he⟩ := hS c.val c.property p.val.2 hd
    have he' : (⟨(c.val.source,p.val.2),hu⟩ : U.Point)=p := Subtype.ext (Prod.ext hr rfl)
    change f ⟨(c.val.source,p.val.2),hu⟩=(c.val.target,translate a c.val.shift p.val.2) at he
    rw [he',hpy] at he
    simp only [PolygonArea.val_finset_sup]
    refine Set.mem_iUnion₂.mpr ⟨p.val.1,Finset.mem_univ _,Set.mem_iUnion₂.mpr ⟨c,Finset.mem_univ _,?_⟩⟩
    have ht : c.val.target=i := (congrArg Prod.fst he).symm
    simp only [Q,ht,ite_true]
    exact ⟨p.val.2,hc,(congrArg Prod.snd he).symm⟩
  calc
    (∑i,PolygonArea.area (imageBank f i)) ≤ ∑i,∑r,∑c,PolygonArea.area (Q i r c) := by
      apply Finset.sum_le_sum
      intro i _
      exact (PolygonArea.area_mono (hbank i)).trans ((PolygonArea.area_finset_sup_le _ _).trans
        (Finset.sum_le_sum (fun r _ => PolygonArea.area_finset_sup_le _ _)))
    _ = ∑r,∑c,PolygonArea.area (P r c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      simp [Q,apply_ite,PolygonArea.area_bot,PolygonArea.area_translation]
    _ = ∑r,PolygonArea.area (U.cell r) := Finset.sum_congr rfl (fun r _ => hsumP r)

end BankEmbedding
end PolygonObject
end PolygonBankEmbedding

section PolygonBankReserve

open Classical Set
namespace PolygonObject
namespace BankEmbedding
variable {a m b : ℕ}

theorem exists_away (U B : Fin m → polygonAlgebra a)
    (f : Fin b → BankEmbedding (PolygonObject.mk m U) m)
    (h : (∑i,PolygonArea.area (B i))+(b+1:ENNReal)*(∑i,PolygonArea.area (U i)) < m) :
    ∃g : BankEmbedding (PolygonObject.mk m U) m,
      (∀p,(g p).2∉(B (g p).1).val) ∧ ∀j p q,g p≠f j q := by
  let D (i : Fin m) : polygonAlgebra a :=
    B i ⊔ Finset.univ.sup (fun j => imageBank (f j) i)
  let V (i : Fin m) : polygonAlgebra a := (D i)ᶜ
  have hD : (∑i,PolygonArea.area (D i))≤
      (∑i,PolygonArea.area (B i))+(b:ENNReal)*(∑i,PolygonArea.area (U i)) := by
    calc
      _≤∑i,(PolygonArea.area (B i)+∑j,PolygonArea.area (imageBank (f j) i)) := by
        apply Finset.sum_le_sum
        intro i _
        exact (PolygonArea.area_sup_le _ _).trans (add_le_add le_rfl (PolygonArea.area_finset_sup_le _ _))
      _=(∑i,PolygonArea.area (B i))+∑j,∑i,PolygonArea.area (imageBank (f j) i) := by
        rw [Finset.sum_add_distrib,Finset.sum_comm]
      _≤(∑i,PolygonArea.area (B i))+∑_j : Fin b,∑i,PolygonArea.area (U i) :=
        add_le_add le_rfl (Finset.sum_le_sum (fun j _ => imageBank_area_le (f j)))
      _=_ := by simp
  have hDV : (∑i,PolygonArea.area (D i))+(∑i,PolygonArea.area (V i))=m := by
    rw [←Finset.sum_add_distrib]
    simp only [V,PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hV : (∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (V i) := by
    by_contra hn
    have hh := (add_le_add hD (le_of_not_gt hn))
    rw [hDV] at hh
    have he : (∑i,PolygonArea.area (B i))+(b:ENNReal)*(∑i,PolygonArea.area (U i))+
        (∑i,PolygonArea.area (U i)) =
        (∑i,PolygonArea.area (B i))+(b+1:ENNReal)*(∑i,PolygonArea.area (U i)) := by
      rw [add_mul,one_mul,add_assoc]
    rw [he] at hh
    exact (not_le_of_gt h) hh
  obtain ⟨g,hg⟩ := exists_into hV
  refine ⟨g,?_,?_⟩
  · intro p hB
    exact hg p (Or.inl hB)
  · intro j p q he
    apply hg p
    right
    rw [PolygonArea.val_finset_sup]
    refine Set.mem_iUnion₂.mpr ⟨j,Finset.mem_univ _,?_⟩
    exact ⟨q,he.symm⟩

theorem cycle_three {U : PolygonObject a} (f g h : BankEmbedding U m)
    (hfg : ∀p q,f p≠g q) (hfh : ∀p q,f p≠h q) (hgh : ∀p q,g p≠h q) :
    ∃ c : polygonAlternatingGroup a m,
      (∀p,c.val.val (f p)=g p) ∧
      (∀y,(∀p,f p≠y) → (∀p,g p≠y) → (∀p,h p≠y) → c.val.val y=y) := by
  let slots : Fin 3 → BankEmbedding U m := ![f,g,h]
  have hinj : Function.Injective (fun p : Fin 3 × U.Point => slots p.1 p.2) := by
    rintro ⟨i,p⟩ ⟨j,q⟩ he
    have hij : i=j := by
      fin_cases i <;> fin_cases j <;> simp only [slots] at he ⊢
      · exact False.elim (hfg p q he)
      · exact False.elim (hfh p q he)
      · exact False.elim (hfg q p he.symm)
      · exact False.elim (hgh p q he)
      · exact False.elim (hfh q p he.symm)
      · exact False.elim (hgh q p he.symm)
    subst j
    exact Prod.ext rfl ((slots i).injective he)
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hσ : σ∈alternatingGroup (Fin 3) := by
    simp [σ,Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_mul]
  obtain ⟨c,hc,hout⟩ := PolygonPiecewise.even_slots U (fun i => slots i) hinj (fun i => (slots i).table) σ hσ
  refine ⟨c,?_,?_⟩
  · intro p
    have hz : σ 0=1 := by decide
    have hu := hc 0 p
    rw [hz] at hu
    exact hu
  · intro y hyf hyg hyh
    apply hout y
    rintro ⟨⟨i,p⟩,he⟩
    fin_cases i
    · exact hyf p he
    · exact hyg p he
    · exact hyh p he

end BankEmbedding
end PolygonObject
end PolygonBankReserve

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonAlternatingExtension
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonAlternatingExtension

open Classical Set
namespace PolygonObject
namespace BankEmbedding
variable {a m : ℕ}

theorem alternating_extension (U B : Fin m → polygonAlgebra a)
    (f : BankEmbedding (PolygonObject.mk m U) m)
    (hU : ∀p : (PolygonObject.mk m U).Point,p.val.2∉(B p.val.1).val)
    (hf : ∀p,(f p).2∉(B (f p).1).val)
    (harea : 10*(∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (B i)ᶜ) :
    ∃c : polygonAlternatingGroup a m,
      (∀p,c.val.val p.val=f p) ∧
      (∀y : TrackPoint a m,y.2∈(B y.1).val → c.val.val y=y) := by
  let u := inclusion U
  have hB : (∑i,PolygonArea.area (B i))≤(m:ENNReal) := by
    calc
      _≤∑_i : Fin m,(1:ENNReal) := Finset.sum_le_sum (fun i _ => PolygonArea.area_le_one (B i))
      _=_ := by simp
  have hBn : (∑i,PolygonArea.area (B i))≠⊤ := ne_top_of_le_ne_top (by simp) hB
  have htotal : (∑i,PolygonArea.area (B i))+(∑i,PolygonArea.area (B i)ᶜ)=m := by
    rw [←Finset.sum_add_distrib]
    simp only [PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have guard (r : ENNReal) (hr : r≤10) :
      (∑i,PolygonArea.area (B i))+r*(∑i,PolygonArea.area (U i)) < m := by
    rw [←htotal]
    exact ENNReal.add_lt_add_left hBn ((mul_le_mul hr le_rfl (by positivity) (by positivity)).trans_lt harea)
  obtain ⟨w₁,hw₁B,hw₁⟩ := exists_away U B ![u,f] (by apply guard; norm_num)
  obtain ⟨w₂,hw₂B,hw₂⟩ := exists_away U B ![u,f,w₁] (by apply guard; norm_num)
  obtain ⟨w₃,hw₃B,hw₃⟩ := exists_away U B ![u,f,w₁,w₂] (by apply guard; norm_num)
  obtain ⟨c₁,hc₁,hout₁⟩ := cycle_three u w₁ w₂
    (fun p q he => hw₁ 0 q p he.symm)
    (fun p q he => hw₂ 0 q p he.symm)
    (fun p q he => hw₂ 2 q p he.symm)
  obtain ⟨c₂,hc₂,hout₂⟩ := cycle_three w₁ f w₃
    (fun p q he => hw₁ 1 p q he)
    (fun p q he => hw₃ 2 q p he.symm)
    (fun p q he => hw₃ 1 q p he.symm)
  refine ⟨c₂*c₁,?_,?_⟩
  · intro p
    change c₂.val.val (c₁.val.val (u p))=f p
    rw [hc₁,hc₂]
  · intro y hy
    have avoid (e : BankEmbedding (PolygonObject.mk m U) m)
        (he : ∀p,(e p).2∉(B (e p).1).val) : ∀p,e p≠y := by
      intro p hp
      exact he p (by simpa only [hp] using hy)
    have hu : ∀p,u p≠y := avoid u hU
    have hf' : ∀p,f p≠y := avoid f hf
    have hw₁' := avoid w₁ hw₁B
    have hw₂' := avoid w₂ hw₂B
    have hw₃' := avoid w₃ hw₃B
    change c₂.val.val (c₁.val.val y)=y
    rw [hout₁ y hu hw₁' hw₂',hout₂ y hw₁' hf' hw₃']

end BankEmbedding
end PolygonObject
end PolygonAlternatingExtension

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonSmallPartition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonSmallSupport

open Classical Set
namespace PolygonObject.BankEmbedding
variable {a m : ℕ}

theorem small_support_coset (f : polygonFullGroup a m) {δ : ℝ} (hδ : 0<δ) :
    ∃a₀ : polygonAlternatingGroup a m,∃S : Fin m → polygonAlgebra a,
      (∑i,PolygonArea.area (S i))<ENNReal.ofReal δ ∧
      ∀y : TrackPoint a m,y.2∉(S y.1).val → (a₀.val*f).val y=y := by
  obtain ⟨N,P,hcover,hsmall⟩ := PolygonGrid.small_bank_cover (a:=a) (m:=m) (show 0<δ/20 by positivity)
  have hnum : (10:ENNReal)*ENNReal.ofReal (δ/20)<ENNReal.ofReal δ := by
    rw [←ENNReal.ofReal_ofNat 10,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10)]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr (by linarith)
  have step (s : Finset (Fin m × Fin N)) :
      ∃a₀ : polygonAlternatingGroup a m,∃B : Fin m → polygonAlgebra a,
        (∀y : TrackPoint a m,y.2∈(B y.1).val → (a₀.val*f).val y=y) ∧
        ((∑i,PolygonArea.area (B i)ᶜ)<ENNReal.ofReal δ ∨ B=fun i => s.sup (fun j => P j i)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,fun _ => ⊥,fun _ hp => False.elim hp,Or.inr (by simp)⟩
    | @insert j s hj ih =>
      obtain ⟨a₀,B,hfix,hB⟩ := ih
      by_cases hsmallB : (∑i,PolygonArea.area (B i)ᶜ)<ENNReal.ofReal δ
      · exact ⟨a₀,B,hfix,Or.inl hsmallB⟩
      · have hBeq := hB.resolve_left hsmallB
        let U (i : Fin m) : polygonAlgebra a := P j i ⊓ (B i)ᶜ
        let g : polygonFullGroup a m := a₀.val*f
        have hU : ∀p : (PolygonObject.mk m U).Point,p.val.2∉(B p.val.1).val :=
          fun p => p.property.2
        have hg : ∀p : (PolygonObject.mk m U).Point,
            (g.val p.val).2∉(B (g.val p.val).1).val := by
          intro p hp
          have he : g.val (g.val p.val)=g.val p.val := hfix (g.val p.val) hp
          have hh : g.val p.val=p.val := g.val.injective he
          exact hU p (by simpa only [hh] using hp)
        have harea : 10*(∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (B i)ᶜ := by
          have hle : (∑i,PolygonArea.area (U i))≤ENNReal.ofReal (δ/20) :=
            (Finset.sum_le_sum (fun i _ => PolygonArea.area_mono inf_le_left)).trans (hsmall j).le
          exact ((mul_le_mul le_rfl hle (by positivity) (by positivity)).trans_lt hnum).trans_le
            (le_of_not_gt hsmallB)
        obtain ⟨c,hc,hcB⟩ := alternating_extension U B (full_restrict g U) hU hg harea
        let B' (i : Fin m) : polygonAlgebra a := P j i ⊔ B i
        refine ⟨c⁻¹*a₀,B',?_,Or.inr ?_⟩
        · intro y hy
          change c.val.val.symm (g.val y)=y
          apply (c.val.val.symm_apply_eq).mpr
          by_cases hyB : y.2∈(B y.1).val
          · rw [show g.val y=y from hfix y hyB,hcB y hyB]
          · have hyP : y.2∈(P j y.1).val := hy.resolve_right hyB
            let p : (PolygonObject.mk m U).Point := ⟨y,hyP,hyB⟩
            exact (hc p).symm
        · funext i
          simp only [B',hBeq,Finset.sup_insert]
  obtain ⟨a₀,B,hfix,hB⟩ := step Finset.univ
  refine ⟨a₀,fun i => (B i)ᶜ,?_,?_⟩
  · rcases hB with hB|rfl
    · exact hB
    · have hall (i : Fin m) : Finset.univ.sup (fun j => P j i)=⊤ := by
        apply top_unique
        intro x _
        obtain ⟨j,hj⟩ := hcover (i,x)
        exact (Finset.le_sup (f:=fun j => P j i) (Finset.mem_univ j)) hj
      simp only [hall,compl_top,PolygonArea.area_bot,Finset.sum_const_zero]
      exact ENNReal.ofReal_pos.mpr hδ
  · intro y hy
    exact hfix y (not_not.mp hy)

end PolygonObject.BankEmbedding
end PolygonSmallSupport

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PolygonCommutingRepresentatives
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
namespace PolygonObject.BankEmbedding
variable {a m : ℕ}

theorem commuting_representatives (hm : 0 < m) (f g : polygonFullGroup a m) :
    ∃u v : polygonFullGroup a m,
      (∃a₀ : polygonAlternatingGroup a m,u=a₀.val*f) ∧
      (∃b₀ c : polygonAlternatingGroup a m,v=c.val*(b₀.val*g)*c.val⁻¹) ∧ Commute u v := by
  let δ : ℝ := (m:ℝ)/100
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨a₀,S,hS,hf⟩ := small_support_coset f hδ
  obtain ⟨b₀,T,hT,hg⟩ := small_support_coset g hδ
  have htotal : (∑i,PolygonArea.area (S i))+(∑i,PolygonArea.area (S i)ᶜ)=(m:ENNReal) := by
    rw [←Finset.sum_add_distrib]
    simp only [PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have htwo : ENNReal.ofReal δ+ENNReal.ofReal δ<(m:ENNReal) := by
    rw [←ENNReal.ofReal_add hδ.le hδ.le,←ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    dsimp [δ]
    have : (0:ℝ) < m := Nat.cast_pos.mpr hm
    linarith
  have hTS : (∑i,PolygonArea.area (T i))<∑i,PolygonArea.area (S i)ᶜ := by
    by_contra hn
    have hle := add_le_add hS.le ((le_of_not_gt hn).trans hT.le)
    rw [htotal] at hle
    exact (not_le_of_gt htwo) hle
  obtain ⟨e,he⟩ := exists_into hTS
  have hten : 10*(∑i,PolygonArea.area (T i))<∑_i : Fin m,PolygonArea.area (⊥ : polygonAlgebra a)ᶜ := by
    calc
      _≤10*ENNReal.ofReal δ := mul_le_mul le_rfl hT.le (by positivity) (by positivity)
      _<(m:ENNReal) := by
        rw [←ENNReal.ofReal_ofNat 10,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤10),←ENNReal.ofReal_natCast]
        apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
        dsimp [δ]
        have : (0:ℝ) < m := Nat.cast_pos.mpr hm
        linarith
      _=_ := by simp [PolygonArea.area_top]
  obtain ⟨c,hc,_⟩ := alternating_extension T (fun _ => ⊥) e
    (fun _ => id) (fun _ => id) hten
  let u : polygonFullGroup a m := a₀.val*f
  let v : polygonFullGroup a m := c.val*(b₀.val*g)*c.val⁻¹
  have hvfix : ∀y : TrackPoint a m,y.2∈(S y.1).val → v.val y=y := by
    intro y hy
    have hpre : (c.val.val.symm y).2∉(T (c.val.val.symm y).1).val := by
      intro hp
      let p : (PolygonObject.mk m T).Point := ⟨c.val.val.symm y,hp⟩
      have hcp : e p=y := by rw [←hc p]; exact c.val.val.apply_symm_apply y
      have hi := he p
      rw [hcp] at hi
      exact hi hy
    change c.val.val ((b₀.val*g).val (c.val.val.symm y))=y
    rw [hg _ hpre]
    exact c.val.val.apply_symm_apply y
  refine ⟨u,v,⟨a₀,rfl⟩,⟨b₀,c,rfl⟩,?_⟩
  have hh : Commute v.val u.val := supported_fixer_commute hvfix hf
  exact Subtype.ext hh.symm.eq

end PolygonObject.BankEmbedding

end PolygonCommutingRepresentatives

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonAlternatingConfigurations
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

noncomputable def bankEmbedding (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) :
    PolygonObject.BankEmbedding (PolygonObject.whole a n) m where
  emb := ⟨fun x => bank f hf x.val,fun x y h => Subtype.ext ((bank f hf).injective h)⟩
  table := by
    choose S hS hcov using fun i => (f i).charts
    let c (i : Fin n) (k : Fin m × (CutRing×CutRing) × polygonAlgebra a) :
        PolygonObject.Chart (a:=a) n m := ⟨i,k.1,k.2.1,k.2.2⟩
    refine ⟨Finset.univ.biUnion (fun i => (S i).image (c i)),?_,?_⟩
    · intro k hk
      obtain ⟨i,_,hk⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      intro z hz
      exact ⟨by trivial,hS i d hd z hz⟩
    · intro x
      obtain ⟨d,hd,hz⟩ := hcov x.val.1 x.val.2
      exact ⟨c x.val.1 d,Finset.mem_biUnion.mpr ⟨x.val.1,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨d,hd,rfl⟩⟩,rfl,hz⟩

@[simp] theorem bankEmbedding_apply (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (x : (PolygonObject.whole a n).Point) : bankEmbedding f hf x=f x.val.1 x.val.2 := rfl

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

noncomputable def emptyIso (a m : ℕ) : column a m 0 ≅ Rep.trivial ℤ (polygonFullGroup a m) ℤ :=
  Rep.mkIso (Representation.Equiv.mk (Finsupp.uniqueLinearEquiv ℤ ℤ (empty a m)) (by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    change (TransitiveInduction.permutationRep g (single x z)) (empty a m)=
      (single x z) (empty a m)
    rw [TransitiveInduction.permutationRep_single]
    congr 2
    exact Subsingleton.elim _ _))

@[simp] lemma emptyIso_single (a m : ℕ) (x : Configuration a m 0) (z : ℤ) :
    (emptyIso a m).hom.hom (single x z)=z := by
  change (single x z) (empty a m)=z
  simp [Subsingleton.elim (empty a m) x]

end PolygonPlacement.Configuration
end SimpleAmenable

end

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StabilizationComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

noncomputable def castFull (a : ℕ) {m n : ℕ} (h : m=n) :
    polygonFullGroup a m ≃* polygonFullGroup a n := h ▸ MulEquiv.refl _

@[simp] lemma castFull_apply (h : m=n) (f : polygonFullGroup a m) (x : TrackPoint a m) :
    (castFull a h f).val (Fin.cast h x.1,x.2)=
      (Fin.cast h (f.val x).1,(f.val x).2) := by subst n; rfl

end PolygonTracks
end SimpleAmenable

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_AlternatingStability
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

noncomputable abbrev altColumn (a m p : ℕ) :=
  Rep.res (polygonAlternatingGroup a m).subtype (column a m p)

end PolygonPlacement.Configuration
end SimpleAmenable

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_AlternatingH2
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
variable {a m : ℕ}

noncomputable def altEmptyIso (a m : ℕ) :
    altColumn a m 0 ≅ Rep.trivial ℤ (polygonAlternatingGroup a m) ℤ :=
  (Rep.resFunctor (polygonAlternatingGroup a m).subtype).mapIso (emptyIso a m)

@[simp] lemma altEmptyIso_single (a m : ℕ) (x : Configuration a m 0) (z : ℤ) :
    (altEmptyIso a m).hom.hom (single x z)=z := emptyIso_single a m x z
end PolygonPlacement.Configuration

namespace PolygonTracks
noncomputable def castAlternating (a : ℕ) {m n : ℕ} (h : m=n) :
    polygonAlternatingGroup a m ≃* polygonAlternatingGroup a n := h ▸ MulEquiv.refl _

@[simp] lemma castAlternating_val (a : ℕ) {m n : ℕ} (h : m=n) (g : polygonAlternatingGroup a m) :
    (castAlternating a h g).val=castFull a h g.val := by subst n; rfl

end PolygonTracks
end SimpleAmenable

end

open _root_.CategoryTheory CategoryTheory.Limits

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleBarMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject

variable {a n : ℕ}
lemma pointShift_sum_left {U V W T : PolygonObject a} (f : U ⟶ W) (g : V ⟶ T) (x : U.Point) :
    pointShift (sumArrow f g) (sumPointEquiv U V (.inl x))=pointShift f x := by
  simpa only [pointShift_reduced] using pointShift_unique (sumArrow f g) _ (pointShift f x)
    (by simpa only [sumArrow_inl,sumPointEquiv_inl] using pointShift_spec f x)
lemma pointShift_sum_right {U V W T : PolygonObject a} (f : U ⟶ W) (g : V ⟶ T) (x : V.Point) :
    pointShift (sumArrow f g) (sumPointEquiv U V (.inr x))=pointShift g x := by
  simpa only [pointShift_reduced] using pointShift_unique (sumArrow f g) _ (pointShift g x)
    (by simpa only [sumArrow_inr,sumPointEquiv_inr] using pointShift_spec g x)
lemma increments_sum_left (F G : RawString a n) (x : (F.obj 0).Point) :
    increments (F⊗G) (sumPointEquiv (F.obj 0) (G.obj 0) (.inl x))=increments F x := by
  funext i
  simp only [increments,trajectoryShift]
  change pointShift (sumArrow _ _) _ - pointShift (sumArrow _ _) _ = _
  rw [pointShift_sum_left,pointShift_sum_left]
  rfl
lemma increments_sum_right (F G : RawString a n) (x : (G.obj 0).Point) :
    increments (F⊗G) (sumPointEquiv (F.obj 0) (G.obj 0) (.inr x))=increments G x := by
  funext i
  simp only [increments,trajectoryShift]
  change pointShift (sumArrow _ _) _ - pointShift (sumArrow _ _) _ = _
  rw [pointShift_sum_right,pointShift_sum_right]
  rfl
namespace Labelled
noncomputable def tensorInitial (U V : Labelled a n) :
    ((string U ⊗ string V).obj.obj 0) ⟶ (string (U⊗V)).obj.obj 0 :=
  inv (C := PolygonObject a) (sumArrow (initial U) (initial V))
    (I := IsIso.of_groupoid (C := PolygonObject a) _) ≫ initial (U⊗V)
lemma tensorInitial_positional (U V : Labelled a n) : Positional (tensorInitial U V) :=
  positional_comp (positional_inv (sumArrow_positional (incrementInitial_positional _ _)
    (incrementInitial_positional _ _))) (incrementInitial_positional _ _)
lemma tensorInitial_labels (U V : Labelled a n) (x : ((string U ⊗ string V).obj.obj 0).Point) :
    increments (string (U⊗V)).obj ((tensorInitial U V).toEquiv x) =
      increments (string U ⊗ string V).obj x := by
  obtain ⟨y,rfl⟩ := (sumArrow (initial U) (initial V)).toEquiv.surjective x
  change increments (string (sum U V)).obj ((initial (sum U V)).toEquiv
    ((inv (C := PolygonObject a) (sumArrow (initial U) (initial V))
      (I := IsIso.of_groupoid (C := PolygonObject a) _)).toEquiv
      ((sumArrow (initial U) (initial V)).toEquiv y))) =
    increments ((string U).obj ⊗ (string V).obj) ((sumArrow (initial U) (initial V)).toEquiv y)
  rw [inv_arrow_apply,Equiv.symm_apply_apply,incrementString_spec_reduced _ _ (sum U V).reduced]
  obtain ⟨z,rfl⟩ := (sumPointEquiv U.polygon V.polygon).surjective y
  cases z with
  | inl z =>
    rw [sumArrow_inl]
    rw [increments_sum_left,incrementString_spec_reduced _ _ U.reduced]
    exact sum_label_left U V z
  | inr z =>
    rw [sumArrow_inr]
    rw [increments_sum_right,incrementString_spec_reduced _ _ V.reduced]
    exact sum_label_right U V z
noncomputable def tensorLadder (U V : Labelled a n) : string U⊗string V ⟶ string (U⊗V) :=
  ⟨extendLadder (tensorInitial U V),extendLadder_positional_of_increments _
    (tensorInitial_positional U V) (tensorInitial_labels U V)⟩
@[simp] lemma tensorLadder_zero (U V : Labelled a n) : (tensorLadder U V).hom.app 0=tensorInitial U V :=
  extendLadder_zero _
noncomputable def unitLadder : 𝟙_ (StringGroupoid a n) ⟶ string (𝟙_ (Labelled a n)) :=
  ⟨extendLadder (initial (𝟙_ _)),extendLadder_positional_of_increments _
    (incrementInitial_positional _ _) (by intro x; change PolygonObject.empty.Point at x; exact isEmptyElim x)⟩
@[simp] lemma unitLadder_zero : (unitLadder (a:=a) (n:=n)).hom.app 0=initial (𝟙_ _) := extendLadder_zero _
end Labelled
end SimpleAmenable.PolygonObject

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_CellFiber
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.Cell
open BarFinitePower

variable {a n : ℕ} (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n)
variable (c : GenericSquare a × (Fin n → CutRing × CutRing))
variable (hp : c.1∈P.val) (hl : l.val=c.2)
noncomputable def fiber (U : FiniteSetGroupoid) :
    Fin U.size ≃ PointFiber.Fiber (object P l U) c where
  toFun i := ⟨⟨(i,c.1),hp⟩,rfl,hl⟩
  invFun y := y.val.val.1
  left_inv _ := rfl
  right_inv y := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl y.property.1.symm
lemma fiber_natural {U V : FiniteSetGroupoid} (f : U ⟶ V) (x : Fin U.size) :
    fiber P l c hp hl V (f x)=
      PointFiber.fiberMap (arrow P l f) c (fiber P l c hp hl U x) := rfl
noncomputable def evaluationIso :
    𝟭 FiniteSetGroupoid ≅ functor P l ⋙ PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := U) (Y := PointFiber.E.obj (object P l U) c)
    ((fiber P l c hp hl U).trans (PointFiber.enumerate (object P l U) c))) (by
      intro U V f
      apply Equiv.ext; intro x
      change PointFiber.enumerate (object P l V) c (fiber P l c hp hl V (f x)) =
        PointFiber.E.map (arrow P l f) c (PointFiber.enumerate (object P l U) c
          (fiber P l c hp hl U x))
      rw [PointFiber.E_map_enum,fiber_natural])
lemma evaluationIso_apply (U : FiniteSetGroupoid) (x : Fin U.size) :
    (evaluationIso P l c hp hl).hom.app U x =
      PointFiber.enumerate (object P l U) c (fiber P l c hp hl U x) := rfl
lemma fiber_sum_left (U V : FiniteSetGroupoid) (x : Fin U.size) :
    PointFiber.fiberMap (tensorArrow P l U V) c
      (PointFiber.fiberSum (object P l U) (object P l V) c (.inl (fiber P l c hp hl U x))) =
      fiber P l c hp hl (U⊗V) (FiniteSetGroupoid.sumEquiv U V (.inl x)) := rfl
lemma fiber_sum_right (U V : FiniteSetGroupoid) (x : Fin V.size) :
    PointFiber.fiberMap (tensorArrow P l U V) c
      (PointFiber.fiberSum (object P l U) (object P l V) c (.inr (fiber P l c hp hl V x))) =
      fiber P l c hp hl (U⊗V) (FiniteSetGroupoid.sumEquiv U V (.inr x)) := rfl
noncomputable instance evaluationIsoMonoidal : NatTrans.IsMonoidal (evaluationIso P l c hp hl).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor U V := by
    apply Equiv.ext; intro x
    change (evaluationIso P l c hp hl).hom.app (U⊗V) x =
      PointFiber.E.map (tensorArrow P l U V) c
        (PointFiber.mu (object P l U) (object P l V) c
          (FiniteSetGroupoid.sumHom ((evaluationIso P l c hp hl).hom.app U)
            ((evaluationIso P l c hp hl).hom.app V) x))
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv U V).surjective x
    cases x with
    | inl x => erw [FiniteSetGroupoid.sumHom_inl,evaluationIso_apply,PointFiber.mu_inl,
        PointFiber.E_map_enum,fiber_sum_left,evaluationIso_apply]
    | inr x => erw [FiniteSetGroupoid.sumHom_inr,evaluationIso_apply,PointFiber.mu_inr,
        PointFiber.E_map_enum,fiber_sum_right,evaluationIso_apply]

variable {hp hl}
lemma fiber_empty (h : ¬(c.1∈P.val ∧ l.val=c.2)) (U : FiniteSetGroupoid) :
    IsEmpty (PointFiber.Fiber (object P l U) c) := ⟨fun x => h
      ⟨x.property.1 ▸ x.val.property,x.property.2⟩⟩
lemma empty_size (h : ¬(c.1∈P.val ∧ l.val=c.2)) (U : FiniteSetGroupoid) :
    (PointFiber.E.obj (object P l U) c).size=0 := by
  have := fiber_empty P l c h U
  exact @Fintype.card_eq_zero _ (PointFiber.instFintypeFiber (object P l U) c) _
noncomputable def emptyIso (h : ¬(c.1∈P.val ∧ l.val=c.2)) :
    FiniteSetGroupoid.terminal ⋙ FiniteSetGroupoid.emptyFunctor ≅
      functor P l ⋙ PointFiber.evaluation ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (X := FiniteSetGroupoid.empty)
    (Y := PointFiber.E.obj (object P l U) c) (finCongr (empty_size P l c h U).symm)) (by
      intros; apply Equiv.ext; intro x; exact Fin.elim0 x)
noncomputable instance emptyIsoMonoidal (h : ¬(c.1∈P.val ∧ l.val=c.2)) :
    NatTrans.IsMonoidal (emptyIso P l c h).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x
end SimpleAmenable.PolygonObject.Labelled.Cell

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open UniformObject BarFinitePower

variable {a n : ℕ} (S : Stage a n)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : GenericSquare a × (Fin n → CutRing × CutRing))
    (hp : S.partition.color c.1=b.1) (hl : S.L b.2=c.2)

variable {S b hp hl}
lemma pointFiber_empty_of_new_label (hc : ∀j,S.L j ≠ c.2) (U : S.Obj) :
    IsEmpty (Labelled.PointFiber.Fiber U.obj c) := ⟨by
  intro x
  obtain ⟨j,hj⟩ := U.supported x.val.val.1
  exact hc j (hj.trans x.property.2)⟩

end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_StageRefinement
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open UniformObject

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : Fin T.partition.size × Fin T.support.card)
    (hp : S.partition.color (T.partition.point c.1)=b.1)
    (hl : S.L b.2=T.L c.2)

noncomputable def refineFiber (U : S.Obj) : Fiber U b ≃ Fiber ((inclusion h).obj U) c where
  toFun x := ⟨⟨(x.val.val.1,T.partition.point c.1),
    (U.uniform x.val.val.1 x.val.val.2 (T.partition.point c.1) (by
      rw [x.property.1,S.partition.color_point,hp])).mp x.val.property⟩,rfl,
    x.property.2.trans hl⟩
  invFun y := ⟨⟨(y.val.val.1,S.partition.point b.1),
    (U.uniform y.val.val.1 y.val.val.2 (S.partition.point b.1) (by
      rw [y.property.1,hp,S.partition.color_point])).mp y.val.property⟩,rfl,
    y.property.2.trans hl.symm⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl x.property.1.symm
  right_inv y := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl y.property.1.symm

lemma refineFiber_natural {U V : S.Obj} (f : U ⟶ V) (x : Fiber U b) :
    refineFiber h b c hp hl V (fiberMap f b x)=
      fiberMap ((inclusion h).map f) c (refineFiber h b c hp hl U x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact f.uniform x.val (refineFiber h b c hp hl U x).val rfl (by
      change S.partition.color x.val.val.2=S.partition.color (T.partition.point c.1)
      rw [x.property.1,S.partition.color_point,hp])
  · exact (f.arrow.positional (refineFiber h b c hp hl U x).val).symm

noncomputable def refineEvaluationIso :
    evaluation (P:=S.partition) (L:=S.L) ⋙ BarFinitePower.project _ b ≅
      inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ BarFinitePower.project _ c :=
  NatIso.ofComponents (fun U => asIso (C := FiniteSetGroupoid)
    (X := _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj U b) (Y := _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj ((inclusion h).obj U) c)
    (show (_root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj U b) ⟶ (_root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj ((inclusion h).obj U) c) from
    ((enumerate U b).symm.trans ((refineFiber h b c hp hl U).trans (enumerate ((inclusion h).obj U) c)))))
    (by
      intro U V f
      apply Equiv.ext
      intro x
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      dsimp only [Functor.comp_map,Pi.eval,BarFinitePower.project,asIso_hom,Equiv.trans_apply,Equiv.symm_apply_apply]
      change enumerate ((inclusion h).obj V) c (refineFiber h b c hp hl V
          ((enumerate V b).symm (_root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.map f b (enumerate U b x)))) =
        _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.map ((inclusion h).map f) c (enumerate ((inclusion h).obj U) c
          (refineFiber h b c hp hl U ((enumerate U b).symm (enumerate U b x))))
      rw [E_map_enum,Equiv.symm_apply_apply,Equiv.symm_apply_apply,E_map_enum,refineFiber_natural])

lemma fiber_empty_of_new_label (hc : ∀j,S.L j ≠ T.L c.2) (U : S.Obj) :
    IsEmpty (Fiber ((inclusion h).obj U) c) := ⟨by
  intro x
  obtain ⟨j,hj⟩ := U.supported x.val.val.1
  exact hc j (hj.trans x.property.2)⟩

lemma new_label_size (hc : ∀j,S.L j ≠ T.L c.2) (U : S.Obj) :
    (evaluation.obj ((inclusion h).obj U) c).size=0 := by
  have := fiber_empty_of_new_label h c hc U
  exact Fintype.card_eq_zero
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageRefinementMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.emptyFunctorMonoidal _root_.OAI.SimpleAmenable.PolygonObject.FiniteSetGroupoid.instBraidedTerminalEmptyFunctor _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open UniformObject BarFinitePower

variable {a n : ℕ} {S T : Stage a n} (h : S≤T)
variable (b : Fin S.partition.size × Fin S.support.card)
    (c : Fin T.partition.size × Fin T.support.card)
    (hp : S.partition.color (T.partition.point c.1)=b.1)
    (hl : S.L b.2=T.L c.2)

lemma refineFiber_sum_inl (U V : S.Obj) (x : Fiber U b) :
    refineFiber h b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inl x)) =
      fiberSum ((inclusion h).obj U) ((inclusion h).obj V) c
        (.inl (refineFiber h b c hp hl U x)) := rfl
lemma refineFiber_sum_inr (U V : S.Obj) (x : Fiber V b) :
    refineFiber h b c hp hl (UniformObject.sum U V) (fiberSum U V b (.inr x)) =
      fiberSum ((inclusion h).obj U) ((inclusion h).obj V) c
        (.inr (refineFiber h b c hp hl V x)) := rfl
lemma refineEvaluationIso_enum (U : S.Obj) (x : Fiber U b) :
    (refineEvaluationIso h b c hp hl).hom.app U (enumerate U b x) =
      enumerate ((inclusion h).obj U) c (refineFiber h b c hp hl U x) := by
  change enumerate ((inclusion h).obj U) c (refineFiber h b c hp hl U
    ((enumerate U b).symm (enumerate U b x)))=_
  rw [Equiv.symm_apply_apply]

instance refineEvaluationIso_monoidal : NatTrans.IsMonoidal (refineEvaluationIso h b c hp hl).hom where
  unit := by
    apply Equiv.ext
    intro x
    exact Fin.elim0 x
  tensor U V := by
    simp only [Functor.LaxMonoidal.comp_μ, inclusion_μ]
    change ((𝟙 _ ≫ mu U V b) ≫ _) = (_ ≫ (𝟙 _ ≫ mu ((inclusion h).obj U) ((inclusion h).obj V) c) ≫
      (_root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.map (𝟙 ((inclusion h).obj U ⊗ (inclusion h).obj V))) c)
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    apply Equiv.ext
    intro x
    change (refineEvaluationIso h b c hp hl).hom.app (UniformObject.sum U V) (mu U V b x) =
      mu ((inclusion h).obj U) ((inclusion h).obj V) c
        (FiniteSetGroupoid.sumHom ((refineEvaluationIso h b c hp hl).hom.app U)
          ((refineEvaluationIso h b c hp hl).hom.app V) x)
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (_root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj U b) (_root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      erw [mu_inl,refineEvaluationIso_enum,refineFiber_sum_inl,FiniteSetGroupoid.sumHom_inl,
        refineEvaluationIso_enum,mu_inl]
      rfl
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      erw [mu_inr,refineEvaluationIso_enum,refineFiber_sum_inr,FiniteSetGroupoid.sumHom_inr,
        refineEvaluationIso_enum,mu_inr]
      rfl
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageCoordinateMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar.Diagram BarFinitePower UniformObject

variable {a n:ℕ} {S T:Stage a n} (h:S≤T)
    (c:Fin T.partition.size × Fin T.support.card)
noncomputable def newLabelIso (hc:∀j,S.L j ≠ T.L c.2) :
    FiniteSetGroupoid.terminal ⋙ FiniteSetGroupoid.emptyFunctor ≅
      inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ project _ c :=
  NatIso.ofComponents (fun U => asIso (C := FiniteSetGroupoid)
    (X := FiniteSetGroupoid.empty) (Y := _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj ((inclusion h).obj U) c)
    (show FiniteSetGroupoid.empty ⟶ _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.E.obj ((inclusion h).obj U) c from
    finCongr (new_label_size h c hc U).symm)) (by
      intros; apply Equiv.ext; intro x; exact Fin.elim0 x)
noncomputable instance newLabelIsoMonoidal (hc:∀j,S.L j ≠ T.L c.2) :
    NatTrans.IsMonoidal (newLabelIso h c hc).hom where
  unit := by apply Equiv.ext; intro x; exact Fin.elim0 x
  tensor _ _ := by apply Equiv.ext; intro x; exact Fin.elim0 x
lemma newLabel_homology_zero (hc:∀j,S.L j ≠ T.L c.2) (j:ℕ) (hj:0<j) :
    SSet.homologyMap (bar₃Map (inclusion h ⋙ evaluation (P:=T.partition) (L:=T.L) ⋙ project _ c))
      DiagonalResolution.Z j=0 := by
  rw [←bar₃Map_eq_of_monoidalNatTrans (newLabelIso h c hc).hom j,
    bar₃Map_comp,SSet.homologyMap_comp]
  have hz := bar₃_acyclic (C:=FiniteSetGroupoid.Terminal) (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
  rw [hz.eq_of_src (SSet.homologyMap (bar₃Map FiniteSetGroupoid.emptyFunctor) DiagonalResolution.Z j) 0,Limits.comp_zero]
variable (S)
variable {S}
lemma refinement_new_label_zero (hc:∀j,S.L j ≠ T.L c.2) (j:ℕ) (hj:0<j) :
    SSet.homologyMap (bar₃Map (inclusion h) ≫ T.finiteProductComparison ≫ evaluate _ _ c)
      DiagonalResolution.Z j=0 := by
  rw [finiteProductComparison_coordinate,←bar₃Map_comp]
  exact newLabel_homology_zero h c hc j hj
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageSimplicialColimit
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.IntervalBar.Diagram.reindex_map_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsEquivalenceDiagramStringsPosDiagramsDiagramPropertyTransposeDiagram _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramInclusionEquivalence _root_.OAI.RestrictedNerve.posDiagramInclusionEssSurj _root_.OAI.RestrictedNerve.posDiagramInclusionMonoidal _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.posReindex_inclusion_monoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.transpose_evaluation_monoidal _root_.OAI.RestrictedNerve.transpose_reindex_monoidal _root_.OAI.RestrictedNerve.triplePosInclusionEquivalence _root_.OAI.RestrictedNerve.tripleTransposeEquivalence _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.emptyIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.evaluationIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.newLabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.refineEvaluationIso_monoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer

variable {a n : ℕ} (p q : ℕ)
noncomputable def degreeRowsCocone : Cocone (degreeRowsStage (a:=a) (n:=n) p q) where
  pt := simplicial (C:=Diagram (Diagram (Labelled a n) (Fin (p+1))) (Fin (q+1)))
  ι := {
    app S := simplicialMap (Diagram.map (I:=Fin (q+1)) (Diagram.map (I:=Fin (p+1)) S.forget))
    naturality S T h := by
      apply NatTrans.ext; funext r; apply Cat.ext
      exact map₃_inclusion_forget r.unop.len q p (leOfHom h) }
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open IntervalBar IntervalBar.Diagram ColimitTransfer SimplicialDiagonal

variable {a n : ℕ}
noncomputable def middleRowsCocone (p:ℕ) : Cocone (middleRowsStage (a:=a) (n:=n) p) where
  pt := rows₂ (C:=Diagram (Labelled a n) (Fin (p+1)))
  ι := {
    app S := rows₂Map (Diagram.map (I:=Fin (p+1)) S.forget)
    naturality S T h := by
      apply NatTrans.ext; funext q
      change nerveDiagonal.map ((degreeRowsStage p q.unop.len).map h) ≫
        nerveDiagonal.map ((degreeRowsCocone p q.unop.len).ι.app T) =
          nerveDiagonal.map ((degreeRowsCocone p q.unop.len).ι.app S)
      rw [←Functor.map_comp,Cocone.w] }
noncomputable def topRowsCocone : Cocone (topRowsStage (a:=a) (n:=n)) where
  pt := rows₃ (C:=Labelled a n)
  ι := {
    app S := rows₃Map S.forget
    naturality S T h := by
      apply NatTrans.ext; funext p
      change diagonal.map ((middleRowsStage p.unop.len).map h) ≫
        diagonal.map ((middleRowsCocone p.unop.len).ι.app T) =
          diagonal.map ((middleRowsCocone p.unop.len).ι.app S)
      rw [←Functor.map_comp,Cocone.w] }

end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PointFiberHomology
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.MarkedH1.linearStable_epi _root_.OAI.MarkedH1.stableOneπ_epi _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StableBarOne.fromStable_epi _root_.OAI.StableBarOne.linearπ_epi _root_.OAI.TranslationFiltered.regular_filtered _root_.OAI.TranslationNerve.nerve_aug_quasiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SimpleAmenable.PolygonObject.Labelled.Cell
section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Classical

variable {a n : ℕ} {K : Type} [AddCommGroup K]
noncomputable def step (P : polygonAlgebra a) (x : K) : BooleanStep a K :=
  ⟨fun p => if p∈P.val then x else 0,by
    obtain ⟨S,hS⟩ := polygon_hasSquareArrangement P.property
    refine ⟨S,fun p q h => ?_⟩
    have hh := decide_eq_decide.mp (hS p q h)
    simp only [hh]⟩
@[simp] lemma step_apply (P : polygonAlgebra a) (x : K) (p : GenericSquare a) :
    (step P x).val p=if p∈P.val then x else 0 := rfl
@[simp] lemma step_zero (P : polygonAlgebra a) : step P (0:K)=0 := by
  apply Subtype.ext; funext p; simp [step]
@[simp] lemma step_add (P : polygonAlgebra a) (x y : K) : step P (x+y)=step P x+step P y := by
  apply Subtype.ext; funext p
  change (if p∈P.val then x+y else 0) =
    (if p∈P.val then x else 0)+(if p∈P.val then y else 0)
  split_ifs <;> simp
variable {modK : Module ℤ K}
noncomputable def coefficient (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n) :
    K →ₗ[ℤ] LabelledStage.Coefficients a n K where
  toFun x := Finsupp.single l (step P x)
  map_add' _ _ := by rw [step_add,Finsupp.single_add]
  map_smul' r x := by
    let h : K →+ LabelledStage.Coefficients a n K := {
      toFun x := Finsupp.single l (step P x)
      map_zero' := by rw [step_zero,Finsupp.single_zero]
      map_add' _ _ := by rw [step_add,Finsupp.single_add] }
    exact map_intCast_smul h ℤ ℤ r x
@[simp] lemma coefficient_apply (P : polygonAlgebra a) (l : LabelledStage.ReducedLabel n) (x : K) :
    coefficient (K:=K) (modK:=modK) P l x=Finsupp.single l (step P x) := rfl

lemma coefficient_ext {T : Type} [AddCommGroup T] {f g : LabelledStage.Coefficients a n K →+ T}
    (h : ∀P l x,f (Finsupp.single l (step P x))=g (Finsupp.single l (step P x))) : f=g := by
  apply AddMonoidHom.ext; intro v
  induction v using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add l s v hl hs ih =>
    rw [map_add,map_add,ih]
    congr 1
    obtain ⟨Q,hQ⟩ := BooleanStep.exists_common (fun _ : Unit => s)
    have hsQ := hQ ()
    have he : s = ∑i:Fin Q.size,step ⟨_,Q.polygon i⟩ ((s.val) (Q.point i)) := by
      apply Subtype.ext; funext p
      have hv := congrArg (fun w : BooleanStep a K => w.val p) hsQ
      change (BooleanStep.inflate (K:=K) Q (BooleanStep.evaluate (K:=K) Q s)).val p=s.val p at hv
      rw [BooleanStep.inflate_apply,BooleanStep.evaluate_apply] at hv
      rw [←hv]
      rw [Submodule.coe_sum,Finset.sum_apply]
      simp only [step,Set.mem_ofPred_eq]
      rw [Finset.sum_eq_single (Q.color p)]
      · simp
      · intro index _ hindex
        simp [Ne.symm hindex]
      · simp
    rw [he,Finsupp.single_finsetSum,map_sum,map_sum]
    apply Finset.sum_congr rfl; intro i _; exact h _ _ _
end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Classical
open IntervalBar.Diagram BarFinitePower FreeChains LabelledStage

variable {a n : ℕ} (P : polygonAlgebra a) (l : ReducedLabel n)
lemma homology_point (j : ℕ) (hj : 0<j)
    (c : GenericSquare a × ReducedLabel n) :
    SSet.homologyMap (bar₃Map (functor P l ⋙ PointFiber.evaluation ⋙ project _ (c.1,c.2.val))) Z j =
      if c.1∈P.val ∧ l=c.2 then 𝟙 _ else 0 := by
  split_ifs with h
  · rw [←bar₃Map_eq_of_monoidalNatTrans
      (evaluationIso P l (c.1,c.2.val) h.1 (congrArg Subtype.val h.2)).hom j]
    exact bar₃Map_id_homology j
  · rw [←bar₃Map_eq_of_monoidalNatTrans
      (emptyIso P l (c.1,c.2.val) (fun hh => h ⟨hh.1,Subtype.ext hh.2⟩)).hom j,
      bar₃Map_comp,SSet.homologyMap_comp]
    have hz := bar₃_acyclic (C:=FiniteSetGroupoid.Terminal)
      (fun x y => ⟨eqToHom (Subsingleton.elim x y)⟩) j hj
    rw [hz.eq_of_src (SSet.homologyMap (bar₃Map FiniteSetGroupoid.emptyFunctor) Z j) 0,comp_zero]
end SimpleAmenable.PolygonObject.Labelled.Cell

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_Supplemental
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SimpleAmenable.PolygonObject
open _root_.CategoryTheory _root_.OAI.CategoryTheory

instance positionalPropertyInverse (a:ℕ) : Fact (positionalProperty a).StableUnderInverse where
  out := by
    intro U V e h
    change Positional e.hom at h
    change Positional e.inv
    have hi := positional_inv h
    simpa using hi

end SimpleAmenable.PolygonObject

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end


