-- Prove2me | Definitions.Def_OAIQ65Sa016
-- name    : OAIQ65Sa016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:21:47.621309+00:00
-- url     : https://prove2.me/theorems/c40b82c0-0e41-45f7-ad9f-6937a57bd501
-- title:
--   Definitions bundle OAIQ65Sa016 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 61 declarations of OpenAI's Lean: 24 definitions, 2 instances and 35 theorems. The definitions and types are `OAI.SimpleAmenable.PolygonObject.Labelled.initialDisplacement`, `OAI.SimpleAmenable.PolygonObject.Labelled.reindexLabel`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.reducedLabelEquiv`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.empty`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.face`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.representationIso`, `OAI.SimpleAmenable.PolygonPlacement.Configuration.standardLE`, `OAI.SimpleAmenable.PolygonPlacement.configurationRepresentation`, `OAI.SimpleAmenable.PolygonTracks.fullConjugation`, `OAI.SimpleAmenable.PolygonTracks.stabilizeAlternating`, `OAI.SimpleAmenable.SymmetricConfiguration.boundary`, `OAI.SimpleAmenable.SymmetricConfiguration.castGroup`, `OAI.SimpleAmenable.SymmetricConfiguration.chainEquiv`, `OAI.SimpleAmenable.SymmetricConfiguration.column`, `OAI.SimpleAmenable.SymmetricConfiguration.configurationRepresentation`, `OAI.SimpleAmenable.SymmetricConfiguration.empty`, `OAI.SimpleAmenable.SymmetricConfiguration.emptyIso`, `OAI.SimpleAmenable.SymmetricConfiguration.face`, `OAI.SimpleAmenable.SymmetricConfiguration.faceHom`, `OAI.SimpleAmenable.SymmetricConfiguration.permHom`, `OAI.SimpleAmenable.SymmetricConfiguration.representationIso`, `OAI.SimpleAmenable.SymmetricConfiguration.stabilize`, `OAI.SimpleAmenable.SymmetricConfiguration.standardStabilizerEquiv`, `OAI.SimpleAmenable.SymmetricConfiguration.successorStabilize`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Configurations_PolygonAlternatingStabilization`, `SimpleAmenable_Configurations_PolygonPlacementAlternating`, `SimpleAmenable_Configurations_PolygonPlacementArea`, `SimpleAmenable_Configurations_PolygonPlacementPermutation`, `SimpleAmenable_Configurations_SymmetricConfiguration`, `SimpleAmenable_Configurations_SymmetricFaces`, `SimpleAmenable_Configurations_SymmetricStabilizer`, `SimpleAmenable_Configurations_SymmetricStable`, `SimpleAmenable_Configurations_TrajectoryFaces`, `SimpleAmenable_Configurations_TransitiveInduction`, `SimpleAmenable_Homology_ConfigurationResolution`, `SimpleAmenable_Homology_FullGroupStability`, `SimpleAmenable_Homology_HomologyAdditive`, `SimpleAmenable_Homology_PolygonHomologyAction`, `SimpleAmenable_Homology_StageHomologyCoordinates`, `SimpleAmenable_Homology_SymmetricH1`, `SimpleAmenable_Simplicial_TrajectoryReindexLabels`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa009` and `OAIQ65Sa013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa017`, `OAIQ65Sa018`, `OAIQ65Sa022`, `OAIQ65Sa023` and `OAIQ65Sa024`; the statements `OAI_SimpleAmenable_InitialCoverSystem_old_axis_bridge_control_cover_uniform` and `OAI_SimpleAmenable_InitialCoverSystem_pair_actual_law`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa009
import Definitions.Def_OAIQ65Sa013

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ConfigurationResolution
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instCoeFunForallFin _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section ConfigurationResolution
open Classical _root_.CategoryTheory Finsupp

namespace PolygonPlacement

noncomputable def configurationRepresentation (a m n : ℕ) :
    Representation ℤ (polygonFullGroup a m) (ConfigurationChains.degree (@Apart a m) n) :=
  ConfigurationChains.representation (fun g v w h => (apart_smul_iff g v w).mpr h) n
end PolygonPlacement
end ConfigurationResolution

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonPlacementArea
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFaithfulForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instMonoidalForget _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instCoeFunForallFin _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonPlacementArea

open Classical Set
namespace PolygonPlacement

theorem imageBank_area_le {a m : ℕ} (f : PolygonPlacement a m) :
    (∑i,PolygonArea.area (imageBank f i))≤1 := by
  obtain ⟨s,hs,hcover⟩ := f.charts
  let D : s → polygonAlgebra a := fun c => c.val.2.2
  obtain ⟨P,hP,hSup,hdisP⟩ := Fintype.exists_disjointed_le D
  have hcoverP : (⊤ : polygonAlgebra a).val=⋃c,(P c).val := by
    have hv := congrArg (fun A : polygonAlgebra a => A.val) hSup
    simp only [PolygonArea.val_finset_sup,Finset.mem_univ,Set.iUnion_true] at hv
    rw [hv]
    ext x
    simp only [BooleanSubalgebra.val_top,Set.top_eq_univ,Set.mem_univ,true_iff,Set.mem_iUnion]
    obtain ⟨c,hc,hx⟩ := hcover x
    exact ⟨⟨c,hc⟩,hx⟩
  have hsumP : (∑c,PolygonArea.area (P c))=1 := by
    rw [←PolygonArea.area_top a]
    symm
    apply PolygonArea.area_eq_sum _ P hcoverP
    intro i j hij
    have h : Disjoint (P i) (P j) := hdisP hij
    rw [disjoint_iff] at h
    exact Set.disjoint_iff_inter_eq_empty.mpr (congrArg (fun A : polygonAlgebra a => A.val) h)
  let Q (i : Fin m) (c : s) : polygonAlgebra a :=
    if c.val.1=i then translatedPolygon c.val.2.1 (P c) else ⊥
  have hbank (i : Fin m) : imageBank f i≤Finset.univ.sup (Q i) := by
    intro y hy
    obtain ⟨x,hxy⟩ := hy
    have hx : x∈⋃c,(P c).val := by rw [←hcoverP]; trivial
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
    have he := (hs c.val c.property x (hP c hc)).symm.trans hxy
    have ht : c.val.1=i := congrArg Prod.fst he
    rw [PolygonArea.val_finset_sup]
    refine Set.mem_iUnion₂.mpr ⟨c,Finset.mem_univ _,?_⟩
    simp only [Q,ht,ite_true]
    exact ⟨x,hc,congrArg Prod.snd he⟩
  calc
    (∑i,PolygonArea.area (imageBank f i))≤∑i,∑c,PolygonArea.area (Q i c) := by
      apply Finset.sum_le_sum
      intro i _
      exact (PolygonArea.area_mono (hbank i)).trans (PolygonArea.area_finset_sup_le _ _)
    _=∑c,PolygonArea.area (P c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      simp only [Q,apply_ite,PolygonArea.area_bot,PolygonArea.area_translation]
      simp
    _=1 := hsumP

end PolygonPlacement
end PolygonPlacementArea

section PolygonCommonNeighbor

open Classical Set
namespace PolygonPlacement

theorem placement_in_bank {a m : ℕ} (hm : 0 < m) (V : Fin m → polygonAlgebra a)
    (hV : 1 < ∑i,PolygonArea.area (V i)) :
    ∃ e : PolygonPlacement a m,∀x,(e x).2∈(V (e x).1).val := by
  let i₀ : Fin m := ⟨0,hm⟩
  let U : Fin m → polygonAlgebra a := fun i => if i=i₀ then ⊤ else ⊥
  have hU : (∑i,PolygonArea.area (U i))=1 := by
    simp [U,apply_ite,PolygonArea.area_bot,PolygonArea.area_top]
  obtain ⟨f,hf⟩ := PolygonGrid.strict_comparison U V (by rwa [hU])
  let PU : PolygonObject a := ⟨m,U⟩
  let PV : PolygonObject a := ⟨m,V⟩
  let src (x : GenericSquare a) : PU.Point := ⟨(i₀,x),by simp [PU,U]⟩
  let ef : GenericSquare a ↪ TrackPoint a m :=
    ⟨fun x => (f (src x)).val,fun x y he =>
      congrArg (fun p : PU.Point => p.val.2) (f.injective (Subtype.ext he))⟩
  have hetab : ∃s : Finset (Fin m × (CutRing×CutRing) × polygonAlgebra a),
      (∀c∈s,∀x∈c.2.2.val,ef x=(c.1,translate a c.2.1 x)) ∧
      ∀x,∃c∈s,x∈c.2.2.val := by
    obtain ⟨s,hs,hcover⟩ := hf
    let t := s.filter (fun c => c.source=i₀)
    let conv : PolygonObject.Chart (a:=a) m m → Fin m × (CutRing×CutRing) × polygonAlgebra a :=
      fun c => (c.target,c.shift,c.domain)
    refine ⟨t.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hds,hdsrc⟩ := Finset.mem_filter.mp hd
      intro x hx
      obtain ⟨hu,he⟩ := hs d hds x hx
      change (f (src x)).val=(d.target,translate a d.shift x)
      simpa only [src,hdsrc] using he
    · intro x
      obtain ⟨c,hc,hx⟩ := hcover (src x)
      refine ⟨conv c,Finset.mem_image.mpr ⟨c,?_,rfl⟩,hx.2⟩
      exact Finset.mem_filter.mpr ⟨hc,hx.1.symm⟩
  exact ⟨⟨ef,hetab⟩,fun x => (f (src x)).property⟩

theorem common_neighbor {a m : ℕ} (S : Finset (PolygonPlacement a m))
    (hm : S.card+1 < m) : ∃e : PolygonPlacement a m,∀f∈S,Apart e f := by
  let B (i : Fin m) : polygonAlgebra a := S.sup (fun f => imageBank f i)
  let V (i : Fin m) : polygonAlgebra a := (B i)ᶜ
  have hB : (∑i,PolygonArea.area (B i))≤S.card := by
    calc
      _≤∑i,∑f∈S,PolygonArea.area (imageBank f i) :=
        Finset.sum_le_sum (fun i _ => PolygonArea.area_finset_sup_le S _)
      _=∑f∈S,∑i,PolygonArea.area (imageBank f i) := Finset.sum_comm
      _≤∑_∈S,(1:ENNReal) := Finset.sum_le_sum (fun f _ => imageBank_area_le f)
      _=S.card := by simp
  have hsum : (∑i,PolygonArea.area (B i))+(∑i,PolygonArea.area (V i))=m := by
    rw [←Finset.sum_add_distrib]
    simp only [V,PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hV : 1 < ∑i,PolygonArea.area (V i) := by
    by_contra hn
    have hh : (m:ENNReal)≤S.card+1 :=
      hsum.symm.trans_le (add_le_add hB (le_of_not_gt hn))
    have hml : (S.card:ENNReal)+1 < m := by exact_mod_cast hm
    exact (not_le_of_gt hml) hh
  obtain ⟨e,he⟩ := placement_in_bank (by omega : 0 < m) V hV
  refine ⟨e,fun f hf => ?_⟩
  rw [apart_iff]
  intro x y hxy
  have hn := he x
  change (e x).2∉(B (e x).1).val at hn
  apply hn
  have hin : (imageBank f (e x).1).val⊆(B (e x).1).val := by
    change imageBank f (e x).1 ≤ S.sup (fun g => imageBank g (e x).1)
    exact Finset.le_sup (f := fun g : PolygonPlacement a m => imageBank g (e x).1) hf
  apply hin
  refine ⟨y,?_⟩
  exact hxy.symm

theorem configuration_lowDegree_exact {a m n : ℕ} (hm : 33 ≤ m) (hn : n ≤ 2) :
    Function.Exact (ConfigurationChains.degreeBoundary (@Apart a m) (n+1))
      (ConfigurationChains.degreeBoundary (@Apart a m) n) := by
  apply ConfigurationChains.lowDegree_exact _ hn
  intro S hS
  exact common_neighbor S (by omega)

end PolygonPlacement
end PolygonCommonNeighbor

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonPlacementPermutation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instCoeFunForallFin _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonConfigurationTransitive

open Classical Set
namespace PolygonPlacement
variable {a m n : ℕ}

theorem exists_configuration_avoiding (S : Finset (PolygonPlacement a m)) (n : ℕ)
    (hm : S.card+n+1 < m) :
    ∃w : Fin n → PolygonPlacement a m,
      Pairwise (fun i j => Apart (w i) (w j)) ∧ ∀i f,f∈S → Apart (w i) f := by
  induction n generalizing S with
  | zero => exact ⟨Fin.elim0,by intro i; exact i.elim0,by intro i; exact i.elim0⟩
  | succ n ih =>
    obtain ⟨v,hv⟩ := common_neighbor S (by omega)
    obtain ⟨w,hw,hws⟩ := ih (insert v S) (by
      have hh := Finset.card_insert_le v S
      omega)
    refine ⟨Fin.cons v w,?_,?_⟩
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact (hws j v (Finset.mem_insert_self _ _)).symm
      | succ i =>
        induction j using Fin.cases with
        | zero => exact hws i v (Finset.mem_insert_self _ _)
        | succ j => exact hw (fun he => hij (congrArg Fin.succ he))
    · intro i f hf
      induction i using Fin.cases with
      | zero => exact hv f hf
      | succ i => exact hws i f (Finset.mem_insert_of_mem hf)

theorem swap_configurations (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j)))
    (hfg : ∀i j,Apart (f i) (g j)) :
    ∃h : polygonFullGroup a m,∀i x,h.val (f i x)=g i x := by
  let e : Fin n ⊕ Fin n → PolygonPlacement a m := Sum.elim f g
  have he : Pairwise (fun i j => Apart (e i) (e j)) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hf (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hfg i j
    | inr i =>
      cases j with
      | inl j => exact (hfg j i).symm
      | inr j => exact hg (fun h => hij (congrArg Sum.inr h))
  refine ⟨familyPerm e he (Equiv.sumComm _ _),?_⟩
  intro i x
  exact familyPerm_apply e he (Equiv.sumComm _ _) (.inl i) x

theorem configuration_transitive (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j))) (hm : 3*n+1 < m) :
    ∃h : polygonFullGroup a m,∀i,h • f i=g i := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S n (by omega)
  have hwf (i j : Fin n) : Apart (w i) (f j) :=
    hws i (f j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hwg (i j : Fin n) : Apart (w i) (g j) :=
    hws i (g j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  obtain ⟨u,hu⟩ := swap_configurations f w hf hw (fun i j => (hwf j i).symm)
  obtain ⟨v,hv⟩ := swap_configurations w g hw hg hwg
  refine ⟨v*u,fun i => ?_⟩
  apply PolygonPlacement.ext
  intro x
  change v.val (u.val (f i x))=g i x
  rw [hu,hv]

end PolygonPlacement
end PolygonConfigurationTransitive

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonPlacementAlternating
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonConfigurationOrbit
open Classical Set
namespace PolygonPlacement

namespace Configuration
variable {a m p : ℕ}

theorem stabilizer_standard (a p n : ℕ) :
    MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n)=
      PolygonTracks.bankFixer a p n := by
  ext g
  change g • standard a p n=standard a p n ↔ _
  constructor
  · intro he x
    exact congrArg (fun f : Configuration a (p+n) p => f x.1 x.2) he
  · intro he
    apply ext
    intro i
    apply PolygonPlacement.ext
    intro x
    exact he (i,x)

theorem transitive (f g : Configuration a m p) (hm : 3*p+1 < m) :
    ∃u : polygonFullGroup a m,u • f=g := by
  obtain ⟨u,hu⟩ := configuration_transitive f.val g.val f.property g.property hm
  exact ⟨u,ext hu⟩

end Configuration
end PolygonPlacement
end PolygonConfigurationOrbit

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonAlternatingStabilization
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonAlternatingStabilization
open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

theorem stabilize_threeSlot {g : polygonFullGroup a n} (hg : IsThreeSlotCycle g) :
    IsThreeSlotCycle (stabilize a k n g) := by
  obtain ⟨U,s,hU,hs,hg,hfix⟩ := hg
  let t : Fin 3 → Fin (k+n) × (CutRing × CutRing) := fun i => ((s i).1.natAdd k,(s i).2)
  have ht (x : Fin 3 × U.val) : SlotMap a (k+n) U t x=rightIncl a k n (SlotMap a n U s x) := rfl
  refine ⟨U,t,hU,?_,?_,?_⟩
  · intro x y hxy
    apply hs
    exact rightIncl_injective (by simpa only [ht] using hxy)
  · intro i x
    rw [ht,ht]
    change (stabilize a k n g).val ((SlotMap a n U s (i,x)).1.natAdd k,
      (SlotMap a n U s (i,x)).2)=_
    rw [stabilize_right,hg]
    rfl
  · intro p hp
    obtain ⟨q,rfl⟩ := (join a k n).surjective p
    cases q with
    | inl q => exact stabilize_left g q
    | inr q =>
      rw [join_inr,stabilize_right]
      have hq : q∉Set.range (SlotMap a n U s) := by
        rintro ⟨x,rfl⟩
        exact hp ⟨x,rfl⟩
      rw [hfix q hq]

theorem stabilize_mem_alternating (g : polygonAlternatingGroup a n) :
    stabilize a k n g.val∈polygonAlternatingGroup a (k+n) := by
  have hl : polygonAlternatingGroup a n ≤
      (polygonAlternatingGroup a (k+n)).comap (stabilize a k n) := by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    exact Subgroup.subset_closure (stabilize_threeSlot hf)
  exact hl g.property

noncomputable def stabilizeAlternating (a k n : ℕ) :
    polygonAlternatingGroup a n →* polygonAlternatingGroup a (k+n) :=
  (stabilize a k n).restrict (fun g hg => stabilize_mem_alternating ⟨g,hg⟩)

@[simp] theorem stabilizeAlternating_val (g : polygonAlternatingGroup a n) :
    (stabilizeAlternating a k n g).val=stabilize a k n g.val := rfl

end PolygonTracks
end PolygonAlternatingStabilization

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TransitiveInduction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section PolygonConfigurationModule

open Classical _root_.CategoryTheory Finsupp
namespace PolygonPlacement.Configuration
variable {a m p : ℕ}

theorem chainEquiv_intertwines (g : polygonFullGroup a m) :
    (chainEquiv a m p).toLinearMap.comp (TransitiveInduction.permutationRep
      (G:=polygonFullGroup a m) (X:=Configuration a m p) g)=
    (configurationRepresentation a m p g).comp (chainEquiv a m p).toLinearMap := by
  apply Finsupp.lhom_ext
  intro f z
  apply Subtype.ext
  change (chainEquiv a m p (TransitiveInduction.permutationRep g (Finsupp.single f z))).val=
    ConfigurationChains.push (fun v => g • v) (chainEquiv a m p (Finsupp.single f z)).val
  rw [TransitiveInduction.permutationRep_single,chainEquiv_single_val,chainEquiv_single_val,
    ConfigurationChains.push_single]
  congr 1
  simp [List.map_ofFn]
  rfl

noncomputable def representationIso (a m p : ℕ) :
    Rep.of (TransitiveInduction.permutationRep (G:=polygonFullGroup a m) (X:=Configuration a m p)) ≅
      Rep.of (configurationRepresentation a m p) :=
  Rep.mkIso {toLinearEquiv:=chainEquiv a m p,isIntertwining':=chainEquiv_intertwines}

end PolygonPlacement.Configuration
end PolygonConfigurationModule

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_HomologyAdditive
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

noncomputable def face (i : Fin (p+1)) (f : Configuration a m (p+1)) :
    Configuration a m p :=
  ⟨fun j => f (i.succAbove j),fun j k hjk => f.property (by
    intro h
    exact hjk (Fin.succAbove_right_injective h))⟩

@[simp] lemma face_apply (i : Fin (p+1)) (f : Configuration a m (p+1)) (j : Fin p) :
    face i f j=f (i.succAbove j) := rfl

@[simp] lemma face_smul (i : Fin (p+1)) (g : polygonFullGroup a m)
    (f : Configuration a m (p+1)) : face i (g • f)=g • face i f := rfl

lemma permHom_centralizes (f : Configuration a m p) (σ : Equiv.Perm (Fin p))
    (h : MulAction.stabilizer (polygonFullGroup a m) f) :
    permHom f.val f.property σ * h.val = h.val * permHom f.val f.property σ := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  have hh (i : Fin p) (y : GenericSquare a) : h.val.val (f i y)=f i y :=
    congrArg (fun t : Configuration a m p => t i y) h.property
  have hs : SupportedIn (permHom f.val f.property σ).val (Set.range (bank f.val f.property)) := by
    intro x hx
    apply perm_fixed
    intro i hi
    obtain ⟨y,rfl⟩ := hi
    exact hx ⟨(i,y),rfl⟩
  have he := supported_fixer_commute (f:=h.val.val) (by
    rintro x ⟨⟨i,y⟩,rfl⟩
    exact hh i y) hs
  exact congrArg (fun e : Equiv.Perm (TrackPoint a m) => e x) he.symm.eq

lemma permHom_face (f : Configuration a m (p+1)) (i j : Fin (p+1)) :
    permHom f.val f.property (facePermutation i j) • face i f=face j f := by
  apply ext
  intro k
  apply PolygonPlacement.ext
  intro x
  change (permHom f.val f.property (facePermutation i j)).val (f (i.succAbove k) x) =
    f (j.succAbove k) x
  rw [permHom_apply, facePermutation_apply]

noncomputable def standardLE (a m p : ℕ) (hp : p ≤ m) : Configuration a m p :=
  ⟨fun k => PolygonPlacement.standard (Fin.castLE hp k),fun _ _ hkl =>
    standard_apart (fun he => hkl (Fin.castLE_injective hp he))⟩

end PolygonPlacement.Configuration
end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricConfiguration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
noncomputable def configurationRepresentation (m p:ℕ) : Representation ℤ (G m) (ConfigurationChains.degree (Ne:Fin m → Fin m → Prop) p) :=
  ConfigurationChains.representation ne_smul p

noncomputable def chainEquiv (m p : ℕ) :
    (Configuration m p  →₀ ℤ) ≃ₗ[ℤ] ConfigurationChains.degree ((Ne:Fin m → Fin m → Prop)) p :=
  (Finsupp.domLCongr (listEquiv m p)).trans (ConfigurationChains.simplexModuleEquiv _ p).symm

@[simp] theorem chainEquiv_single_val (f : Configuration m p) (z : ℤ) :
    (chainEquiv m p (Finsupp.single f z)).val=Finsupp.single (List.ofFn f.val) z := by
  unfold chainEquiv
  rw [LinearEquiv.trans_apply,Finsupp.domLCongr_single]
  simp [ConfigurationChains.simplexModuleEquiv]
  exact Finsupp.supportedEquivFinsupp_symm_single _ _ _

theorem chainEquiv_intertwines (g : G m) :
    (chainEquiv m p).toLinearMap.comp (TransitiveInduction.permutationRep
      (G:=G m) (X:=Configuration m p) g)=
    (configurationRepresentation m p g).comp (chainEquiv m p).toLinearMap := by
  apply Finsupp.lhom_ext
  intro f z
  apply Subtype.ext
  change (chainEquiv m p (TransitiveInduction.permutationRep g (Finsupp.single f z))).val=
    ConfigurationChains.push (fun v => g  •  v) (chainEquiv m p (Finsupp.single f z)).val
  rw [TransitiveInduction.permutationRep_single,chainEquiv_single_val,chainEquiv_single_val,
    ConfigurationChains.push_single]
  congr 1
  simp [List.map_ofFn]
  rfl

noncomputable def representationIso (m p : ℕ) :
    Rep.of (TransitiveInduction.permutationRep (G:=G m) (X:=Configuration m p)) ≅
      Rep.of (configurationRepresentation m p) :=
  Rep.mkIso {toLinearEquiv:=chainEquiv m p,isIntertwining':=chainEquiv_intertwines}

noncomputable abbrev column (m p : ℕ) :=
  Rep.of (TransitiveInduction.permutationRep
    (G:=G m) (X:=Configuration m p))

noncomputable def face (i : Fin (p+1)) (f : Configuration m (p+1)) :
    Configuration m p :=
  ⟨fun j => f (i.succAbove j),f.property.comp Fin.succAbove_right_injective⟩

@[simp] lemma face_apply (i : Fin (p+1)) (f : Configuration m (p+1)) (j : Fin p) :
    face i f j=f (i.succAbove j) := rfl

@[simp] lemma face_smul (i : Fin (p+1)) (g : G m)
    (f : Configuration m (p+1)) : face i (g  •  f)=g  •  face i f := rfl

noncomputable def faceHom (m p : ℕ) (i : Fin (p+1)) :
    column m (p+1) ⟶ column m p :=
  TransitiveInduction.equivariantMap (face i) (face_smul i)

noncomputable def boundary (m p : ℕ) : column m (p+1) ⟶ column m p :=
  (representationIso m (p+1)).hom ≫
    ConfigurationChains.boundaryRep ne_smul p ≫
    (representationIso m p).inv

lemma boundary_chain (c : Configuration m (p+1)  →₀ ℤ) :
    chainEquiv m p ((boundary m p).hom c) =
      ConfigurationChains.degreeBoundary ((Ne:Fin m → Fin m → Prop)) p (chainEquiv m (p+1) c) := by
  change chainEquiv m p ((chainEquiv m p).symm _) = _
  exact (chainEquiv m p).apply_symm_apply _

end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FullGroupStability
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
instance empty_subsingleton (a m : ℕ) : Subsingleton (Configuration a m 0) :=
  ⟨fun _ _ => ext (fun index => Fin.elim0 index)⟩

noncomputable def empty (a m : ℕ) : Configuration a m 0 := standardLE a m 0 (by omega)

end PolygonPlacement.Configuration
end SimpleAmenable

end

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricFaces
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

section

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
noncomputable def permHom (f:Configuration m p) (σ:Equiv.Perm (Fin p)) : G m :=
  σ.viaFintypeEmbedding ⟨f.val,f.property⟩

lemma boundary_square (m p : ℕ) : boundary m (p+1) ≫ boundary m p=0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro c
  apply (chainEquiv m p).injective
  change chainEquiv m p ((boundary m p).hom ((boundary m (p+1)).hom c)) =
    chainEquiv m p 0
  rw [boundary_chain, boundary_chain, ConfigurationChains.degreeBoundary_square, map_zero]

end

attribute [local instance 1200] Rep.hV2
variable {m p:ℕ}
instance empty_subsingleton (m : ℕ) : Subsingleton (Configuration m 0) :=
  ⟨fun _ _ => ext (fun i => Fin.elim0 i)⟩

noncomputable def empty (m : ℕ) : Configuration m 0 := standardLE m 0 (by omega)

noncomputable def emptyIso (m : ℕ) : column m 0 ≅ Rep.trivial ℤ (G m) ℤ :=
  Rep.mkIso (Representation.Equiv.mk (Finsupp.uniqueLinearEquiv ℤ ℤ (empty m)) (by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    change (TransitiveInduction.permutationRep g (single x z)) (empty m)=
      (single x z) (empty m)
    rw [TransitiveInduction.permutationRep_single]
    congr 2
    exact Subsingleton.elim _ _))

@[simp] lemma emptyIso_single (m : ℕ) (x : Configuration m 0) (z : ℤ) :
    (emptyIso m).hom.hom (single x z)=z := by
  change (single x z) (empty m)=z
  simp [Subsingleton.elim (empty m) x]

end SimpleAmenable.SymmetricConfiguration

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricStabilizer
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2
noncomputable def stabilize (p n:ℕ) : G n →* G (p+n) :=
  Equiv.Perm.ofSubtype.comp (Equiv.permCongrHom (tailEquiv p n)).toMonoidHom
lemma stabilize_apply_tail (p n:ℕ) (g:G n) (i:Fin n) :
    stabilize p n g (Fin.natAdd p i)=Fin.natAdd p (g i) := by
  change Equiv.Perm.ofSubtype ((Equiv.permCongrHom (tailEquiv p n)) g) _ = _
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (by simp)]
  change ((tailEquiv p n) (g ((tailEquiv p n).symm ((tailEquiv p n) i)))).val = _
  rw [Equiv.symm_apply_apply]
  rfl
lemma stabilize_apply_head (p n:ℕ) (g:G n) (i:Fin p) :
    stabilize p n g (Fin.castAdd n i)=Fin.castAdd n i := by
  apply Equiv.Perm.ofSubtype_apply_of_not_mem
  exact not_le.mpr i.isLt
lemma stabilize_injective (p n:ℕ) : Function.Injective (stabilize p n) := by
  intro _ _ gh
  apply Equiv.ext
  intro i
  have hi := congrArg (fun g:G (p+n)=>g (Fin.natAdd p i)) gh
  simpa only [stabilize_apply_tail,Fin.natAdd_inj] using hi
lemma stabilize_range (p n:ℕ) : (stabilize p n).range =
    MulAction.stabilizer (G (p+n)) (standard p n) := by
  ext g
  constructor
  · rintro ⟨h,rfl⟩
    apply ext
    intro i
    exact stabilize_apply_head p n h i
  · intro hg
    have hfix (i:Fin p) : g (Fin.castAdd n i)=Fin.castAdd n i :=
      congrArg (fun f:Configuration (p+n) p=>f i) hg
    have hr : g ∈ (Equiv.Perm.ofSubtype : Equiv.Perm {x:Fin (p+n)//p≤x.val} →* G (p+n)).range := by
      rw [Equiv.Perm.mem_range_ofSubtype_iff]
      intro x hx
      change p≤x.val
      by_contra hp
      have he := hfix ⟨x.val,by omega⟩
      exact (Equiv.Perm.mem_support.mp hx) he
    obtain ⟨h,hh⟩ := hr
    refine ⟨(Equiv.permCongrHom (tailEquiv p n)).symm h,?_⟩
    change Equiv.Perm.ofSubtype ((Equiv.permCongrHom (tailEquiv p n)) ((Equiv.permCongrHom (tailEquiv p n)).symm h))=g
    rw [MulEquiv.apply_symm_apply]
    exact hh
noncomputable def standardStabilizerEquiv (p n:ℕ) : G n ≃*
    MulAction.stabilizer (G (p+n)) (standard p n) :=
  (MulEquiv.ofBijective (stabilize p n).rangeRestrict ⟨fun _ _ h=>stabilize_injective p n (congrArg Subtype.val h),
    fun x=>by obtain ⟨g,hg⟩:=x.property; exact ⟨g,Subtype.ext hg⟩⟩).trans
    (MulEquiv.subgroupCongr (stabilize_range p n))
end SimpleAmenable.SymmetricConfiguration

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_SymmetricH1
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.SymmetricConfiguration

section

attribute [local instance 1200] Rep.hV2
noncomputable def castGroup {m n:ℕ} (h:m=n) : G m ≃* G n := h ▸ MulEquiv.refl _
end

attribute [local instance 1200] Rep.hV2
end SimpleAmenable.SymmetricConfiguration

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Representation Rep
namespace SimpleAmenable.SymmetricConfiguration

attribute [local instance 1200] Rep.hV2

noncomputable def successorStabilize (n : ℕ) :
    G n →* G (n+1) :=
  (castGroup (Nat.add_comm 1 n)).toMonoidHom.comp (stabilize 1 n)

end SimpleAmenable.SymmetricConfiguration

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PolygonHomologyAction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonHomologyAction

open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

noncomputable def fullConjugation (a m : ℕ) (f : polygonFullGroup a m) :
    polygonAlternatingGroup a m →* polygonAlternatingGroup a m :=
  (MulAut.conj f).toMonoidHom.restrict (fun g hg =>
    (polygonAlternatingGroup_normal a m).conj_mem g hg f)

@[simp] theorem fullConjugation_val (f : polygonFullGroup a (k+n))
    (g : polygonAlternatingGroup a (k+n)) :
    (fullConjugation a (k+n) f g).val=f*g.val*f⁻¹ := rfl

end PolygonTracks
end PolygonHomologyAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TrajectoryReindexLabels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled
section

variable {a n m:ℕ}
def reindexLabel (u : Fin (m+1) ⥤ Fin (n+1))
    (g:Fin n → CutRing × CutRing) (i:Fin m) : CutRing × CutRing :=
  Fin.partialSum g (u.obj i.succ)-Fin.partialSum g (u.obj i.castSucc)
def initialDisplacement (u : Fin (m+1) ⥤ Fin (n+1))
    (g:Fin n → CutRing × CutRing) : CutRing × CutRing :=
  Fin.partialSum g (u.obj 0)
lemma representative_partialSum (g:Fin n → CutRing × CutRing) (hg:Reduced g) (i:Fin (n+1)) :
    orbitRepresentative (Fin.partialSum g i)=Fin.partialSum g i := by
  induction i using Fin.induction with
  | zero => simp only [Fin.partialSum_zero]; rfl
  | succ i ih => rw [Fin.partialSum_succ,representative_add,ih,hg i]
lemma reindexLabel_reduced (u : Fin (m+1) ⥤ Fin (n+1))
    (g:Fin n → CutRing × CutRing) (hg:Reduced g) : Reduced (reindexLabel u g) := by
  intro i
  rw [reindexLabel,representative_sub,representative_partialSum g hg,representative_partialSum g hg]
end

end SimpleAmenable.PolygonObject.Labelled

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrajectoryFaces
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace SimpleAmenable.PolygonObject.Labelled

variable {n : ℕ}
lemma reindexLabel_zero_face (g : Fin (n+1) → CutRing × CutRing) :
    reindexLabel (faceFunctor (0 : Fin (n+2))) g = Fin.tail g := by
  funext k
  simp only [reindexLabel,faceFunctor_obj,Fin.zero_succAbove,Fin.partialSum_succ']
  rw [show g 0 + Fin.partialSum (Fin.tail g) k.succ -
    (g 0 + Fin.partialSum (Fin.tail g) k.castSucc) =
    -Fin.partialSum (Fin.tail g) k.castSucc + Fin.partialSum (Fin.tail g) k.succ by abel]
  rw [Fin.partialSum_succ]
  abel
lemma reindexLabel_succ_face (g : Fin (n+1) → CutRing × CutRing) (i : Fin (n+1)) :
    reindexLabel (faceFunctor i.succ) g = i.contractNth (·+·) g := by
  funext k
  simp only [reindexLabel,faceFunctor_obj,Fin.succ_succAbove_succ]
  rw [sub_eq_add_neg,add_comm]
  exact Fin.neg_partialSum_add_eq_contractNth g i k
lemma initialDisplacement_zero_face (g : Fin (n+1) → CutRing × CutRing) :
    initialDisplacement (faceFunctor (0 : Fin (n+2))) g = g 0 := by
  simp only [initialDisplacement,faceFunctor_obj,Fin.zero_succAbove,Fin.partialSum_succ',Fin.partialSum_zero,add_zero]
lemma initialDisplacement_succ_face (g : Fin (n+1) → CutRing × CutRing) (i : Fin (n+1)) :
    initialDisplacement (faceFunctor i.succ) g = 0 := by
  simp only [initialDisplacement,faceFunctor_obj,Fin.succ_succAbove_zero,Fin.partialSum_zero]
end SimpleAmenable.PolygonObject.Labelled

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_StageHomologyCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
open scoped TensorProduct
namespace SimpleAmenable.PolygonObject.LabelledStage

noncomputable def reducedLabelEquiv (n:ℕ) : ReducedLabel n ≃ (Fin n → Multiplicative (ℤ×ℤ)) where
  toFun l i := SquareStep.orbitProjection (Multiplicative.ofAdd (l.val i))
  invFun l := ⟨fun i => (SquareStep.orbitLift (l i)).toAdd,by
    intro i
    change orbitRepresentative (((l i).toAdd.1:CutRing)*cutTau,((l i).toAdd.2:CutRing)*cutTau)=_
    simp [orbitRepresentative,cutTau]
    rfl⟩
  left_inv l := by
    apply Subtype.ext; funext i
    exact l.property i
  right_inv l := by
    funext i
    change Multiplicative.ofAdd ((((l i).toAdd.1:CutRing)*cutTau).im,
      (((l i).toAdd.2:CutRing)*cutTau).im) = l i
    simp [cutTau]

end SimpleAmenable.PolygonObject.LabelledStage

end

end

end OAI
end


