-- Prove2me | Definitions.Def_OAIQ65Sa006
-- name    : OAIQ65Sa006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T01:31:01.234333+00:00
-- url     : https://prove2.me/theorems/a3860fb2-e78d-49c3-a7a7-bc269ac052b8
-- title:
--   Definitions bundle OAIQ65Sa006 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 277 declarations of OpenAI's Lean: 106 definitions, 4 inductive types or structures, 22 instances and 145 theorems. The definitions and types are `OAI.SimpleAmenable.ConditionalAvailable`, `OAI.SimpleAmenable.PolygonArea.area`, `OAI.SimpleAmenable.PolygonGrid.displacement`, `OAI.SimpleAmenable.PolygonGrid.rectangle`, `OAI.SimpleAmenable.PolygonObject`, `OAI.SimpleAmenable.PolygonObject.Arrow`, `OAI.SimpleAmenable.PolygonObject.Chart`, `OAI.SimpleAmenable.PolygonObject.Chart.Contains`, `OAI.SimpleAmenable.PolygonObject.Chart.Holds`, `OAI.SimpleAmenable.PolygonObject.Chart.comp`, `OAI.SimpleAmenable.PolygonObject.Chart.inverse`, `OAI.SimpleAmenable.PolygonObject.Component`, `OAI.SimpleAmenable.PolygonObject.HasTable`, `OAI.SimpleAmenable.PolygonObject.LabelledStage.Stage.tripleDegree`, `OAI.SimpleAmenable.PolygonObject.Point`, `OAI.SimpleAmenable.PolygonObject.Positional`, `OAI.SimpleAmenable.PolygonObject.RawString`, `OAI.SimpleAmenable.PolygonObject.StringGroupoid`, `OAI.SimpleAmenable.PolygonObject.baseArrow`, `OAI.SimpleAmenable.PolygonObject.complement`, `OAI.SimpleAmenable.PolygonObject.complementArrow`, `OAI.SimpleAmenable.PolygonObject.complementIso`, `OAI.SimpleAmenable.PolygonObject.component`, `OAI.SimpleAmenable.PolygonObject.empty`, `OAI.SimpleAmenable.PolygonObject.extendLadder`, `OAI.SimpleAmenable.PolygonObject.fullGroupArrow`, `OAI.SimpleAmenable.PolygonObject.fullGroupOfArrow`, `OAI.SimpleAmenable.PolygonObject.ladderProperty`, `OAI.SimpleAmenable.PolygonObject.leftUnit`, `OAI.SimpleAmenable.PolygonObject.leftUnitEquiv`, `OAI.SimpleAmenable.PolygonObject.positionalProperty`, `OAI.SimpleAmenable.PolygonObject.positionalSubgroupoid`, `OAI.SimpleAmenable.PolygonObject.refinement`, `OAI.SimpleAmenable.PolygonObject.refinementArrow`, `OAI.SimpleAmenable.PolygonObject.refinementEquiv`, `OAI.SimpleAmenable.PolygonObject.relabelArrow`, `OAI.SimpleAmenable.PolygonObject.rightUnit`, `OAI.SimpleAmenable.PolygonObject.rightUnitEquiv`, `OAI.SimpleAmenable.PolygonObject.shiftArrow`, `OAI.SimpleAmenable.PolygonObject.shiftEquiv` and 70 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Arithmetic_CompiledTranslations`, `SimpleAmenable_Arithmetic_ConcurrentDenominators`, `SimpleAmenable_CentralCovers_BoundedRelationCover`, `SimpleAmenable_CentralCovers_ConditionalBooleanGeneration`, `SimpleAmenable_CentralCovers_FinitelyManyTranslationRelations`, `SimpleAmenable_CentralCovers_FormalCoordinates`, `SimpleAmenable_CentralCovers_FrameActions`, `SimpleAmenable_CentralCovers_GenuineFiniteGeneration`, `SimpleAmenable_CentralCovers_PairLawAssembly`, `SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration`, `SimpleAmenable_Configurations_FiveTrackGeneration`, `SimpleAmenable_Configurations_PolygonComponentStable`, `SimpleAmenable_Configurations_PolygonGroupoid`, `SimpleAmenable_Configurations_PolygonGroupoidTracks`, `SimpleAmenable_Configurations_PolygonStringGroupoid`, `SimpleAmenable_Configurations_PolygonTrackStabilizer`, `SimpleAmenable_Configurations_RepeatedTrackRouting`, `SimpleAmenable_Configurations_TrackTranslationChart`, `SimpleAmenable_Configurations_TransitiveInduction`, `SimpleAmenable_Homology_E2Descend`, `SimpleAmenable_Homology_FilteredHomology`, `SimpleAmenable_Homology_FreeChains`, `SimpleAmenable_Homology_PermutationAugmentation`, `SimpleAmenable_Homology_TransitiveCanonical`, `SimpleAmenable_Homology_WindowEnclosureChains`, `SimpleAmenable_PolygonGeometry_AlignedGroups`, `SimpleAmenable_PolygonGeometry_CanonicalSectors`, `SimpleAmenable_PolygonGeometry_CoordinateProductPatterns`, `SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates`, `SimpleAmenable_PolygonGeometry_PlaneCornerInjectivity`, `SimpleAmenable_PolygonGeometry_PolygonArea`, `SimpleAmenable_PolygonGeometry_PolygonAreaAlgebra`, `SimpleAmenable_PolygonGeometry_PolygonComponentCompletion`, `SimpleAmenable_PolygonGeometry_PolygonGridEmbedding`, `SimpleAmenable_PolygonGeometry_PolygonObjectRefinement`, `SimpleAmenable_PolygonGeometry_PolygonObjectSum`, `SimpleAmenable_PolygonGeometry_ShiftedSlots`, `SimpleAmenable_PolygonGeometry_Supported`, `SimpleAmenable_PolygonGeometry_TranslationLifts`, `SimpleAmenable_PolygonGeometry_TupleChartDomain`, `SimpleAmenable_RandomFields_FiniteCovariance`, `SimpleAmenable_Simplicial_LowerBarComposition`, `SimpleAmenable_Simplicial_PolygonMonoidalData`, `SimpleAmenable_Simplicial_PolygonPositionalMonoidal`, `SimpleAmenable_Simplicial_StageSimplicialColimit`, `SimpleAmenable_Simplicial_StageTripleHomology`, `SimpleAmenable_Simplicial_TranslationCoinvariants`, `SimpleAmenable_Simplicial_TranslationNerve`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa000`, `OAIQ65Sa001`, `OAIQ65Sa002` and `OAIQ65Sa003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa007`, `OAIQ65Sa008`, `OAIQ65Sa009`, `OAIQ65Sa013` and `OAIQ65Sa014`; the statement `OAI_SimpleAmenable_polygonFullGroup_finiteTestReiter`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa000
import Definitions.Def_OAIQ65Sa001
import Definitions.Def_OAIQ65Sa002
import Definitions.Def_OAIQ65Sa003

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TupleChartDomain
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

open scoped commutatorElement in
theorem five_cycle_commutator :
    ⁅trackCycle leftThreeInFive, trackCycle rightThreeInFive⁆ = trackCycle threeInFive := by
  decide

noncomputable def extendSlots {m : ℕ}
    (s : Fin 3 → Fin m × (CutRing × CutRing)) (k l : Fin m) (i : Fin 5) :
    Fin m × (CutRing × CutRing) :=
  if h : i.val < 3 then s ⟨i.val,h⟩ else if i.val = 3 then (k,0) else (l,0)

theorem extendSlots_three {m : ℕ}
    (s : Fin 3 → Fin m × (CutRing × CutRing)) (k l : Fin m) (i : Fin 3) :
    extendSlots s k l (threeInFive i) = s i := by
  fin_cases i <;> simp [extendSlots, threeInFive]

theorem extendSlots_injective {a m : ℕ} (U : polygonAlgebra a)
    (s : Fin 3 → Fin m × (CutRing × CutRing))
    (hs : Function.Injective (SlotMap a m U s)) (k l : Fin m)
    (hkl : k ≠ l) (hk : ∀ i, (s i).1 ≠ k) (hl : ∀ i, (s i).1 ≠ l) :
    Function.Injective (SlotMap a m U (extendSlots s k l)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have htrack := congrArg Prod.fst he
  change (extendSlots s k l i).1 = (extendSlots s k l j).1 at htrack
  have hij : i = j := by
    by_cases hi : i.val < 3
    · by_cases hj : j.val < 3
      · have hh : SlotMap a m U s (⟨i.val,hi⟩,x) =
            SlotMap a m U s (⟨j.val,hj⟩,y) := by
          simpa [SlotMap, extendSlots, hi, hj] using he
        have hh' := congrArg (fun z : Fin 3 × U.val => z.1.val) (hs hh)
        exact Fin.ext hh'
      · by_cases hj3 : j.val = 3
        · exact False.elim (hk ⟨i.val,hi⟩ (by simpa [extendSlots,hi,hj,hj3] using htrack))
        · exact False.elim (hl ⟨i.val,hi⟩ (by simpa [extendSlots,hi,hj,hj3] using htrack))
    · by_cases hj : j.val < 3
      · by_cases hi3 : i.val = 3
        · exact False.elim (hk ⟨j.val,hj⟩ (by simpa [extendSlots,hi,hj,hi3] using htrack.symm))
        · exact False.elim (hl ⟨j.val,hj⟩ (by simpa [extendSlots,hi,hj,hi3] using htrack.symm))
      · by_cases hi3 : i.val = 3 <;> by_cases hj3 : j.val = 3
        · exact Fin.ext (hi3.trans hj3.symm)
        · exact False.elim (hkl (by simpa [extendSlots,hi,hj,hi3,hj3] using htrack))
        · exact False.elim (hkl (by simpa [extendSlots,hi,hj,hi3,hj3] using htrack.symm))
        · apply Fin.ext
          omega
  subst j
  refine Prod.ext rfl ?_
  apply Subtype.ext
  exact (translation a (extendSlots s k l i).2).injective (congrArg Prod.snd he)

open scoped commutatorElement in

theorem threeSlotCycle_is_commutator {a m : ℕ} (hm : 5 ≤ m)
    {g : polygonFullGroup a m} (hg : IsThreeSlotCycle g) :
    ∃ b c : polygonFullGroup a m,
      IsThreeSlotCycle b ∧ IsThreeSlotCycle c ∧ ⁅b,c⁆ = g := by
  obtain ⟨U,s,hU,hs,hgact,hgfix⟩ := hg
  obtain ⟨k,l,hkl,hk,hl⟩ := two_spare_tracks hm (fun i => (s i).1)
  let S := extendSlots s k l
  have hS := extendSlots_injective U s hs k l hkl hk hl
  let φ := slotHom U S hS
  refine ⟨φ (trackCycle leftThreeInFive), φ (trackCycle rightThreeInFive),
    slotHom_cycle_isThreeSlotCycle U hU S hS _,
    slotHom_cycle_isThreeSlotCycle U hU S hS _, ?_⟩
  rw [← map_commutatorElement, five_cycle_commutator]
  have he (i : Fin 3) (x : U.val) :
      SlotMap a m U S (threeInFive i,x) = SlotMap a m U s (i,x) := by
    simp only [SlotMap, S, extendSlots_three]
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change slotPerm U S hS (trackCycle threeInFive) p = g.val p
  by_cases hp : p ∈ Set.range (SlotMap a m U s)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    rw [← he i x, slotPerm_apply, trackCycle_apply, he, he, hgact]
  · rw [hgfix p hp]
    by_cases hP : p ∈ Set.range (SlotMap a m U S)
    · obtain ⟨⟨j,x⟩,rfl⟩ := hP
      rw [slotPerm_apply]
      have hj : j ∉ Set.range threeInFive := by
        rintro ⟨i,rfl⟩
        exact hp ⟨(i,x),(he i x).symm⟩
      rw [trackCycle_apply_of_notMem threeInFive hj]
    · exact slotPerm_apply_of_notMem U S hS _ hP

theorem polygonAlternatingGroup_perfect (a m : ℕ) (hm : 5 ≤ m) :
    Group.IsPerfect (polygonAlternatingGroup a m) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain ⟨b,c,hb,hc,rfl⟩ := threeSlotCycle_is_commutator hm hg
  exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure hb)
    (Subgroup.subset_closure hc)

theorem shrinkingLevel_bounds (n : ℕ) :
    0 < ordinary (shrinkingLevel n) ∧ ordinary (shrinkingLevel n) < 1 := by
  have hpos : 0 < Real.goldenRatio - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hlt : Real.goldenRatio - 1 < 1 := by linarith [Real.goldenRatio_lt_two]
  simpa using And.intro (pow_pos hpos (n+1)) (pow_lt_one₀ hpos.le hlt (Nat.succ_ne_zero n))

noncomputable def shrinkingPolygon (a n : ℕ) : polygonAlgebra a :=
  ⟨halfPlane a 0 (shrinkingLevel n), BooleanSubalgebra.subset_closure ⟨0,shrinkingLevel n,rfl⟩⟩

theorem slotHom_alternating_mem {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots))
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    slotHom U slots hinj σ ∈ polygonAlternatingGroup a m := by
  have hle : alternatingGroup (Fin n) ≤
      (polygonAlternatingGroup a m).comap (slotHom U slots hinj) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    intro ρ hρ
    obtain ⟨ι,rfl⟩ := isThreeCycle_eq_trackCycle hρ
    change slotHom U slots hinj (trackCycle ι) ∈ polygonAlternatingGroup a m
    by_cases hU : U.val.Nonempty
    · exact Subgroup.subset_closure (slotHom_cycle_isThreeSlotCycle U hU slots hinj ι)
    · rw [slotHom_empty U slots hinj _ (Set.not_nonempty_iff_eq_empty.mp hU)]
      exact Subgroup.one_mem _
  exact hle hσ

end PolygonFullGroup
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_TrackTranslationChart
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

instance instFiniteSourceGeneratorLabel (m : ℕ) : Finite (SourceGeneratorLabel m) := by
  unfold SourceGeneratorLabel
  infer_instance

end PolygonFullGroup

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ConditionalBooleanGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section ConditionalBooleanGeneration

open scoped commutatorElement

theorem conditional_inter_commutator {a m : ℕ} (U V : polygonAlgebra a)
    (g h : Equiv.Perm (Fin m)) :
    conditionalHom (U ⊓ V) ⁅g,h⁆ = ⁅conditionalHom U g,conditionalHom V h⁆ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm (U ⊓ V) ⁅g,h⁆ p =
    conditionalPerm U g (conditionalPerm V h
      ((conditionalPerm U g).symm ((conditionalPerm V h).symm p)))
  obtain ⟨i,p⟩ := p
  by_cases hU : p ∈ U.val <;> by_cases hV : p ∈ V.val <;>
    simp_all [conditionalPerm,commutatorElement_def,Equiv.Perm.mul_apply]

theorem conditional_complement {a m : ℕ} (U : polygonAlgebra a)
    (g : Equiv.Perm (Fin m)) :
    conditionalHom Uᶜ g = conditionalHom (wholePolygon a) g * (conditionalHom U g)⁻¹ := by
  classical
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change conditionalPerm Uᶜ g p =
    conditionalPerm (wholePolygon a) g ((conditionalPerm U g).symm p)
  obtain ⟨i,p⟩ := p
  by_cases hp : p ∈ U.val <;> simp_all [conditionalPerm,wholePolygon]

def ConditionalAvailable {a m : ℕ} {E : Type*} [Group E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (U : polygonAlgebra a) : Prop := ∀ g, conditionalHom U (φ g) ∈ H

theorem conditionalAvailable_inter {a m : ℕ} {E : Type*} [Group E] [Group.IsPerfect E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    {U V : polygonAlgebra a} (hU : ConditionalAvailable φ H U)
    (hV : ConditionalAvailable φ H V) : ConditionalAvailable φ H (U ⊓ V) := by
  let K := H.comap ((conditionalHom (U ⊓ V)).comp φ)
  have hK : commutator E ≤ K := by
    rw [commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change conditionalHom (U ⊓ V) (φ ⁅x,y⁆) ∈ H
    rw [map_commutatorElement,conditional_inter_commutator]
    exact Subgroup.commutator_le_self H (Subgroup.commutator_mem_commutator (hU x) (hV y))
  intro x
  exact hK (Group.IsPerfect.commutator_eq_top (G := E) ▸ Subgroup.mem_top x)

theorem conditionalAvailable_compl {a m : ℕ} {E : Type*} [Group E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (hwhole : ConditionalAvailable φ H (wholePolygon a))
    {U : polygonAlgebra a} (hU : ConditionalAvailable φ H U) :
    ConditionalAvailable φ H Uᶜ := by
  intro x
  rw [conditional_complement]
  exact H.mul_mem (hwhole x) (H.inv_mem (hU x))

theorem conditionalAvailable_union {a m : ℕ} {E : Type*} [Group E] [Group.IsPerfect E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (hwhole : ConditionalAvailable φ H (wholePolygon a))
    {U V : polygonAlgebra a} (hU : ConditionalAvailable φ H U)
    (hV : ConditionalAvailable φ H V) : ConditionalAvailable φ H (U ⊔ V) := by
  have hh := conditionalAvailable_compl φ H hwhole
    (conditionalAvailable_inter φ H (conditionalAvailable_compl φ H hwhole hU)
      (conditionalAvailable_compl φ H hwhole hV))
  simpa only [compl_inf,compl_compl] using hh

noncomputable def conditionalBoolean {a m : ℕ} {E : Type*} [Group E] [Group.IsPerfect E]
    (φ : E →* Equiv.Perm (Fin m)) (H : Subgroup (polygonFullGroup a m))
    (hwhole : ConditionalAvailable φ H (wholePolygon a)) :
    BooleanSubalgebra (Set (GenericSquare a)) where
  carrier := {U | ∃ hU : U ∈ polygonAlgebra a, ConditionalAvailable φ H ⟨U,hU⟩}
  infClosed' := by
    rintro U ⟨hU,hU'⟩ V ⟨hV,hV'⟩
    exact ⟨BooleanSubalgebra.inf_mem hU hV,conditionalAvailable_inter φ H hU' hV'⟩
  supClosed' := by
    rintro U ⟨hU,hU'⟩ V ⟨hV,hV'⟩
    exact ⟨BooleanSubalgebra.sup_mem hU hV,conditionalAvailable_union φ H hwhole hU' hV'⟩
  compl_mem' := by
    rintro U ⟨hU,hU'⟩
    exact ⟨BooleanSubalgebra.compl_mem hU,conditionalAvailable_compl φ H hwhole hU'⟩
  bot_mem' := by
    refine ⟨BooleanSubalgebra.bot_mem,?_⟩
    intro x
    have he : conditionalHom (⟨∅,BooleanSubalgebra.bot_mem⟩ : polygonAlgebra a) (φ x) = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro p
      simp [conditionalHom,conditionalPerm]
    change conditionalHom (⟨∅,BooleanSubalgebra.bot_mem⟩ : polygonAlgebra a) (φ x) ∈ H
    rw [he]
    exact H.one_mem

noncomputable def sourceGenerated (a : ℕ) (r : CutRing) (m : ℕ) :
    Subgroup (polygonFullGroup a (m+1)) := Subgroup.closure (Set.range (sourceGenerator a r m))

theorem sourceGenerator_mem_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (s : SourceGeneratorLabel m) : sourceGenerator a r m s ∈ sourceGenerated a r m :=
  Subgroup.subset_closure ⟨s,rfl⟩

end ConditionalBooleanGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_BoundedRelationCover
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section BoundedRelationCover

variable (α : Type*) (L : ℕ)

instance instFiniteShortWord [Finite α] : Finite (ShortWord α L) := by
  unfold ShortWord
  infer_instance

end BoundedRelationCover

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FinitelyManyTranslationRelations
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable

def SourceCoverCentrality (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m) : Prop :=
  ∃ L : ℕ, (coverMap L (alternatingGenerator a r m hm)).ker ≤
    Subgroup.center (BoundedRelationCover L (alternatingGenerator a r m hm))

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TranslationLifts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section ActualTranslationLifts

def sourceTranslationLabel (m : ℕ) (i : Fin m × Fin 2) : SourceGeneratorLabel m := Sum.inr i

end ActualTranslationLifts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiveTrackGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FiveTrackGeneration

theorem fiveTrack_initial_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) (j : Fin 5) :
    ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) (initialTest a r j) := by
  intro g
  exact sourceGenerator_mem_generated a r m
    (Sum.inl (j,⟨fiveTrackHom ι g,fiveTrack_sign ι g,fiveTrack_support ι g⟩))

theorem fiveTrack_whole_generated (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) :
    ConditionalAvailable (fiveTrackHom ι) (sourceGenerated a r m) (wholePolygon a) :=
  fiveTrack_initial_generated a r m ι 0

noncomputable def alphabetTranslation {m : ℕ} (ι : Fin 5 ↪ Fin m)
    (b : Fin m) (u : CutRing × CutRing) : Fin m → CutRing × CutRing :=
  ∑ j : Fin 5, (Pi.single (ι j) u - Pi.single b u)

noncomputable def fiveTrackBoolean (a : ℕ) (r : CutRing) (m : ℕ)
    (ι : Fin 5 ↪ Fin (m+1)) : BooleanSubalgebra (Set (GenericSquare a)) :=
  conditionalBoolean (fiveTrackHom ι) (sourceGenerated a r m)
    (fiveTrack_whole_generated a r m ι)

end FiveTrackGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_AlignedGroups
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section AlignedGroups

variable {A H : Type*} [Group A] [Group H] {B : Type*}

theorem alignedGroup_generator (t : A →* H) (x : B → H) (P : B → Prop)
    (b : B) (hb : P b) (u : A) : t u*x b*(t u)⁻¹ ∈ alignedGroup t x P :=
  Subgroup.subset_closure ⟨b,hb,u,rfl⟩

theorem alignedGroup_input (t : A →* H) (x : B → H) (P : B → Prop)
    (b : B) (hb : P b) : x b ∈ alignedGroup t x P := by
  simpa only [map_one,inv_one,one_mul,mul_one] using alignedGroup_generator t x P b hb 1

theorem alignedGroup_conjugate (t : A →* H) (x : B → H) (P : B → Prop)
    (u : A) {y : H} (hy : y ∈ alignedGroup t x P) :
    t u*y*(t u)⁻¹ ∈ alignedGroup t x P := by
  let f : H →* H := (MulAut.conj (t u)).toMonoidHom
  have hh : alignedGroup t x P ≤ (alignedGroup t x P).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨b,hb,v,rfl⟩
    change t u*(t v*x b*(t v)⁻¹)*(t u)⁻¹ ∈ alignedGroup t x P
    have he : t u*(t v*x b*(t v)⁻¹)*(t u)⁻¹ = t (u*v)*x b*(t (u*v))⁻¹ := by
      rw [map_mul]; group
    rw [he]
    exact alignedGroup_generator t x P b hb (u*v)
  exact hh hy

end AlignedGroups

section SourceAlignedGroups

instance instFiniteSmallConditional (m : ℕ) : Finite (SmallConditional m) := by unfold SmallConditional; infer_instance

end SourceAlignedGroups

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_Supported
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

instance instTopologicalSpaceGenericSquare (a : ℕ) : TopologicalSpace (GenericSquare a) := inferInstanceAs
  (TopologicalSpace {p : ℝ × ℝ // p.1 ∈ Set.Ico 0 1 ∧ p.2 ∈ Set.Ico 0 1 ∧ AvoidsCuts a p})

instance instMetricSpaceGenericSquare (a : ℕ) : MetricSpace (GenericSquare a) := inferInstanceAs
  (MetricSpace {p : ℝ × ℝ // p.1 ∈ Set.Ico 0 1 ∧ p.2 ∈ Set.Ico 0 1 ∧ AvoidsCuts a p})

noncomputable def smallSquare (a : ℕ) (d : CutRing) : polygonAlgebra a :=
  ⟨halfPlane a 0 d ∩ halfPlane a 1 d,
    BooleanSubalgebra.inf_mem (halfPlane_mem a 0 d) (halfPlane_mem a 1 d)⟩

noncomputable def fiveRectangleShifts (l : CutRing × CutRing) (d : CutRing)
    (i : Fin 5) : CutRing × CutRing := (l.1 + 2 * (i.val : CutRing)*d, l.2)

theorem slots_injective_of_tracks {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (h : Function.Injective (fun i => (s i).1)) :
    Function.Injective (SlotMap a m U s) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have htrack : (s i).1 = (s j).1 := congrArg (fun p : TrackPoint a m => p.1) he
  have hij := h htrack
  subst j
  refine Prod.ext rfl ?_
  apply Subtype.ext
  exact (translation a (s i).2).injective (congrArg Prod.snd he)

end LocalDisplacement
end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PrimitiveGeometricGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PrimitiveGeometricGeneration

theorem mem_circularBoxPiece {a : ℕ} (r : CutRing) (k : Fin 2 × Fin 2)
    (p : GenericSquare a) : p ∈ (circularBoxPiece a r k).val ↔
    (-ordinary r ≤ p.val.1-k.1.val ∧ p.val.1-k.1.val < ordinary r) ∧
    (-ordinary r ≤ p.val.2-k.2.val ∧ p.val.2-k.2.val < ordinary r) := by
  simp only [circularBoxPiece,Set.mem_inter_iff,Set.mem_compl_iff,halfPlane,
    Set.mem_ofPred_eq,not_lt,cutForm,Matrix.cons_val_zero,Matrix.cons_val_one,
    map_add,map_neg,map_natCast]
  constructor <;> rintro ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩ <;> constructor <;> constructor <;> linarith

end PrimitiveGeometricGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_ShiftedSlots
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

theorem subslots_injective {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (ι : Fin 3 ↪ Fin n) : Function.Injective (SlotMap a m U (s ∘ ι)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  change SlotMap a m U s (ι i,x) = SlotMap a m U s (ι j,y) at he
  have he' := hs he
  exact Prod.ext (ι.injective (congrArg Prod.fst he')) (congrArg (fun p : Fin n × U.val => p.2) he')

noncomputable def shiftedSlots {m n : ℕ} (u : CutRing × CutRing)
    (s : Fin n → Fin m × (CutRing × CutRing)) : Fin n → Fin m × (CutRing × CutRing) :=
  fun i => ((s i).1,(s i).2-u)

end LocalDisplacement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_GenuineFiniteGeneration
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section GenuineFiniteGeneration

noncomputable def offsetFrame {m n : ℕ} (s : Fin n ↪ Fin m) (b : Fin m)
    (u : Fin n → CutRing × CutRing) : Fin m → CutRing × CutRing :=
  ∑ i, (Pi.single (s i) (u i) - Pi.single b (u i))

def starThreeInFive (i : Fin 3) : Fin 3 ↪ Fin 5 :=
  ⟨![threeInFive i,3,4],by fin_cases i <;> decide⟩

end GenuineFiniteGeneration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CanonicalSectors
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section CanonicalSectors
open scoped commutatorElement

variable {E H Q : Type*} [Group E] [Group H] [Group Q]

variable {Ω : Type*}

variable [Group.IsPerfect E]

noncomputable def centralSector (φ : (Ω → E) →* H ⧸ Subgroup.center H) (U : Set Ω) :
    UniversalExtension E →* H :=
  universalLift (QuotientGroup.mk' (Subgroup.center H))
    (QuotientGroup.mk'_surjective (Subgroup.center H))
    (by rw [QuotientGroup.ker_mk']) (φ.comp (sectorMask U))

def assignmentProjection : (Ω → UniversalExtension E) →* (Ω → E) where
  toFun s ω := universalProjection E (s ω)
  map_one' := by ext ω; exact map_one _
  map_mul' s t := by ext ω; exact map_mul _ _ _

end CanonicalSectors

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteCovariance
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section SourceConstantCovariance

variable (a : ℕ) (r : CutRing) (m : ℕ) (hm : 2 ≤ m)

noncomputable def reindexSmallConditional (s : alternatingGroup (Fin (m+1)))
    (b : SmallConditional m) : SmallConditional m :=
  (b.1,⟨s.val*b.2.val*s.val⁻¹, (alternatingGroup (Fin (m+1))).mul_mem
    ((alternatingGroup (Fin (m+1))).mul_mem s.property b.2.property.1)
    ((alternatingGroup (Fin (m+1))).inv_mem s.property),
    by simpa only [Equiv.Perm.card_support_conj] using b.2.property.2⟩)

@[simp] theorem reindexSmallConditional_support (s : alternatingGroup (Fin (m+1)))
    (b : SmallConditional m) :
    (reindexSmallConditional m s b).2.val.support = b.2.val.support.map s.val.toEmbedding :=
  Equiv.Perm.support_conj

end SourceConstantCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_CompiledTranslations
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section CompiledTranslations

noncomputable def latticeWord {m : ℕ}
    (k : Multiplicative (FreeAbelianGroup (Fin m × Fin 2))) :
    FreeGroup (SourceGeneratorLabel m) :=
  FreeGroup.map (sourceTranslationLabel m)
    (translationWordMap_surjective k).choose

end CompiledTranslations

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_ConcurrentDenominators
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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

section VertexResidues

noncomputable def cutResidue (D : ℕ) (z : CutRing) : CutRing :=
  ⟨z.re % (D : ℤ),z.im % (D : ℤ)⟩
noncomputable def cutQuotient (D : ℕ) (z : CutRing) : CutRing :=
  ⟨z.re / (D : ℤ),z.im / (D : ℤ)⟩

noncomputable def finiteCutResidue (D : ℕ) (t : Fin D × Fin D) : CutRing :=
  ⟨t.1.val,t.2.val⟩

noncomputable def vertexRepresentative (D : ℕ)
    (t : (Fin D × Fin D) × (Fin D × Fin D)) : ℝ × ℝ :=
  (ordinary (finiteCutResidue D t.1)/(D : ℝ),ordinary (finiteCutResidue D t.2)/(D : ℝ))

end VertexResidues

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_WindowEnclosureChains
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section WindowEnclosureChains

structure WindowBracket (n : ℕ) (q : ℤ) (t : ℝ) where
  lower : CutRing
  upper : CutRing
  lower_label : q ≤ endpointLabel lower ∧ endpointLabel lower < q+n
  upper_label : q ≤ endpointLabel upper ∧ endpointLabel upper < q+n
  lower_bound : t-201/(n:ℝ) ≤ ordinary lower
  lower_lt : ordinary lower < t
  upper_lt : t < ordinary upper
  upper_bound : ordinary upper ≤ t+201/(n:ℝ)

end WindowEnclosureChains

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_PairLawAssembly
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PairLawAssembly
variable {G E ι : Type*} [Group G] [Group E]

variable [Fintype ι]
variable (A B : ι → Subgroup G) (h : ∀ i, CommutingFactors (A i) (B i))
    (hz : Subgroup.center G = ⊥)

@[simp] theorem simultaneousAssignmentMap_whole (c : E →* G) :
    (simultaneousAssignmentMap A B h hz c).comp (sectorMask Set.univ) = c := by
  ext s
  change refinementEquiv A B h hz
    (fun σ => refinementSource A B h hz c σ (sectorMask Set.univ s σ)) = c s
  simp only [sectorMask_of_mem _ _ _ (Set.mem_univ _)]
  exact (refinementEquiv A B h hz).apply_symm_apply (c s)

end PairLawAssembly

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FormalCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FormalCoordinates
variable {S Q Ω : Type*} [Group S] [Group Q] [DecidableEq Ω]

theorem coordinateFactors (φ : (Ω → S) →* Q) (hφ : Function.Surjective φ) (ω : Ω) :
    CommutingFactors ((φ.comp (MonoidHom.mulSingle (fun _ : Ω => S) ω)).range)
      ((φ.comp (assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω})).range) := by
  classical
  constructor
  · rintro x ⟨s,rfl⟩ y ⟨t,rfl⟩
    change Commute (φ (Pi.mulSingle ω s)) (φ (assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω} t))
    apply Commute.map _ φ
    ext ν
    by_cases hν : ν = ω
    · subst ν; simp [assignmentRestriction]
    · simp [assignmentRestriction,hν]
  · intro x
    obtain ⟨s,rfl⟩ := hφ x
    refine ⟨φ (Pi.mulSingle ω (s ω)),⟨s ω,rfl⟩,
      φ (assignmentRestriction (fun _ : Ω => S) {ν | ν ≠ ω} s),⟨s,rfl⟩,?_⟩
    rw [← map_mul]
    congr 1
    ext ν
    by_cases hν : ν = ω
    · subst ν; simp [assignmentRestriction]
    · simp [assignmentRestriction,hν]

noncomputable def coordinateProjection (φ : (Ω → S) →* Q) (hφ : Function.Surjective φ)
    (hz : Subgroup.center Q = ⊥) (ω : Ω) : Q →* Q :=
  (coordinateFactors φ hφ ω).projectLeft hz

end FormalCoordinates

section StarFormalComponents
variable {E S G ι κ Ω : Type*} [Group E] [Group S] [Group G]
    [Finite ι] [DecidableEq (ι → Bool)] [Group.IsPerfect G]
    (π : E →* S) (c : S →* G) (F : Option ι → E →* G)
    (hc : F none = c.comp π)
    (φ : ((ι → Bool) → S) →* (G ⧸ Subgroup.center G))
    (hφ : Function.Surjective φ)
    (hφc : φ.comp (sectorMask Set.univ) = (QuotientGroup.mk' _).comp c)
    (hφi : ∀ i, (φ.comp (sectorMask {σ | σ i = true})).comp π =
      (QuotientGroup.mk' _).comp (F (some i)))

noncomputable def formalCoordinateMap (σ : ι → Bool) : G →* (G ⧸ Subgroup.center G) :=
  (coordinateProjection φ hφ perfect_center_quotient σ).comp (QuotientGroup.mk' _)

end StarFormalComponents

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_CoordinateProductPatterns
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section CoordinateProductPatterns

def genericSwap {a : ℕ} (p : GenericSquare a) : GenericSquare a :=
  ⟨p.val.swap,p.property.2.1,p.property.1,by
    intro j z
    fin_cases j
    · exact p.property.2.2 1 z
    · exact p.property.2.2 0 z
    · exact p.property.2.2 3 z
    · exact p.property.2.2 2 z⟩

end CoordinateProductPatterns

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_FrameActions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FrameActions

variable {P H Q : Type*} [Group P] [Group H] [Group Q]

theorem CentralOn.commute_perfect [Group.IsPerfect P] (q : H →* Q) (S : Subgroup H)
    (h : CentralOn q S) (f : P →* H) (hf : f.range ≤ S) (z : H) (hz : z ∈ S)
    (hc : ∀ s, Commute (q z) (q (f s))) (s : P) : Commute z (f s) := by
  have he : (MulAut.conj z).toMonoidHom.comp f = f := by
    apply CentralOn.lift_unique q S h
    · rintro x ⟨s,rfl⟩
      exact S.mul_mem (S.mul_mem hz (hf ⟨s,rfl⟩)) (S.inv_mem hz)
    · exact hf
    · ext s : 1
      change q (z*f s*z⁻¹)=q (f s)
      rw [map_mul,map_mul,map_inv,(hc s).eq,mul_assoc,mul_inv_cancel,mul_one]
  have hh := DFunLike.congr_fun he s
  change z*f s*z⁻¹=f s at hh
  have hh' := congrArg (fun x => x*z) hh
  exact show z*f s=f s*z from by simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh'

end FrameActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_RepeatedTrackRouting
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

theorem exists_privateRoutingBank {m : ℕ} (i : Fin 5 → Fin m) (J : Finset (Fin m))
    (hreserve : 20 ≤ ((Finset.univ : Finset (Fin m)) \
      (J ∪ Finset.univ.image i)).card) :
    ∃ P : PrivateRoutingBank i, ∀ j k, k≠0 → P.row j k ∉ J := by
  classical
  let R := (Finset.univ : Finset (Fin m)) \ (J ∪ Finset.univ.image i)
  have hc : Fintype.card (Fin 5 × {k : Fin 5 // k≠0}) ≤ Fintype.card R := by
    have hfour : Fintype.card {k : Fin 5 // k≠0}=4 := by decide
    rw [Fintype.card_prod,Fintype.card_fin,hfour,Fintype.card_coe]
    exact hreserve
  obtain ⟨p⟩ := Function.Embedding.nonempty_of_card_le hc
  let f : Fin 5 → Fin 5 → Fin m := fun j k =>
    if hk : k=0 then i j else (p (j,⟨k,hk⟩)).val
  have hfresh : ∀ j k hk l, (p (j,⟨k,hk⟩)).val ≠ i l := by
    intro j k hk l he
    exact (Finset.mem_sdiff.mp (p (j,⟨k,hk⟩)).property).2
      (Finset.mem_union_right _ (he.symm ▸ Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩))
  have hinj : ∀ j, Function.Injective (f j) := by
    intro j k l he
    by_cases hk : k=0 <;> by_cases hl : l=0
    · exact hk.trans hl.symm
    · subst k
      have hh : i j=(p (j,⟨l,hl⟩)).val := by simpa [f,hl] using he
      exact (hfresh j l hl j hh.symm).elim
    · subst l
      have hh : (p (j,⟨k,hk⟩)).val=i j := by simpa [f,hk] using he
      exact (hfresh j k hk j hh).elim
    · have he' : p (j,⟨k,hk⟩)=p (j,⟨l,hl⟩) :=
        Subtype.ext (by simpa only [f,dite_eq_right hk,dite_eq_right hl] using he)
      have hh := p.injective he'
      exact congrArg (fun q : Fin 5 × {k : Fin 5 // k≠0} => q.2.val) hh
  let P : PrivateRoutingBank i := {
    row := fun j => ⟨f j,hinj j⟩
    source := by intro j; simp [f]
    fresh := by
      intro j k hk l
      exact (show f j k≠i l from by simpa [f,hk] using hfresh j k hk l)
    separate := by
      intro j k j' k' hk hk' he
      change f j k=f j' k' at he
      have he' : p (j,⟨k,hk⟩)=p (j',⟨k',hk'⟩) :=
        Subtype.ext (by simpa only [f,dite_eq_right hk,dite_eq_right hk'] using he)
      have hh := p.injective he'
      exact ⟨congrArg Prod.fst hh,congrArg (fun q : Fin 5 × {k : Fin 5 // k≠0} => q.2.val) hh⟩ }
  refine ⟨P,?_⟩
  intro j k hk hJ
  have hh : (p (j,⟨k,hk⟩)).val ∈ J := by simpa [P,f,hk] using hJ
  exact (Finset.mem_sdiff.mp (p (j,⟨k,hk⟩)).property).2 (Finset.mem_union_left _ hh)

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonGroupoid
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open Classical Set _root_.CategoryTheory

structure PolygonObject (a : ℕ) where
  tracks : ℕ
  cell : Fin tracks → polygonAlgebra a

namespace PolygonObject
variable {a : ℕ}

abbrev Point (U : PolygonObject a) := {x : TrackPoint a U.tracks // x.2 ∈ (U.cell x.1).val}

structure Chart (m n : ℕ) where
  source : Fin m
  target : Fin n
  shift : CutRing × CutRing
  domain : polygonAlgebra a

namespace Chart
variable {U V W : PolygonObject a}

def Holds (c : Chart (a:=a) U.tracks V.tracks) (f : U.Point → V.Point) : Prop :=
  ∀ x∈c.domain.val, ∃hx : x∈(U.cell c.source).val,
    (f ⟨(c.source,x),hx⟩).val=(c.target,translate a c.shift x)

def Contains (c : Chart (a:=a) U.tracks V.tracks) (x : U.Point) : Prop :=
  x.val.1=c.source ∧ x.val.2∈c.domain.val

noncomputable def comp (c : Chart (a:=a) V.tracks W.tracks)
    (d : Chart (a:=a) U.tracks V.tracks) : Chart (a:=a) U.tracks W.tracks :=
  ⟨d.source,c.target,c.shift+d.shift,
    ⟨d.domain.val ∩ translate a d.shift ⁻¹' c.domain.val,
      BooleanSubalgebra.inf_mem d.domain.property (polygon_preimage_translate d.shift c.domain.property)⟩⟩

theorem comp_holds {c : Chart (a:=a) V.tracks W.tracks}
    {d : Chart (a:=a) U.tracks V.tracks} {f : V.Point → W.Point} {g : U.Point → V.Point}
    (hc : c.Holds f) (hd : d.Holds g) (hmatch : c.source=d.target) :
    (c.comp d).Holds (f ∘ g) := by
  rintro x ⟨hx,hcx⟩
  obtain ⟨hu,he⟩ := hd x hx
  obtain ⟨hv,hf⟩ := hc (translate a d.shift x) hcx
  refine ⟨hu,?_⟩
  have hp : g ⟨(d.source,x),hu⟩=⟨(c.source,translate a d.shift x),hv⟩ := by
    apply Subtype.ext
    simpa only [hmatch] using he
  change (f (g ⟨(d.source,x),hu⟩)).val=(c.target,translate a (c.shift+d.shift) x)
  rw [hp,hf,translate_add]

noncomputable def inverse (c : Chart (a:=a) U.tracks V.tracks) :
    Chart (a:=a) V.tracks U.tracks :=
  ⟨c.target,c.source,-c.shift,
    ⟨translation a c.shift '' c.domain.val,polygon_image_translation _ c.domain.property⟩⟩

theorem inverse_holds (f : U.Point ≃ V.Point) {c : Chart (a:=a) U.tracks V.tracks}
    (hc : c.Holds f) : c.inverse.Holds f.symm := by
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨hu,he⟩ := hc x hx
  have hv : translate a c.shift x∈(V.cell c.target).val := by
    have h := (f ⟨(c.source,x),hu⟩).property
    rw [he] at h
    exact h
  refine ⟨hv,?_⟩
  have hp : (⟨(c.target,translate a c.shift x),hv⟩ : V.Point)=f ⟨(c.source,x),hu⟩ :=
    Subtype.ext he.symm
  change (f.symm ⟨(c.target,translate a c.shift x),hv⟩).val =
    (c.source,translate a (-c.shift) (translate a c.shift x))
  rw [hp,f.symm_apply_apply,←translate_add,neg_add_cancel,translate_zero]

end Chart

def HasTable {U V : PolygonObject a} (f : U.Point → V.Point) : Prop :=
  ∃s : Finset (Chart (a:=a) U.tracks V.tracks),
    (∀c∈s,c.Holds f) ∧ ∀x,∃c∈s,c.Contains x

theorem identity_hasTable (U : PolygonObject a) : HasTable (id : U.Point → U.Point) := by
  let c : Fin U.tracks → Chart (a:=a) U.tracks U.tracks := fun i => ⟨i,i,0,U.cell i⟩
  refine ⟨Finset.univ.image c,?_,?_⟩
  · intro d hd
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hd
    intro x hx
    exact ⟨hx,by change (i,x)=(i,translate a 0 x); rw [translate_zero]⟩
  · intro x
    exact ⟨c x.val.1,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl,x.property⟩

theorem comp_hasTable {U V W : PolygonObject a} {f : V.Point → W.Point} {g : U.Point → V.Point}
    (hf : HasTable f) (hg : HasTable g) : HasTable (f ∘ g) := by
  obtain ⟨s,hs,hcover⟩ := hf
  obtain ⟨t,ht,tcover⟩ := hg
  let pairs := (s×ˢt).filter (fun cd => cd.1.source=cd.2.target)
  refine ⟨pairs.image (fun cd => cd.1.comp cd.2),?_,?_⟩
  · intro e he
    obtain ⟨⟨c,d⟩,hcd,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hmem,hmatch⟩ := Finset.mem_filter.mp hcd
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hmem
    exact Chart.comp_holds (hs c hc) (ht d hd) hmatch
  · intro x
    obtain ⟨d,hd,hx⟩ := tcover x
    obtain ⟨c,hc,hgx⟩ := hcover (g x)
    obtain ⟨hu,he⟩ := ht d hd x.val.2 hx.2
    have hxval : (⟨(d.source,x.val.2),hu⟩ : U.Point)=x := by
      apply Subtype.ext
      exact Prod.ext hx.1.symm rfl
    rw [hxval] at he
    have hmatch : c.source=d.target := by
      change (g x).val.1=c.source ∧ (g x).val.2∈c.domain.val at hgx
      rw [he] at hgx
      exact hgx.1.symm
    refine ⟨c.comp d,Finset.mem_image.mpr ⟨(c,d),?_,rfl⟩,hx.1,hx.2,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,hd⟩,hmatch⟩
    · change translate a d.shift x.val.2∈c.domain.val
      simpa only [he] using hgx.2

theorem inverse_hasTable {U V : PolygonObject a} (f : U.Point ≃ V.Point)
    (hf : HasTable f) : HasTable f.symm := by
  obtain ⟨s,hs,hcover⟩ := hf
  refine ⟨s.image Chart.inverse,?_,?_⟩
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    exact Chart.inverse_holds f (hs d hd)
  · intro y
    obtain ⟨c,hc,hx⟩ := hcover (f.symm y)
    obtain ⟨hu,he⟩ := hs c hc (f.symm y).val.2 hx.2
    have hp : (⟨(c.source,(f.symm y).val.2),hu⟩ : U.Point)=f.symm y := by
      apply Subtype.ext
      exact Prod.ext hx.1.symm rfl
    rw [hp,f.apply_symm_apply] at he
    refine ⟨c.inverse,Finset.mem_image.mpr ⟨c,hc,rfl⟩,?_,?_⟩
    · exact congrArg Prod.fst he
    · exact ⟨(f.symm y).val.2,hx.2,(congrArg Prod.snd he).symm⟩

structure Arrow (U V : PolygonObject a) where
  toEquiv : U.Point ≃ V.Point
  hasTable : HasTable toEquiv

@[ext] theorem Arrow.ext {U V : PolygonObject a} {f g : Arrow U V}
    (h : f.toEquiv=g.toEquiv) : f=g := by
  cases f; cases g; cases h; rfl

noncomputable instance instGroupoid : Groupoid (PolygonObject a) where
  Hom := Arrow
  id U := ⟨Equiv.refl _,identity_hasTable U⟩
  comp f g := ⟨f.toEquiv.trans g.toEquiv,comp_hasTable (f:=g.toEquiv) (g:=f.toEquiv) g.hasTable f.hasTable⟩
  id_comp f := Arrow.ext rfl
  comp_id f := Arrow.ext rfl
  assoc f g h := Arrow.ext rfl
  inv f := ⟨f.toEquiv.symm,inverse_hasTable f.toEquiv f.hasTable⟩
  inv_comp f := by apply Arrow.ext; exact Equiv.symm_trans_self _
  comp_inv f := by apply Arrow.ext; exact Equiv.self_trans_symm _

def Positional {U V : PolygonObject a} (f : U ⟶ V) : Prop :=
  ∀x,(f.toEquiv x).val.2=x.val.2

noncomputable def positionalSubgroupoid (a : ℕ) : Subgroupoid (PolygonObject a) where
  arrows U V := {f | Positional f}
  inv := by
    intro U V f hf y
    change (f.toEquiv.symm y).val.2=y.val.2
    have h := hf (f.toEquiv.symm y)
    simpa using h.symm
  mul := by
    intro U V W f hf g hg x
    exact (hg (f.toEquiv x)).trans (hf x)

theorem identity_positional (U : PolygonObject a) : Positional (𝟙 U) := fun _ => rfl

end PolygonObject

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonArea
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonArea
open Classical Set MeasureTheory

theorem continuous_cutForm (a : ℕ) (j : Fin 4) : Continuous (cutForm a j) := by
  change Continuous (fun p => cutForm a j p)
  fin_cases j <;> dsimp [cutForm] <;> fun_prop

theorem volume_cut_level (a : ℕ) (j : Fin 4) (r : ℝ) :
    volume {p : ℝ×ℝ | cutForm a j p=r}=0 := by
  have hm : MeasurableSet {p : ℝ×ℝ | cutForm a j p=r} :=
    (continuous_cutForm a j).measurable (measurableSet_singleton r)
  change ((volume : Measure ℝ).prod volume) _=0
  fin_cases j
  · rw [Measure.prod_apply_symm hm]
    simp [cutForm]
  · rw [Measure.prod_apply hm]
    simp [cutForm]
  · rw [Measure.prod_apply hm]
    have hy (x : ℝ) : {y : ℝ | y-Real.goldenRatio^a*x=r}={r+Real.goldenRatio^a*x} := by
      ext y
      simp only [mem_ofPred_eq,mem_singleton_iff]
      constructor <;> intro h <;> linarith
    simp only [cutForm,Set.preimage]
    simp [hy]
  · rw [Measure.prod_apply_symm hm]
    have hx (y : ℝ) : {x : ℝ | x-Real.goldenRatio^a*y=r}={r+Real.goldenRatio^a*y} := by
      ext x
      simp only [mem_ofPred_eq,mem_singleton_iff]
      constructor <;> intro h <;> linarith
    simp only [cutForm,Set.preimage]
    simp [hx]

end PolygonArea

section PolygonJordan
open Classical Set MeasureTheory
namespace PolygonArea

theorem null_frontier_cut (a : ℕ) (j : Fin 4) (r : ℝ) :
    volume (frontier {p : ℝ×ℝ | cutForm a j p < r})=0 := by
  have h := (continuous_cutForm a j).frontier_preimage_subset (Iio r)
  rw [frontier_Iio] at h
  exact measure_mono_null h (volume_cut_level a j r)

theorem null_frontier_square : volume (frontier square)=0 := by
  have hcoord (j : Fin 4) : volume (frontier (cutForm 0 j ⁻¹' Ico (0:ℝ) 1))=0 := by
    apply measure_mono_null ((continuous_cutForm 0 j).frontier_preimage_subset _)
    rw [frontier_Ico (by norm_num : (0:ℝ)<1)]
    have he : cutForm 0 j ⁻¹' ({0,1} : Set ℝ)=
        {p | cutForm 0 j p=0}∪{p | cutForm 0 j p=1} := by ext p; simp
    rw [he]
    exact measure_union_null (volume_cut_level 0 j 0) (volume_cut_level 0 j 1)
  exact null_frontier_inter (hcoord 0) (hcoord 1)

theorem representative {a : ℕ} {U : Set (GenericSquare a)} (hU : U∈polygonAlgebra a) :
    ∃S : Set (ℝ×ℝ), S⊆square ∧ MeasurableSet S ∧ volume (frontier S)=0 ∧
      ∀x : GenericSquare a,x∈U ↔ x.val∈S := by
  apply polygon_induction (P:=fun U => ∃S : Set (ℝ×ℝ), S⊆square ∧ MeasurableSet S ∧
    volume (frontier S)=0 ∧ ∀x : GenericSquare a,x∈U ↔ x.val∈S) ?_ ?_ ?_ ?_ hU
  · intro j z
    refine ⟨square∩{p | cutForm a j p<ordinary z},Set.inter_subset_left,?_,
      null_frontier_inter null_frontier_square (null_frontier_cut a j (ordinary z)),?_⟩
    · exact (measurableSet_Ico.prod measurableSet_Ico).inter
        (isOpen_lt (continuous_cutForm a j) continuous_const).measurableSet
    · intro x
      change cutForm a j x.val<ordinary z ↔ x.val∈square ∧ cutForm a j x.val<ordinary z
      exact ⟨fun hx => ⟨⟨x.property.1,x.property.2.1⟩,hx⟩,And.right⟩
  · exact ⟨∅,Set.empty_subset _,MeasurableSet.empty,by simp,by simp⟩
  · intro U V hU hV
    obtain ⟨S,hS,hmS,hbS,heS⟩ := hU
    obtain ⟨T,hT,hmT,hbT,heT⟩ := hV
    exact ⟨S∪T,Set.union_subset hS hT,hmS.union hmT,null_frontier_union hbS hbT,
      fun x => or_congr (heS x) (heT x)⟩
  · intro U hU
    obtain ⟨S,hS,hmS,hbS,heS⟩ := hU
    refine ⟨square\S,Set.sdiff_subset,(measurableSet_Ico.prod measurableSet_Ico).diff hmS,
      null_frontier_diff null_frontier_square hbS,?_⟩
    intro x
    change x∉U ↔ x.val∈square ∧ x.val∉S
    exact ⟨fun hx => ⟨⟨x.property.1,x.property.2.1⟩,fun hs => hx ((heS x).mpr hs)⟩,
      fun hx hu => hx.2 ((heS x).mp hu)⟩

noncomputable def area {a : ℕ} (U : polygonAlgebra a) : ENNReal :=
  volume (Subtype.val '' U.val)

theorem image_eq_rep {a : ℕ} (U : polygonAlgebra a) {S : Set (ℝ×ℝ)}
    (hS : S⊆square) (he : ∀x : GenericSquare a,x∈U.val ↔ x.val∈S) :
    Subtype.val '' U.val=S∩{p | AvoidsCuts a p} := by
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(he x).mp hx,x.property.2.2⟩
  · rintro ⟨hp,hcut⟩
    have hsq := hS hp
    exact ⟨⟨p,hsq.1,hsq.2,hcut⟩,(he _).mpr hp,rfl⟩

end PolygonArea
end PolygonJordan

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonAreaAlgebra
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonAreaAlgebra

open Classical Set MeasureTheory
namespace PolygonArea

@[simp] theorem area_bot (a : ℕ) : area (⊥ : polygonAlgebra a)=0 := by
  change volume ((fun point : GenericSquare a => point.val) '' (∅ : Set (GenericSquare a)))=0
  simp

theorem area_mono {a : ℕ} {U V : polygonAlgebra a} (h : U≤V) : area U≤area V :=
  measure_mono (Set.image_mono h)

theorem area_sup_le {a : ℕ} (U V : polygonAlgebra a) : area (U⊔V)≤area U+area V := by
  change volume ((fun point : GenericSquare a => point.val) '' (U.val∪V.val))≤_
  rw [Set.image_union]
  exact measure_union_le _ _

theorem area_finset_sup_le {a : ℕ} {ι : Type*} (s : Finset ι) (f : ι → polygonAlgebra a) :
    area (s.sup f)≤∑i∈s,area (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    exact (area_sup_le _ _).trans (add_le_add le_rfl ih)

end PolygonArea
end PolygonAreaAlgebra

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonGridEmbedding
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonGridEmbedding
open Classical Set
namespace PolygonGrid

noncomputable def rectangle (a : ℕ) (r : CutRing) (i j : ℕ) : polygonAlgebra a :=
  ⟨(halfPlane a 0 (r*(i+1)) ∩ (halfPlane a 0 (r*i))ᶜ) ∩
    (halfPlane a 1 (r*(j+1)) ∩ (halfPlane a 1 (r*j))ᶜ),
    BooleanSubalgebra.inf_mem
      (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))
      (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))⟩

@[simp] theorem mem_rectangle (a : ℕ) (r : CutRing) (i j : ℕ) (x : GenericSquare a) :
    x∈(rectangle a r i j).val ↔
      x.val.1∈interval (ordinary r) i ∧ x.val.2∈interval (ordinary r) j := by
  simp only [rectangle,halfPlane,interval,Set.mem_inter_iff,Set.mem_compl_iff,
    Set.mem_ofPred_eq,Set.mem_Ico,cutForm,Matrix.cons_val_zero,Matrix.cons_val_one,
    map_mul,map_add,map_natCast,map_one,not_lt]
  tauto

noncomputable def displacement {m N : ℕ} (r : CutRing) (i j : Index m N) : CutRing×CutRing :=
  (r*((j.2.1.val:CutRing)-i.2.1.val),r*((j.2.2.val:CutRing)-i.2.2.val))

theorem displacement_mem_cell {m N : ℕ} (r : CutRing) (i j : Index m N)
    {x : ℝ×ℝ} (hx : (i.1.val,x)∈cell (ordinary r) i) :
    (j.1.val,x+(ordinary (displacement r i j).1,ordinary (displacement r i j).2))∈
      cell (ordinary r) j := by
  refine ⟨rfl,?_,?_⟩
  · have hxi := hx.2.1
    change ordinary r*i.2.1.val ≤ x.1 ∧ x.1 < ordinary r*(i.2.1.val+1) at hxi
    change ordinary r*j.2.1.val ≤ x.1+ordinary (displacement r i j).1 ∧
      x.1+ordinary (displacement r i j).1 < ordinary r*(j.2.1.val+1)
    simp only [displacement,map_mul,map_sub,map_natCast]
    constructor <;> nlinarith [hxi.1,hxi.2]
  · have hxi := hx.2.2
    change ordinary r*i.2.2.val ≤ x.2 ∧ x.2 < ordinary r*(i.2.2.val+1) at hxi
    change ordinary r*j.2.2.val ≤ x.2+ordinary (displacement r i j).2 ∧
      x.2+ordinary (displacement r i j).2 < ordinary r*(j.2.2.val+1)
    simp only [displacement,map_mul,map_sub,map_natCast]
    constructor <;> nlinarith [hxi.1,hxi.2]

theorem translate_displacement_mem {a m N : ℕ} (r : CutRing) (i j : Index m N)
    {x : GenericSquare a} (hx : (i.1.val,x.val)∈cell (ordinary r) i)
    (hj : cell (ordinary r) j⊆region m) :
    (j.1.val,(translate a (displacement r i j) x).val)∈cell (ordinary r) j := by
  have hd := displacement_mem_cell r i j hx
  have hs := hj hd
  have he : (translate a (displacement r i j) x).val =
      x.val+(ordinary (displacement r i j).1,ordinary (displacement r i j).2) := by
    apply Prod.ext
    · exact Int.fract_eq_self.mpr hs.2.1
    · exact Int.fract_eq_self.mpr hs.2.2
  rwa [he]

theorem exists_grid_side {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ, 0 < ordinary (shrinkingLevel b) ∧ ordinary (shrinkingLevel b)<δ := by
  have hp : 0 < Real.goldenRatio-1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hlt : Real.goldenRatio-1<1 := by linarith [Real.goldenRatio_lt_two]
  obtain ⟨b,hb⟩ := exists_pow_lt_of_lt_one hδ hlt
  refine ⟨b,(shrinkingLevel_bounds b).1,?_⟩
  rw [ordinary_shrinkingLevel,pow_succ]
  exact (mul_le_of_le_one_right (pow_nonneg hp.le _) hlt.le).trans_lt hb

end PolygonGrid
end PolygonGridEmbedding

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonTrackStabilizer
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonTrackStabilizer
open Classical Set

namespace PolygonTracks
variable {a k n : ℕ}
noncomputable def join (a k n : ℕ) :
    TrackPoint a k ⊕ TrackPoint a n ≃ TrackPoint a (k+n) :=
  (Equiv.sumProdDistrib (Fin k) (Fin n) (GenericSquare a)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl _))

@[simp] theorem join_inl (x : TrackPoint a k) : join a k n (.inl x)=(x.1.castAdd n,x.2) := rfl
@[simp] theorem join_inr (x : TrackPoint a n) : join a k n (.inr x)=(x.1.natAdd k,x.2) := rfl
@[simp] theorem join_symm_left (x : TrackPoint a k) :
    (join a k n).symm (x.1.castAdd n,x.2)=.inl x := (join a k n).symm_apply_apply (.inl x)
@[simp] theorem join_symm_right (x : TrackPoint a n) :
    (join a k n).symm (x.1.natAdd k,x.2)=.inr x := (join a k n).symm_apply_apply (.inr x)

noncomputable def blockPerm (k : ℕ) (f : Equiv.Perm (TrackPoint a n)) :
    Equiv.Perm (TrackPoint a (k+n)) :=
  (join a k n).symm.trans (((Equiv.refl _).sumCongr f).trans (join a k n))

@[simp] theorem blockPerm_left (f : Equiv.Perm (TrackPoint a n)) (x : TrackPoint a k) :
    blockPerm k f (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2) := by
  simp [blockPerm]

@[simp] theorem blockPerm_right (f : Equiv.Perm (TrackPoint a n)) (x : TrackPoint a n) :
    blockPerm k f (x.1.natAdd k,x.2)=((f x).1.natAdd k,(f x).2) := by
  simp [blockPerm]

theorem blockPerm_hasTable (f : polygonFullGroup a n) : HasTranslationTable (blockPerm k f.val) := by
  obtain ⟨s,hs,hcover⟩ := f.property
  let leftChart : Fin k → TableChart a (k+n) := fun i => ⟨i.castAdd n,i.castAdd n,0,⊤⟩
  let rightChart : TableChart a n → TableChart a (k+n) := fun c =>
    ⟨c.source.natAdd k,c.target.natAdd k,c.shift,c.domain⟩
  refine ⟨Finset.univ.image leftChart ∪ s.image rightChart,?_,?_⟩
  · intro c hc
    rcases Finset.mem_union.mp hc with hc|hc
    · obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      change blockPerm k f.val (i.castAdd n,x)=(i.castAdd n,translate a 0 x)
      rw [blockPerm_left (x:=(i,x)),translate_zero]
    · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      change blockPerm k f.val (d.source.natAdd k,x)=(d.target.natAdd k,translate a d.shift x)
      rw [blockPerm_right (x:=(d.source,x)),hs d hd x hx]
  · rintro ⟨i,x⟩
    induction i using Fin.addCases with
    | left i =>
      exact ⟨leftChart i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),rfl,by trivial⟩
    | right i =>
      obtain ⟨c,hc,hx⟩ := hcover (i,x)
      refine ⟨rightChart c,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c,hc,rfl⟩),?_,hx.2⟩
      exact congrArg (Fin.natAdd k) hx.1

noncomputable def stabilize (a k n : ℕ) : polygonFullGroup a n →* polygonFullGroup a (k+n) where
  toFun f := ⟨blockPerm k f.val,blockPerm_hasTable f⟩
  map_one' := by
    apply Subtype.ext; apply Equiv.ext
    intro x
    obtain ⟨y,rfl⟩ := (join a k n).surjective x
    cases y <;> simp [blockPerm]
  map_mul' f g := by
    apply Subtype.ext; apply Equiv.ext
    intro x
    obtain ⟨y,rfl⟩ := (join a k n).surjective x
    cases y <;> simp [blockPerm,Equiv.Perm.mul_apply]

@[simp] theorem stabilize_left (f : polygonFullGroup a n) (x : TrackPoint a k) :
    (stabilize a k n f).val (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2) := blockPerm_left f.val x
@[simp] theorem stabilize_right (f : polygonFullGroup a n) (x : TrackPoint a n) :
    (stabilize a k n f).val (x.1.natAdd k,x.2)=((f.val x).1.natAdd k,(f.val x).2) := blockPerm_right f.val x

theorem stabilize_injective : Function.Injective (stabilize a k n) := by
  intro f g he
  apply Subtype.ext; apply Equiv.ext
  intro x
  have h := congrArg (fun p : polygonFullGroup a (k+n) => p.val (x.1.natAdd k,x.2)) he
  simp only [stabilize_right] at h
  apply Prod.ext
  · apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun p : TrackPoint a (k+n) => p.1.val) h)
  · exact congrArg (fun p : TrackPoint a (k+n) => p.2) h

def bankFixer (a k n : ℕ) : Subgroup (polygonFullGroup a (k+n)) where
  carrier := {g | ∀x : TrackPoint a k,g.val (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro f g hf hg x
    change f.val (g.val (x.1.castAdd n,x.2))=_
    rw [hg x,hf x]
  inv_mem' := by
    intro g hg x
    exact g.val.symm_apply_eq.mpr (hg x).symm

@[simp] theorem mem_bankFixer (g : polygonFullGroup a (k+n)) :
    g∈bankFixer a k n ↔ ∀x : TrackPoint a k,g.val (x.1.castAdd n,x.2)=(x.1.castAdd n,x.2) := Iff.rfl

theorem stabilize_mem_bankFixer (g : polygonFullGroup a n) :
    stabilize a k n g∈bankFixer a k n := stabilize_left g

end PolygonTracks
end PolygonTrackStabilizer

section PolygonTrackRestriction
open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

def rightIncl (a k n : ℕ) (x : TrackPoint a n) : TrackPoint a (k+n) :=
  (x.1.natAdd k,x.2)

theorem rightIncl_injective : Function.Injective (rightIncl a k n) := by
  intro x y he
  apply Prod.ext
  · apply Fin.ext
    exact Nat.add_left_cancel (congrArg (fun p : TrackPoint a (k+n) => p.1.val) he)
  · exact congrArg (fun p : TrackPoint a (k+n) => p.2) he

theorem bankFixer_preserves_right (g : bankFixer a k n) (x : TrackPoint a n) :
    ∃y : TrackPoint a n,g.val.val (rightIncl a k n x)=rightIncl a k n y := by
  obtain ⟨z,hz⟩ := (join a k n).surjective (g.val.val (rightIncl a k n x))
  cases z with
  | inl z =>
    have he : rightIncl a k n x=(z.1.castAdd n,z.2) :=
      g.val.val.injective (hz.symm.trans (g.property z).symm)
    have hf := congrArg (fun p : TrackPoint a (k+n) => p.1.val) he
    have := z.1.isLt
    change k+x.1.val=z.1.val at hf
    omega
  | inr y => exact ⟨y,hz.symm⟩

noncomputable def rightValue (g : bankFixer a k n) (x : TrackPoint a n) : TrackPoint a n :=
  (bankFixer_preserves_right g x).choose

@[simp] theorem rightValue_spec (g : bankFixer a k n) (x : TrackPoint a n) :
    rightIncl a k n (rightValue g x)=g.val.val (rightIncl a k n x) :=
  (bankFixer_preserves_right g x).choose_spec.symm

noncomputable def restrictPerm (g : bankFixer a k n) : Equiv.Perm (TrackPoint a n) where
  toFun := rightValue g
  invFun := rightValue g⁻¹
  left_inv x := by
    apply rightIncl_injective (a:=a) (k:=k)
    rw [rightValue_spec,rightValue_spec]
    exact g.val.val.symm_apply_apply _
  right_inv x := by
    apply rightIncl_injective (a:=a) (k:=k)
    rw [rightValue_spec,rightValue_spec]
    exact g.val.val.apply_symm_apply _

@[simp] theorem restrictPerm_spec (g : bankFixer a k n) (x : TrackPoint a n) :
    rightIncl a k n (restrictPerm g x)=g.val.val (rightIncl a k n x) := rightValue_spec g x

theorem restrictPerm_hasTable (g : bankFixer a k n) : HasTranslationTable (restrictPerm g) := by
  obtain ⟨s,hs,hcover⟩ := g.val.property
  let admissible : Fin n × Fin n × TableChart a (k+n) → Prop := fun t =>
    t.2.2.source=t.1.natAdd k ∧ t.2.2.target=t.2.1.natAdd k
  let conv : Fin n × Fin n × TableChart a (k+n) → TableChart a n := fun t =>
    ⟨t.1,t.2.1,t.2.2.shift,t.2.2.domain⟩
  let ts := ((Finset.univ : Finset (Fin n)).product ((Finset.univ : Finset (Fin n)).product s)).filter admissible
  refine ⟨ts.image conv,?_,?_⟩
  · intro c hc
    obtain ⟨⟨i,j,d⟩,hd,rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hmem,hsource,htarget⟩ := Finset.mem_filter.mp hd
    have hdmem : d∈s := (Finset.mem_product.mp (Finset.mem_product.mp hmem).2).2
    intro x hx
    apply rightIncl_injective (a:=a) (k:=k)
    rw [restrictPerm_spec]
    change g.val.val (i.natAdd k,x)=(j.natAdd k,translate a d.shift x)
    change d.source=i.natAdd k at hsource
    change d.target=j.natAdd k at htarget
    rw [← hsource,← htarget]
    exact hs d hdmem x hx
  · intro x
    obtain ⟨d,hd,hsource,hx⟩ := hcover (rightIncl a k n x)
    have he := hs d hd x.2 hx
    have htarget : d.target=(restrictPerm g x).1.natAdd k := by
      have hp := congrArg Prod.fst (restrictPerm_spec g x)
      change x.1.natAdd k=d.source at hsource
      rw [← hsource] at he
      exact (congrArg Prod.fst he).symm.trans hp.symm
    refine ⟨conv (x.1,(restrictPerm g x).1,d),Finset.mem_image.mpr ⟨_,?_,rfl⟩,rfl,hx⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_product.mpr ⟨Finset.mem_univ _,hd⟩⟩,hsource.symm,htarget⟩

noncomputable def restrict (g : bankFixer a k n) : polygonFullGroup a n :=
  ⟨restrictPerm g,restrictPerm_hasTable g⟩

@[simp] theorem stabilize_restrict (g : bankFixer a k n) : stabilize a k n (restrict g)=g.val := by
  apply Subtype.ext; apply Equiv.ext
  intro x
  obtain ⟨z,rfl⟩ := (join a k n).surjective x
  cases z with
  | inl y => exact (stabilize_left _ y).trans (g.property y).symm
  | inr y => exact (stabilize_right _ y).trans (restrictPerm_spec g y)

@[simp] theorem restrict_stabilize (g : polygonFullGroup a n) :
    restrict ⟨stabilize a k n g,stabilize_mem_bankFixer g⟩=g := by
  apply stabilize_injective (k:=k)
  exact stabilize_restrict _

noncomputable def stabilizerEquiv (a k n : ℕ) : polygonFullGroup a n ≃* bankFixer a k n where
  toFun g := ⟨stabilize a k n g,stabilize_mem_bankFixer g⟩
  invFun := restrict
  left_inv := restrict_stabilize
  right_inv g := Subtype.ext (stabilize_restrict g)
  map_mul' g h := Subtype.ext ((stabilize a k n).map_mul g h)

end PolygonTracks
end PolygonTrackRestriction

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
section TransitiveInduction

open Classical _root_.CategoryTheory Representation Finsupp
namespace TransitiveInduction
variable {G X : Type} [Group G] [MulAction G X] (x : X)

lemma from_to (ht : ∀y : X,∃g : G,g • x=y) :
    (fromPermutation x ht).comp (toPermutation (G:=G) x).hom.toLinearMap=LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro z
  change fromPermutation x ht (toPermutation (G:=G) x (IndV.mk _ _ g z))=IndV.mk _ _ g z
  rw [toPermutation_mk,fromPermutation_single]
  apply mk_same
  simp

lemma to_from (ht : ∀y : X,∃g : G,g • x=y) :
    (toPermutation (G:=G) x).hom.toLinearMap.comp (fromPermutation x ht)=LinearMap.id := by
  apply Finsupp.lhom_ext
  intro y z
  change toPermutation (G:=G) x (fromPermutation x ht (Finsupp.single y z))=Finsupp.single y z
  rw [fromPermutation_single,toPermutation_mk]
  simp

noncomputable def iso (ht : ∀y : X,∃g : G,g • x=y) :
    Rep.ind (MulAction.stabilizer G x).subtype (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≅
      Rep.of (permutationRep (G:=G) (X:=X)) :=
  Rep.mkIso (Representation.IntertwiningMap.ofBijective (toPermutation (G:=G) x).hom
    ⟨by
      intro u v he
      exact (LinearMap.congr_fun (from_to x ht) u).symm.trans
        ((congrArg (fromPermutation x ht) he).trans (LinearMap.congr_fun (from_to x ht) v)),
      fun y => ⟨fromPermutation x ht y,LinearMap.congr_fun (to_from x ht) y⟩⟩)

noncomputable def homologyIso (ht : ∀y : X,∃g : G,g • x=y) (q : ℕ) :
    groupHomology (Rep.of (permutationRep (G:=G) (X:=X))) q ≅
      groupHomology (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) q :=
  (groupHomology.functor ℤ G q).mapIso (iso x ht).symm ≪≫ groupHomology.indIso _ _ q

end TransitiveInduction
end TransitiveInduction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_TransitiveCanonical
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

lemma pointMap_factorization (x : X) (ht : ∀y : X, ∃g : G, g • x=y) :
    pointMap (G:=G) x =
      CanonicalShapiro.indUnit (MulAction.stabilizer G x).subtype
        (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≫
      (Rep.resFunctor.{0,0,0,0} (MulAction.stabilizer G x).subtype).map (iso x ht).hom := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro z
  change Finsupp.single x z =
    toPermutation x ((CanonicalShapiro.indUnit _ _).hom z)
  rw [CanonicalShapiro.indUnit_apply, toPermutation_mk]
  simp
lemma isIso_map_pointMap (x : X) (ht : ∀y : X, ∃g : G, g • x=y) (q : ℕ) :
    IsIso (groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q) := by
  rw [pointMap_factorization x ht]
  have hn : groupHomology.map (MulAction.stabilizer G x).subtype
      (CanonicalShapiro.indUnit _ (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) ≫
       (Rep.resFunctor.{0,0,0,0} (MulAction.stabilizer G x).subtype).map (iso x ht).hom) q =
      groupHomology.map (MulAction.stabilizer G x).subtype
        (CanonicalShapiro.indUnit _ (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ)) q ≫
      (groupHomology.functor ℤ G q).map (iso x ht).hom :=
    groupHomology.map_comp (C:=Rep.of (permutationRep (G:=G) (X:=X)))
      (MulAction.stabilizer G x).subtype (MonoidHom.id G)
      (CanonicalShapiro.indUnit _ (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ))
      (iso x ht).hom q
  rw [hn]
  have first := CanonicalShapiro.isIso_map_indUnit (MulAction.stabilizer G x)
    (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) q
  have second : IsIso ((groupHomology.functor ℤ G q).map (iso x ht).hom) := inferInstance
  have composite := IsIso.comp_isIso' first second
  exact composite

lemma pointMap_natural (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x) (x : X) (q : ℕ) :
    groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q ≫
      (groupHomology.functor ℤ G q).map (equivariantMap f hf) =
    groupHomology.map (A:=Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) (B:=Rep.trivial ℤ (MulAction.stabilizer G (f x)) ℤ) (stabilizerMap f hf x) (trivialMap (stabilizerMap f hf x)) q ≫
      groupHomology.map (MulAction.stabilizer G (f x)).subtype (pointMap (f x)) q := by
  rw [groupHomology.functor_map]
  erw [← groupHomology.map_comp, ← groupHomology.map_comp]
  apply groupHomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro z
    change (equivariantMap f hf).hom (Finsupp.single x z) = Finsupp.single (f x) z
    exact equivariantMap_single f hf x z

lemma map_equivariant_eq_of_centralizer
    (f₀ f₁ : X → Y) (h₀ : ∀g : G,∀x,f₀ (g • x)=g • f₀ x)
    (h₁ : ∀g : G,∀x,f₁ (g • x)=g • f₁ x)
    (x : X) (ht : ∀y : X, ∃g : G,g • x=y) (c : G)
    (hc : ∀h : MulAction.stabilizer G x,c*h.val=h.val*c)
    (hx : c • f₀ x=f₁ x) (q : ℕ) :
    (groupHomology.functor ℤ G q).map (equivariantMap f₁ h₁) =
      (groupHomology.functor ℤ G q).map (equivariantMap f₀ h₀) := by
  let := isIso_map_pointMap x ht q
  apply (cancel_epi (groupHomology.map (MulAction.stabilizer G x).subtype (pointMap x) q)).1
  rw [groupHomology.functor_map, groupHomology.functor_map]
  erw [← groupHomology.map_comp, ← groupHomology.map_comp]
  apply HomologyConjugation.map_eq_of_centralizer _ _ _ c hc
  intro z
  change (equivariantMap f₁ h₁).hom (Finsupp.single x z) =
    permutationRep c ((equivariantMap f₀ h₀).hom (Finsupp.single x z))
  rw [equivariantMap_single, equivariantMap_single, permutationRep_single, hx]
lemma isIso_map_equivariant_H0 (f : X → Y) (hf : ∀g : G,∀x,f (g • x)=g • f x)
    (x : X) (htx : ∀y:X,∃g:G,g • x=y)
    (hty : ∀y:Y,∃g:G,g • f x=y) :
    IsIso ((groupHomology.functor ℤ G 0).map (equivariantMap f hf)) := by
  have sourceIso := isIso_map_pointMap x htx 0
  have targetIso := isIso_map_pointMap (f x) hty 0
  have trivialIso := isIso_map_trivial_H0 (stabilizerMap f hf x)
  have composite := IsIso.comp_isIso' trivialIso targetIso
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ sourceIso composite
    (pointMap_natural f hf x 0)

end SimpleAmenable.TransitiveInduction

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PermutationAugmentation
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Classical _root_.CategoryTheory CategoryTheory.Limits Representation Rep Finsupp
namespace SimpleAmenable.TransitiveInduction

attribute [local instance 1200] Rep.hV2
variable {G X Y : Type} [Group G] [MulAction G X] [MulAction G Y]

noncomputable def augmentation (G X : Type) [Group G] [MulAction G X] :
    Rep.of (permutationRep (G:=G) (X:=X)) ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ⟨Finsupp.lsum ℤ (fun _ => (LinearMap.id : ℤ →ₗ[ℤ] ℤ)), by
    intro g
    apply Finsupp.lhom_ext
    intro x z
    change (Finsupp.lsum ℤ (fun _ : X => (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))
      (permutationRep (G:=G) (X:=X) g (single x z))=
      (Finsupp.lsum ℤ (fun _ : X => (LinearMap.id : ℤ →ₗ[ℤ] ℤ))) (single x z)
    rw [permutationRep_single]
    simp⟩

@[simp] lemma augmentation_single (x : X) (z : ℤ) :
    (augmentation G X).hom (single x z)=z := by simp [augmentation]

end SimpleAmenable.TransitiveInduction

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FreeChains
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory Limits MonoidalCategory HomologicalComplex
namespace TensorCoefficient

variable {R : Type} [CommRing R]
variable (K : ChainComplex (ModuleCat.{0} R) ℕ)

noncomputable def unitIso : (functor K).obj (ModuleCat.of R R) ≅ K :=
  (NatIso.mapHomologicalComplex (rightUnitorNatIso (ModuleCat.{0} R)) c).app K ≪≫
    (Functor.mapHomologicalComplexIdIso _ _).app K

noncomputable def homologyUnitIso (n : ℕ) :
    (homologyFunctor K n).obj (ModuleCat.of R R) ≅ K.homology n :=
  (HomologicalComplex.homologyFunctor _ c n).mapIso (unitIso K)

end TensorCoefficient

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonGroupoidTracks
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonGroupoidTracks
open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable def standard (a m : ℕ) : PolygonObject a := ⟨m,fun _ => ⊤⟩

noncomputable def standardPointEquiv (a m : ℕ) : (standard a m).Point ≃ TrackPoint a m where
  toFun := Subtype.val
  invFun x := ⟨x,by trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def fullGroupArrow {m : ℕ} (g : polygonFullGroup a m) : standard a m ⟶ standard a m where
  toEquiv := (standardPointEquiv a m).trans (g.val.trans (standardPointEquiv a m).symm)
  hasTable := by
    obtain ⟨s,hs,hcover⟩ := g.property
    let conv : TableChart a m → Chart (a:=a) m m := fun c => ⟨c.source,c.target,c.shift,c.domain⟩
    refine ⟨s.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      refine ⟨by trivial,?_⟩
      exact hs d hd x hx
    · intro x
      obtain ⟨c,hc,hx⟩ := hcover x.val
      exact ⟨conv c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,hx⟩

noncomputable def fullGroupOfArrow {m : ℕ} (g : standard a m ⟶ standard a m) : polygonFullGroup a m :=
  ⟨(standardPointEquiv a m).symm.trans (g.toEquiv.trans (standardPointEquiv a m)),by
    obtain ⟨s,hs,hcover⟩ := g.hasTable
    let conv : Chart (a:=a) m m → TableChart a m := fun c => ⟨c.source,c.target,c.shift,c.domain⟩
    refine ⟨s.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      intro x hx
      obtain ⟨hu,he⟩ := hs d hd x hx
      exact he
    · intro x
      obtain ⟨c,hc,hx⟩ := hcover ((standardPointEquiv _ _).symm x)
      exact ⟨conv c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,hx⟩⟩

@[simp] theorem arrow_fullGroup {m : ℕ} (g : standard a m ⟶ standard a m) :
    fullGroupArrow (fullGroupOfArrow g)=g := by
  apply Arrow.ext
  apply Equiv.ext
  intro x
  rfl

@[simp] theorem fullGroup_arrow {m : ℕ} (g : polygonFullGroup a m) :
    fullGroupOfArrow (fullGroupArrow g)=g := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rfl

theorem fullGroupArrow_injective {m : ℕ} : Function.Injective (@fullGroupArrow a m) := by
  intro g h he
  simpa using congrArg fullGroupOfArrow he

noncomputable def standardAutEquiv (a m : ℕ) : Aut (standard a m) ≃* polygonFullGroup a m where
  toFun g := fullGroupOfArrow g.hom
  invFun g := asIso (fullGroupArrow g)
  left_inv g := by apply Iso.ext; exact arrow_fullGroup g.hom
  right_inv g := fullGroup_arrow g
  map_mul' g h := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl

end PolygonObject
end PolygonGroupoidTracks

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonObjectSum
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonObjectSum

open Classical Set _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

@[simp] theorem arrow_id_apply (U : PolygonObject a) (x : U.Point) : (𝟙 U : U ⟶ U).toEquiv x=x := rfl
@[simp] theorem arrow_comp_apply {U V W : PolygonObject a} (f : U ⟶ V) (g : V ⟶ W) (x : U.Point) :
    (f≫g).toEquiv x=g.toEquiv (f.toEquiv x) := rfl

noncomputable def sum (U V : PolygonObject a) : PolygonObject a :=
  ⟨U.tracks+V.tracks,Fin.addCases U.cell V.cell⟩

noncomputable def sumPointEquiv (U V : PolygonObject a) :
    U.Point ⊕ V.Point ≃ (sum U V).Point where
  toFun := Sum.elim
    (fun x => ⟨(x.val.1.castAdd V.tracks,x.val.2),by simpa [sum] using x.property⟩)
    (fun x => ⟨(x.val.1.natAdd U.tracks,x.val.2),by simpa [sum] using x.property⟩)
  invFun x := Fin.addCases (motive:=fun i => x.val.2∈((sum U V).cell i).val → U.Point ⊕ V.Point)
    (fun i => fun h : x.val.2∈((sum U V).cell (i.castAdd V.tracks)).val =>
      Sum.inl ⟨(i,x.val.2),by simpa [sum] using h⟩)
    (fun i => fun h : x.val.2∈((sum U V).cell (i.natAdd U.tracks)).val =>
      Sum.inr ⟨(i,x.val.2),by simpa [sum] using h⟩) x.val.1 x.property
  left_inv x := by cases x <;> simp
  right_inv x := by
    obtain ⟨⟨i,x⟩,hx⟩ := x
    induction i using Fin.addCases <;> simp

@[simp] theorem sumPointEquiv_inl (U V : PolygonObject a) (x : U.Point) :
    (sumPointEquiv U V (.inl x)).val=(x.val.1.castAdd V.tracks,x.val.2) := rfl
@[simp] theorem sumPointEquiv_inr (U V : PolygonObject a) (x : V.Point) :
    (sumPointEquiv U V (.inr x)).val=(x.val.1.natAdd U.tracks,x.val.2) := rfl

noncomputable def sumArrow {U V W Z : PolygonObject a} (f : U ⟶ W) (g : V ⟶ Z) :
    sum U V ⟶ sum W Z where
  toEquiv := (sumPointEquiv U V).symm.trans ((Equiv.sumCongr f.toEquiv g.toEquiv).trans (sumPointEquiv W Z))
  hasTable := by
    obtain ⟨s,hs,hcover⟩ := f.hasTable
    obtain ⟨t,ht,htcover⟩ := g.hasTable
    let L : Chart (a:=a) U.tracks W.tracks → Chart (a:=a) (U.tracks+V.tracks) (W.tracks+Z.tracks) :=
      fun c => ⟨c.source.castAdd V.tracks,c.target.castAdd Z.tracks,c.shift,c.domain⟩
    let R : Chart (a:=a) V.tracks Z.tracks → Chart (a:=a) (U.tracks+V.tracks) (W.tracks+Z.tracks) :=
      fun c => ⟨c.source.natAdd U.tracks,c.target.natAdd W.tracks,c.shift,c.domain⟩
    refine ⟨s.image L ∪ t.image R,?_,?_⟩
    · intro c hc
      rcases Finset.mem_union.mp hc with hc|hc
      · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        obtain ⟨hu,he⟩ := hs d hd x hx
        refine ⟨by simpa [sum,L] using hu,?_⟩
        change (sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv
          ((sumPointEquiv U V).symm (sumPointEquiv U V (.inl ⟨(d.source,x),hu⟩))))).val=_
        rw [Equiv.symm_apply_apply]
        change (sumPointEquiv W Z (.inl (f.toEquiv ⟨(d.source,x),hu⟩))).val=_
        rw [sumPointEquiv_inl,he]
        rfl
      · obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        obtain ⟨hv,he⟩ := ht d hd x hx
        refine ⟨by simpa [sum,R] using hv,?_⟩
        change (sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv
          ((sumPointEquiv U V).symm (sumPointEquiv U V (.inr ⟨(d.source,x),hv⟩))))).val=_
        rw [Equiv.symm_apply_apply]
        change (sumPointEquiv W Z (.inr (g.toEquiv ⟨(d.source,x),hv⟩))).val=_
        rw [sumPointEquiv_inr,he]
        rfl
    · intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
      cases y with
      | inl y =>
        obtain ⟨c,hc,hy⟩ := hcover y
        exact ⟨L c,Finset.mem_union_left _ (Finset.mem_image_of_mem L hc),
          congrArg (Fin.castAdd V.tracks) hy.1,hy.2⟩
      | inr y =>
        obtain ⟨c,hc,hy⟩ := htcover y
        exact ⟨R c,Finset.mem_union_right _ (Finset.mem_image_of_mem R hc),
          congrArg (Fin.natAdd U.tracks) hy.1,hy.2⟩

@[simp] theorem sumArrow_inl {U V W Z : PolygonObject a} (f : U ⟶ W) (g : V ⟶ Z) (x : U.Point) :
    (sumArrow f g).toEquiv (sumPointEquiv U V (.inl x))=sumPointEquiv W Z (.inl (f.toEquiv x)) := by
  change sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv ((sumPointEquiv U V).symm (sumPointEquiv U V (.inl x))))=_
  rw [Equiv.symm_apply_apply];rfl
@[simp] theorem sumArrow_inr {U V W Z : PolygonObject a} (f : U ⟶ W) (g : V ⟶ Z) (x : V.Point) :
    (sumArrow f g).toEquiv (sumPointEquiv U V (.inr x))=sumPointEquiv W Z (.inr (g.toEquiv x)) := by
  change sumPointEquiv W Z (Equiv.sumCongr f.toEquiv g.toEquiv ((sumPointEquiv U V).symm (sumPointEquiv U V (.inr x))))=_
  rw [Equiv.symm_apply_apply];rfl

theorem sumArrow_id (U V : PolygonObject a) : sumArrow (𝟙 U) (𝟙 V)=𝟙 (sum U V) := by
  apply Arrow.ext;apply Equiv.ext;intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y <;> simp

theorem sumArrow_comp {U U' U'' V V' V'' : PolygonObject a}
    (f : U ⟶ U') (f' : U' ⟶ U'') (g : V ⟶ V') (g' : V' ⟶ V'') :
    sumArrow (f≫f') (g≫g')=sumArrow f g ≫ sumArrow f' g' := by
  apply Arrow.ext;apply Equiv.ext;intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y <;> simp only [arrow_comp_apply,sumArrow_inl,sumArrow_inr]

end PolygonObject
end PolygonObjectSum

open Classical Set _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable def complement (U : PolygonObject a) : PolygonObject a :=
  ⟨U.tracks,fun i => (U.cell i)ᶜ⟩

noncomputable def splitPointEquiv (U : PolygonObject a) :
    U.Point ⊕ (complement U).Point ≃ TrackPoint a U.tracks where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if hx : x.2∈(U.cell x.1).val then .inl ⟨x,hx⟩ else .inr ⟨x,hx⟩
  left_inv := by
    rintro (x|x)
    · dsimp only
      exact dite_eq_left x.property
    · dsimp only
      exact dite_eq_right x.property
  right_inv x := by dsimp;split <;> rfl

@[simp] theorem splitPointEquiv_inl (U : PolygonObject a) (x : U.Point) :
    splitPointEquiv U (.inl x)=x.val := rfl
@[simp] theorem splitPointEquiv_inr (U : PolygonObject a) (x : (complement U).Point) :
    splitPointEquiv U (.inr x)=x.val := rfl

noncomputable def complementArrow (U : PolygonObject a) : sum U (complement U) ⟶ standard a U.tracks where
  toEquiv := (sumPointEquiv U (complement U)).symm.trans ((splitPointEquiv U).trans (standardPointEquiv a U.tracks).symm)
  hasTable := by
    let L (i : Fin U.tracks) : Chart (a:=a) (U.tracks+U.tracks) U.tracks := ⟨i.castAdd _,i,0,U.cell i⟩
    let R (i : Fin U.tracks) : Chart (a:=a) (U.tracks+U.tracks) U.tracks := ⟨i.natAdd _,i,0,(U.cell i)ᶜ⟩
    refine ⟨Finset.univ.image L ∪ Finset.univ.image R,?_,?_⟩
    · intro c hc
      rcases Finset.mem_union.mp hc with hc|hc
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        refine ⟨by simpa [sum,complement,L] using hx,?_⟩
        change (splitPointEquiv U ((sumPointEquiv U (complement U)).symm
          (sumPointEquiv U (complement U) (.inl ⟨(i,x),hx⟩))))=(i,translate a 0 x)
        rw [Equiv.symm_apply_apply,splitPointEquiv_inl,translate_zero]
      · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hc
        intro x hx
        refine ⟨(sumPointEquiv U (complement U) (.inr ⟨(i,x),hx⟩)).property,?_⟩
        change (splitPointEquiv U ((sumPointEquiv U (complement U)).symm
          (sumPointEquiv U (complement U) (.inr ⟨(i,x),hx⟩))))=(i,translate a 0 x)
        rw [Equiv.symm_apply_apply,splitPointEquiv_inr,translate_zero]
        rfl
    · intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U (complement U)).surjective x
      cases y with
      | inl y => exact ⟨L y.val.1,Finset.mem_union_left _ (Finset.mem_image_of_mem L (Finset.mem_univ _)),rfl,y.property⟩
      | inr y => exact ⟨R y.val.1,Finset.mem_union_right _ (Finset.mem_image_of_mem R (Finset.mem_univ _)),rfl,y.property⟩

@[simp] theorem complementArrow_inl (U : PolygonObject a) (x : U.Point) :
    ((complementArrow U).toEquiv (sumPointEquiv U (complement U) (.inl x))).val=x.val := by
  change splitPointEquiv U ((sumPointEquiv U (complement U)).symm (sumPointEquiv U (complement U) (.inl x)))=x.val
  rw [Equiv.symm_apply_apply];rfl
@[simp] theorem complementArrow_inr (U : PolygonObject a) (x : (complement U).Point) :
    ((complementArrow U).toEquiv (sumPointEquiv U (complement U) (.inr x))).val=x.val := by
  change splitPointEquiv U ((sumPointEquiv U (complement U)).symm (sumPointEquiv U (complement U) (.inr x)))=x.val
  rw [Equiv.symm_apply_apply];rfl

noncomputable def complementIso (U : PolygonObject a) : sum U (complement U) ≅ standard a U.tracks :=
  asIso (complementArrow U)

end PolygonObject

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PolygonMonoidalData
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonMonoidalData

open Classical Set _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable def relabelArrow {U V : PolygonObject a} (e : U.Point ≃ V.Point)
    (r : Fin U.tracks → Fin V.tracks)
    (he : ∀x,(e x).val=(r x.val.1,x.val.2)) : U ⟶ V where
  toEquiv := e
  hasTable := by
    let c : Fin U.tracks → Chart (a:=a) U.tracks V.tracks := fun i => ⟨i,r i,0,U.cell i⟩
    refine ⟨Finset.univ.image c,?_,?_⟩
    · intro d hd
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      intro x hx
      exact ⟨hx,by simpa [c,translate_zero] using he ⟨(i,x),hx⟩⟩
    · intro x
      exact ⟨c x.val.1,Finset.mem_image_of_mem c (Finset.mem_univ _),rfl,x.property⟩

noncomputable def sumSwapEquiv (U V : PolygonObject a) : (sum U V).Point ≃ (sum V U).Point :=
  (sumPointEquiv U V).symm.trans ((Equiv.sumComm _ _).trans (sumPointEquiv V U))

@[simp] theorem sumSwapEquiv_inl (U V : PolygonObject a) (x : U.Point) :
    sumSwapEquiv U V (sumPointEquiv U V (.inl x))=sumPointEquiv V U (.inr x) := by
  simp [sumSwapEquiv]
@[simp] theorem sumSwapEquiv_inr (U V : PolygonObject a) (x : V.Point) :
    sumSwapEquiv U V (sumPointEquiv U V (.inr x))=sumPointEquiv V U (.inl x) := by
  simp [sumSwapEquiv]
noncomputable def sumSwap (U V : PolygonObject a) : sum U V ⟶ sum V U :=
  relabelArrow (sumSwapEquiv U V)
    (Fin.addCases (fun i => i.natAdd V.tracks) (fun i => i.castAdd U.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
      cases y with
      | inl y =>
        simp only [sumSwapEquiv_inl,sumPointEquiv_inl,sumPointEquiv_inr]
        erw [Fin.addCases_left]
        rfl
      | inr y =>
        simp only [sumSwapEquiv_inr,sumPointEquiv_inl,sumPointEquiv_inr]
        erw [Fin.addCases_right]
        rfl)

noncomputable def sumAssocEquiv (U V W : PolygonObject a) : (sum (sum U V) W).Point ≃ (sum U (sum V W)).Point :=
  (sumPointEquiv (sum U V) W).symm.trans
    ((Equiv.sumCongr (sumPointEquiv U V).symm (Equiv.refl _)).trans
      ((Equiv.sumAssoc U.Point V.Point W.Point).trans
        ((Equiv.sumCongr (Equiv.refl _) (sumPointEquiv V W)).trans (sumPointEquiv U (sum V W)))))

@[simp] theorem sumAssocEquiv_left (U V W : PolygonObject a) (x : U.Point) :
    sumAssocEquiv U V W (sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inl x))))=
      sumPointEquiv U (sum V W) (.inl x) := by simp [sumAssocEquiv]
@[simp] theorem sumAssocEquiv_mid (U V W : PolygonObject a) (x : V.Point) :
    sumAssocEquiv U V W (sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inr x))))=
      sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inl x))) := by simp [sumAssocEquiv]
@[simp] theorem sumAssocEquiv_right (U V W : PolygonObject a) (x : W.Point) :
    sumAssocEquiv U V W (sumPointEquiv (sum U V) W (.inr x))=
      sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inr x))) := by simp [sumAssocEquiv]
noncomputable def sumAssoc (U V W : PolygonObject a) : sum (sum U V) W ⟶ sum U (sum V W) :=
  relabelArrow (sumAssocEquiv U V W)
    (Fin.addCases
      (Fin.addCases (fun i => i.castAdd (V.tracks+W.tracks)) (fun i => (i.castAdd W.tracks).natAdd U.tracks))
      (fun i => (i.natAdd V.tracks).natAdd U.tracks)) (by
      intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
        cases z with
        | inl z =>
          simp only [sumAssocEquiv_left,sumPointEquiv_inl]
          erw [Fin.addCases_left,Fin.addCases_left]
          rfl
        | inr z =>
          simp only [sumAssocEquiv_mid,sumPointEquiv_inl,sumPointEquiv_inr]
          erw [Fin.addCases_left,Fin.addCases_right]
          rfl
      | inr y =>
        simp only [sumAssocEquiv_right,sumPointEquiv_inr]
        erw [Fin.addCases_right]
        rfl)

noncomputable def empty : PolygonObject a := ⟨0,Fin.elim0⟩
instance instIsEmptyPointEmpty : IsEmpty (empty (a:=a)).Point := ⟨fun x => Fin.elim0 x.val.1⟩

noncomputable def leftUnitEquiv (U : PolygonObject a) : (sum empty U).Point ≃ U.Point :=
  (sumPointEquiv empty U).symm.trans (Equiv.emptySum _ _)
noncomputable def rightUnitEquiv (U : PolygonObject a) : (sum U empty).Point ≃ U.Point :=
  (sumPointEquiv U empty).symm.trans (Equiv.sumEmpty _ _)

@[simp] theorem leftUnitEquiv_apply (U : PolygonObject a) (x : U.Point) :
    leftUnitEquiv U (sumPointEquiv empty U (.inr x))=x := by simp [leftUnitEquiv]
@[simp] theorem rightUnitEquiv_apply (U : PolygonObject a) (x : U.Point) :
    rightUnitEquiv U (sumPointEquiv U empty (.inl x))=x := by simp [rightUnitEquiv]
noncomputable def leftUnit (U : PolygonObject a) : sum empty U ⟶ U :=
  relabelArrow (leftUnitEquiv U) (Fin.addCases Fin.elim0 id) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv empty U).surjective x
    cases y with
    | inl y => exact isEmptyElim y
    | inr y =>
      simp only [leftUnitEquiv_apply,sumPointEquiv_inr]
      erw [Fin.addCases_right]
      rfl)
noncomputable def rightUnit (U : PolygonObject a) : sum U empty ⟶ U :=
  relabelArrow (rightUnitEquiv U) (Fin.addCases id Fin.elim0) (by
    intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U empty).surjective x
    cases y with
    | inl y =>
      simp only [rightUnitEquiv_apply,sumPointEquiv_inl]
      erw [Fin.addCases_left]
      rfl
    | inr y => exact isEmptyElim y)

@[simp] theorem sumSwap_apply (U V : PolygonObject a) (x : (sum U V).Point) :
    (sumSwap U V).toEquiv x=sumSwapEquiv U V x := rfl
@[simp] theorem sumAssoc_apply (U V W : PolygonObject a) (x : (sum (sum U V) W).Point) :
    (sumAssoc U V W).toEquiv x=sumAssocEquiv U V W x := rfl
@[simp] theorem leftUnit_apply (U : PolygonObject a) (x : (sum empty U).Point) :
    (leftUnit U).toEquiv x=leftUnitEquiv U x := rfl
@[simp] theorem rightUnit_apply (U : PolygonObject a) (x : (sum U empty).Point) :
    (rightUnit U).toEquiv x=rightUnitEquiv U x := rfl

end PolygonObject
end PolygonMonoidalData

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

noncomputable abbrev monoidalStruct : MonoidalCategoryStruct (PolygonObject a) where
  tensorObj := sum
  tensorHom := sumArrow
  whiskerLeft U _ _ f := sumArrow (𝟙 U) f
  whiskerRight f U := sumArrow f (𝟙 U)
  tensorUnit := empty
  associator U V W := asIso (sumAssoc U V W)
  leftUnitor U := asIso (leftUnit U)
  rightUnitor U := asIso (rightUnit U)

attribute [instance] monoidalStruct

noncomputable instance monoidal : MonoidalCategory (PolygonObject a) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := sumArrow_id)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' => (sumArrow_comp f f' g g').symm)
    (associator_naturality := by
      intro U V W U' V' W' f g h
      change sumArrow (sumArrow f g) h ≫ sumAssoc U' V' W' = sumAssoc U V W ≫ sumArrow f (sumArrow g h)
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
        cases z <;> simp
      | inr y => simp)
    (leftUnitor_naturality := by
      intro U V f
      change sumArrow (𝟙 empty) f ≫ leftUnit V = leftUnit U ≫ f
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv empty U).surjective x
      cases y with
      | inl y => exact isEmptyElim y
      | inr y => simp)
    (rightUnitor_naturality := by
      intro U V f
      change sumArrow f (𝟙 empty) ≫ rightUnit V = rightUnit U ≫ f
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv U empty).surjective x
      cases y with
      | inl y => simp
      | inr y => exact isEmptyElim y)
    (pentagon := by
      intro U V W Z
      change sumArrow (sumAssoc U V W) (𝟙 Z) ≫ sumAssoc U (sum V W) Z ≫ sumArrow (𝟙 U) (sumAssoc V W Z) =
        sumAssoc (sum U V) W Z ≫ sumAssoc U V (sum W Z)
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum (sum U V) W) Z).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv (sum U V) W).surjective y
        cases z with
        | inl z =>
          obtain ⟨t,rfl⟩ := (sumPointEquiv U V).surjective z
          cases t <;> simp
        | inr z => simp
      | inr y => simp)
    (triangle := by
      intro U V
      change sumAssoc U empty V ≫ sumArrow (𝟙 U) (leftUnit V) = sumArrow (rightUnit U) (𝟙 V)
      apply Arrow.ext;apply Equiv.ext;intro x
      obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U empty) V).surjective x
      cases y with
      | inl y =>
        obtain ⟨z,rfl⟩ := (sumPointEquiv U empty).surjective y
        cases z with
        | inl z => simp
        | inr z => exact isEmptyElim z
      | inr y => simp)

@[simp] theorem sumAssocEquiv_symm_left (U V W : PolygonObject a) (x : U.Point) :
    (sumAssocEquiv U V W).symm (sumPointEquiv U (sum V W) (.inl x))=
      sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inl x))) :=
  (Equiv.symm_apply_eq _).mpr (sumAssocEquiv_left U V W x).symm
@[simp] theorem sumAssocEquiv_symm_mid (U V W : PolygonObject a) (x : V.Point) :
    (sumAssocEquiv U V W).symm (sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inl x))))=
      sumPointEquiv (sum U V) W (.inl (sumPointEquiv U V (.inr x))) :=
  (Equiv.symm_apply_eq _).mpr (sumAssocEquiv_mid U V W x).symm
@[simp] theorem sumAssocEquiv_symm_right (U V W : PolygonObject a) (x : W.Point) :
    (sumAssocEquiv U V W).symm (sumPointEquiv U (sum V W) (.inr (sumPointEquiv V W (.inr x))))=
      sumPointEquiv (sum U V) W (.inr x) :=
  (Equiv.symm_apply_eq _).mpr (sumAssocEquiv_right U V W x).symm

@[simp] theorem associator_inv_apply (U V W : PolygonObject a) (x : (sum U (sum V W)).Point) :
    (monoidalStruct.associator U V W).inv.toEquiv x=(sumAssocEquiv U V W).symm x := by
  change (CategoryTheory.inv (sumAssoc U V W)).toEquiv x=_
  rw [← Groupoid.inv_eq_inv]
  rfl

@[simp] theorem sumAssoc_toEquiv (U V W : PolygonObject a) :
    (sumAssoc U V W).toEquiv = sumAssocEquiv U V W := rfl

@[simp] theorem inv_arrow_apply {U V : PolygonObject a} (f : U ⟶ V) (x : V.Point) :
    (CategoryTheory.inv f).toEquiv x = f.toEquiv.symm x := by
  rw [← Groupoid.inv_eq_inv]
  rfl

noncomputable instance braided : BraidedCategory (PolygonObject a) where
  braiding U V := asIso (sumSwap U V)
  braiding_naturality_right := by
    intro U V W f
    change sumArrow (𝟙 U) f ≫ sumSwap U W = sumSwap U V ≫ sumArrow f (𝟙 U)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
    cases y <;> simp
  braiding_naturality_left := by
    intro U V f W
    change sumArrow f (𝟙 W) ≫ sumSwap V W = sumSwap U W ≫ sumArrow (𝟙 W) f
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U W).surjective x
    cases y <;> simp
  hexagon_forward := by
    intro U V W
    change sumAssoc U V W ≫ sumSwap U (sum V W) ≫ sumAssoc V W U =
      sumArrow (sumSwap U V) (𝟙 W) ≫ sumAssoc V U W ≫ sumArrow (𝟙 V) (sumSwap U W)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
    cases y with
    | inl y =>
      obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
      cases z <;> simp
    | inr y => simp
  hexagon_reverse := by
    intro U V W
    change (CategoryTheory.inv (sumAssoc U V W)) ≫ sumSwap (sum U V) W ≫ (CategoryTheory.inv (sumAssoc W U V)) =
      sumArrow (𝟙 U) (sumSwap V W) ≫ (CategoryTheory.inv (sumAssoc U W V)) ≫ sumArrow (sumSwap U W) (𝟙 V)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U (sum V W)).surjective x
    cases y with
    | inl y => simp only [arrow_comp_apply, inv_arrow_apply, sumAssoc_toEquiv,
        sumAssocEquiv_symm_left,sumAssocEquiv_symm_mid,
        sumSwap_apply,sumSwapEquiv_inl,sumArrow_inl,arrow_id_apply]
    | inr y =>
      obtain ⟨z,rfl⟩ := (sumPointEquiv V W).surjective y
      cases z <;> simp only [arrow_comp_apply, inv_arrow_apply, sumAssoc_toEquiv,
        sumAssocEquiv_symm_left,sumAssocEquiv_symm_mid,sumAssocEquiv_symm_right,
        sumSwap_apply,sumSwapEquiv_inl,sumSwapEquiv_inr,sumArrow_inl,sumArrow_inr,arrow_id_apply]

noncomputable instance symmetric : SymmetricCategory (PolygonObject a) where
  symmetry U V := by
    change sumSwap U V ≫ sumSwap V U = 𝟙 (sum U V)
    apply Arrow.ext;apply Equiv.ext;intro x
    obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
    cases y <;> simp

end PolygonObject

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_PolygonPositionalMonoidal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonPositionalMonoidal

open Classical _root_.CategoryTheory
open scoped MonoidalCategory
namespace PolygonObject
variable {a : ℕ}

theorem positional_comp {U V W : PolygonObject a} {f : U ⟶ V} {g : V ⟶ W}
    (hf : Positional f) (hg : Positional g) : Positional (f≫g) :=
  (positionalSubgroupoid a).mul hf hg

theorem positional_inv {U V : PolygonObject a} {f : U ⟶ V}
    (hf : Positional f) : Positional (CategoryTheory.inv f) := by
  rw [←Groupoid.inv_eq_inv]
  exact (positionalSubgroupoid a).inv hf

theorem sumArrow_positional {U V W Z : PolygonObject a} {f : U ⟶ W} {g : V ⟶ Z}
    (hf : Positional f) (hg : Positional g) : Positional (sumArrow f g) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y with
  | inl y => simpa only [sumArrow_inl,sumPointEquiv_inl] using hf y
  | inr y => simpa only [sumArrow_inr,sumPointEquiv_inr] using hg y

theorem sumSwap_positional (U V : PolygonObject a) : Positional (sumSwap U V) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U V).surjective x
  cases y <;> simp only [sumSwap_apply,sumSwapEquiv_inl,sumSwapEquiv_inr,
    sumPointEquiv_inl,sumPointEquiv_inr]

theorem sumAssoc_positional (U V W : PolygonObject a) : Positional (sumAssoc U V W) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv (sum U V) W).surjective x
  cases y with
  | inl y =>
    obtain ⟨z,rfl⟩ := (sumPointEquiv U V).surjective y
    cases z <;> simp only [sumAssoc_apply,sumAssocEquiv_left,sumAssocEquiv_mid,
      sumPointEquiv_inl,sumPointEquiv_inr]
  | inr y => simp only [sumAssoc_apply,sumAssocEquiv_right,sumPointEquiv_inr]

theorem leftUnit_positional (U : PolygonObject a) : Positional (leftUnit U) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv empty U).surjective x
  cases y with
  | inl y => exact isEmptyElim y
  | inr y => simp only [leftUnit_apply,leftUnitEquiv_apply,sumPointEquiv_inr]

theorem rightUnit_positional (U : PolygonObject a) : Positional (rightUnit U) := by
  intro x
  obtain ⟨y,rfl⟩ := (sumPointEquiv U empty).surjective x
  cases y with
  | inl y => simp only [rightUnit_apply,rightUnitEquiv_apply,sumPointEquiv_inl]
  | inr y => exact isEmptyElim y

def positionalProperty (a : ℕ) : MorphismProperty (PolygonObject a) :=
  fun _ _ f => Positional f

instance positionalProperty_multiplicative : (positionalProperty a).IsMultiplicative where
  id_mem := identity_positional
  comp_mem _ _ := positional_comp

instance positionalProperty_monoidal : (positionalProperty a).IsMonoidalStable where
  whiskerLeft U _ _ _ hf := sumArrow_positional (identity_positional U) hf
  whiskerRight _ hf V := sumArrow_positional hf (identity_positional V)
  associator_hom_mem := sumAssoc_positional
  associator_inv_mem U V W := positional_inv (sumAssoc_positional U V W)
  leftUnitor_hom_mem := leftUnit_positional
  leftUnitor_inv_mem U := positional_inv (leftUnit_positional U)
  rightUnitor_hom_mem := rightUnit_positional
  rightUnitor_inv_mem U := positional_inv (rightUnit_positional U)

instance positionalProperty_braided : (positionalProperty a).IsStableUnderBraiding where
  braiding_hom_mem := sumSwap_positional
  braiding_inv_mem U V := positional_inv (sumSwap_positional U V)

end PolygonObject
end PolygonPositionalMonoidal

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonStringGroupoid
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PolygonStringGroupoid

open Classical _root_.CategoryTheory
open scoped MonoidalCategory
namespace PolygonObject
variable {a : ℕ}

abbrev RawString (a n : ℕ) := Fin (n+1) ⥤ PolygonObject a

def ladderProperty (a n : ℕ) : MorphismProperty (RawString a n) :=
  (positionalProperty a).functorCategory (Fin (n+1))

instance ladderProperty_multiplicative (n : ℕ) : (ladderProperty a n).IsMultiplicative where
  id_mem F i := identity_positional (F.obj i)
  comp_mem _ _ hf hg i := positional_comp (hf i) (hg i)

instance ladderProperty_monoidal (n : ℕ) : (ladderProperty a n).IsMonoidalStable where
  whiskerLeft F _ _ _ hg i := sumArrow_positional (identity_positional (F.obj i)) (hg i)
  whiskerRight _ hf G i := sumArrow_positional (hf i) (identity_positional (G.obj i))
  associator_hom_mem F G H i := sumAssoc_positional (F.obj i) (G.obj i) (H.obj i)
  associator_inv_mem F G H i := positional_inv (sumAssoc_positional (F.obj i) (G.obj i) (H.obj i))
  leftUnitor_hom_mem F i := leftUnit_positional (F.obj i)
  leftUnitor_inv_mem F i := positional_inv (leftUnit_positional (F.obj i))
  rightUnitor_hom_mem F i := rightUnit_positional (F.obj i)
  rightUnitor_inv_mem F i := positional_inv (rightUnit_positional (F.obj i))

instance ladderProperty_braided (n : ℕ) : (ladderProperty a n).IsStableUnderBraiding where
  braiding_hom_mem F G i := sumSwap_positional (F.obj i) (G.obj i)
  braiding_inv_mem F G i := positional_inv (sumSwap_positional (F.obj i) (G.obj i))

abbrev StringGroupoid (a n : ℕ) := WideSubcategory (ladderProperty a n)

noncomputable instance stringGroupoid_isIso {n : ℕ} (F G : StringGroupoid a n) (f : F ⟶ G) : IsIso f := by
  let : IsIso f.hom := NatIso.isIso_of_isIso_app f.hom
  refine ⟨⟨⟨CategoryTheory.inv f.hom,?_⟩,?_,?_⟩⟩
  · intro i
    rw [NatIso.isIso_inv_app]
    exact positional_inv (f.property i)
  · apply WideSubcategory.hom_ext
    exact IsIso.hom_inv_id f.hom
  · apply WideSubcategory.hom_ext
    exact IsIso.inv_hom_id f.hom

noncomputable instance stringGroupoid (n : ℕ) : Groupoid (StringGroupoid a n) :=
  Groupoid.ofIsIso (fun _ => inferInstance)

noncomputable def stringReindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    StringGroupoid a m ⥤ StringGroupoid a n where
  obj F := ⟨u ⋙ F.obj⟩
  map f := ⟨CategoryTheory.Functor.whiskerLeft u f.hom,fun i => f.property (u.obj i)⟩
  map_id F := by apply WideSubcategory.hom_ext; rfl
  map_comp f g := by apply WideSubcategory.hom_ext; rfl

@[simp] theorem stringReindex_id (n : ℕ) : stringReindex (a:=a) (𝟭 (Fin (n+1)))=𝟭 _ := by
  apply CategoryTheory.Functor.ext
  · intro F G f; rfl
  · intro F; cases F; rfl

@[simp] theorem stringReindex_comp {n m k : ℕ}
    (u : Fin (n+1) ⥤ Fin (m+1)) (v : Fin (m+1) ⥤ Fin (k+1)) :
    stringReindex (a:=a) (u⋙v)=stringReindex v ⋙ stringReindex u := by
  apply CategoryTheory.Functor.ext
  · intro F G f; rfl
  · intro F; rfl

noncomputable instance stringReindex_monoidal {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1)) :
    (stringReindex (a:=a) u).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := Iso.refl _
    μIso := fun _ _ => Iso.refl _
    μIso_hom_natural_left := by intros; simp; apply WideSubcategory.hom_ext; rfl
    μIso_hom_natural_right := by intros; simp; apply WideSubcategory.hom_ext; rfl
    associativity := by
      intro first second third
      apply WideSubcategory.hom_ext
      apply NatTrans.ext
      funext point
      change (𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (α_ _ _ _).hom) =
        ((α_ _ _ _).hom ≫ _ ◁ 𝟙 _ ≫ 𝟙 _)
      simp
    left_unitality := by
      intro object
      apply WideSubcategory.hom_ext
      apply NatTrans.ext
      funext point
      change (λ_ _).hom = 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (λ_ _).hom
      simp
    right_unitality := by
      intro object
      apply WideSubcategory.hom_ext
      apply NatTrans.ext
      funext point
      change (ρ_ _).hom = _ ◁ 𝟙 _ ≫ 𝟙 _ ≫ (ρ_ _).hom
      simp }

end PolygonObject
end PolygonStringGroupoid

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a n : ℕ}

def baseArrow (F : RawString a n) (i : Fin (n+1)) : F.obj 0 ⟶ F.obj i :=
  F.map (homOfLE (Fin.zero_le i))

@[simp] theorem baseArrow_zero (F : RawString a n) : baseArrow F 0=𝟙 _ := by
  unfold baseArrow
  exact (congrArg F.map (show homOfLE (Fin.zero_le (0 : Fin (n+1)))=𝟙 (0 : Fin (n+1))
    from Subsingleton.elim _ _)).trans (F.map_id _)

@[simp, reassoc] theorem baseArrow_comp (F : RawString a n) {i j : Fin (n+1)}
    (f : i ⟶ j) : baseArrow F i ≫ F.map f=baseArrow F j := by
  rw [baseArrow,←F.map_comp]
  congr 1

noncomputable def extendLadder {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0) : F ⟶ G where
  app i := CategoryTheory.inv (baseArrow F i) ≫ h ≫ baseArrow G i
  naturality i j f := by
    have he : F.map f ≫ CategoryTheory.inv (baseArrow F j)=CategoryTheory.inv (baseArrow F i) := by
      apply (cancel_epi (baseArrow F i)).mp
      rw [←Category.assoc,baseArrow_comp]
      simp
    simp only [←Category.assoc,he]
    simp only [Category.assoc,baseArrow_comp]

@[simp] theorem extendLadder_zero {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0) :
    (extendLadder h).app 0=h := by
  simp [extendLadder]

theorem ladder_ext {F G : RawString a n} {h k : F ⟶ G}
    (h0 : h.app 0=k.app 0) : h=k := by
  apply NatTrans.ext
  funext i
  apply (cancel_epi (baseArrow F i)).mp
  rw [show baseArrow F i=F.map (homOfLE (Fin.zero_le i)) from rfl,
    h.naturality,k.naturality,h0]

@[simp] theorem extendLadder_app_zero {F G : RawString a n} (h : F ⟶ G) :
    extendLadder (h.app 0)=h := ladder_ext (extendLadder_zero _)

def trajectory (F : RawString a n) (x : (F.obj 0).Point) (i : Fin (n+1)) :=
  ((baseArrow F i).toEquiv x).val.2

theorem ladder_preserves_trajectory {F G : StringGroupoid a n} (h : F ⟶ G)
    (x : (F.obj.obj 0).Point) :
    trajectory G.obj ((h.hom.app 0).toEquiv x)=trajectory F.obj x := by
  funext i
  have he := congrArg (fun k : F.obj.obj 0 ⟶ G.obj.obj i => k.toEquiv x)
    (h.hom.naturality (homOfLE (Fin.zero_le i)))
  change (h.hom.app i).toEquiv ((baseArrow F.obj i).toEquiv x) =
    (baseArrow G.obj i).toEquiv ((h.hom.app 0).toEquiv x) at he
  unfold trajectory
  rw [←he]
  exact h.property i _

theorem extendLadder_positional {F G : RawString a n} (h : F.obj 0 ⟶ G.obj 0)
    (he : ∀x,trajectory G (h.toEquiv x)=trajectory F x) :
    (ladderProperty a n) (extendLadder h) := by
  intro i y
  let x := (baseArrow F i).toEquiv.symm y
  have hi := congrFun (he x) i
  change ((baseArrow G i).toEquiv (h.toEquiv x)).val.2=
    ((baseArrow F i).toEquiv x).val.2 at hi
  simpa only [extendLadder,arrow_comp_apply,inv_arrow_apply,x,Equiv.apply_symm_apply] using hi

end PolygonObject

end SimpleAmenable

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonObjectRefinement
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.braided _root_.OAI.SimpleAmenable.PolygonObject.instIsEmptyPointEmpty _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.monoidal _root_.OAI.SimpleAmenable.PolygonObject.monoidalStruct _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.PolygonObject.symmetric _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonObjectRefinement

open Classical _root_.CategoryTheory Set
namespace PolygonObject
variable {a : ℕ}

noncomputable def shifted (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing) :
    PolygonObject a := ⟨U.tracks,fun i => ⟨translation a (d i) '' (U.cell i).val,
      polygon_image_translation _ (U.cell i).property⟩⟩

noncomputable def shiftEquiv (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing) :
    U.Point ≃ (shifted U d).Point where
  toFun x := ⟨(x.val.1,translate a (d x.val.1) x.val.2),⟨x.val.2,x.property,rfl⟩⟩
  invFun y := ⟨(y.val.1,translate a (-d y.val.1) y.val.2),by
    obtain ⟨x,hx,he⟩ := y.property
    change translate a (-d y.val.1) y.val.2∈(U.cell y.val.1).val
    rw [←he]
    simpa only [translation_apply,←translate_add,neg_add_cancel,translate_zero] using hx⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl (by
      change translate a (-d x.val.1) (translate a (d x.val.1) x.val.2)=x.val.2
      rw [←translate_add,neg_add_cancel,translate_zero])
  right_inv y := by
    apply Subtype.ext
    exact Prod.ext rfl (by
      change translate a (d y.val.1) (translate a (-d y.val.1) y.val.2)=y.val.2
      rw [←translate_add,add_neg_cancel,translate_zero])

noncomputable def shiftArrow (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing) :
    U ⟶ shifted U d where
  toEquiv := shiftEquiv U d
  hasTable := by
    let c : Fin U.tracks → Chart (a:=a) U.tracks U.tracks := fun i => ⟨i,i,d i,U.cell i⟩
    refine ⟨Finset.univ.image c,?_,?_⟩
    · intro k hk
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hk
      intro x hx
      exact ⟨hx,rfl⟩
    · intro x
      exact ⟨c x.val.1,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl,x.property⟩

@[simp] theorem shiftArrow_apply (U : PolygonObject a) (d : Fin U.tracks → CutRing × CutRing)
    (x : U.Point) : (shiftArrow U d).toEquiv x=
      ⟨(x.val.1,translate a (d x.val.1) x.val.2),⟨x.val.2,x.property,rfl⟩⟩ := rfl

variable {κ : Type} [Fintype κ]

noncomputable def refinement (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    PolygonObject a :=
  ⟨Fintype.card (Fin U.tracks × κ),fun j =>
    let ik := (Fintype.equivFin (Fin U.tracks × κ)).symm j
    ⟨{z | ∃hz : z∈(U.cell ik.1).val,label ⟨(ik.1,z),hz⟩=ik.2},hpoly ik.1 ik.2⟩⟩

noncomputable def refinementEquiv (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    (refinement U label hpoly).Point ≃ U.Point where
  toFun x :=
    ⟨(((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).1,x.val.2),x.property.choose⟩
  invFun y := ⟨((Fintype.equivFin _) (y.val.1,label y),y.val.2),by
    change ∃hz : _∈(U.cell _).val,label ⟨(_,y.val.2),hz⟩=_
    simp only [Equiv.symm_apply_apply]
    exact ⟨y.property,True.intro⟩⟩
  left_inv x := by
    apply Subtype.ext
    change ((Fintype.equivFin (Fin U.tracks × κ))
      (((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).1,
        label ⟨(((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).1,x.val.2),x.property.choose⟩),x.val.2)=
      (x.val.1,x.val.2)
    apply Prod.ext
    · apply (Fintype.equivFin (Fin U.tracks × κ)).symm.injective
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext rfl x.property.choose_spec
    · rfl
  right_inv y := by
    apply Subtype.ext
    exact Prod.ext (by simp) rfl

noncomputable def refinementArrow (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    refinement U label hpoly ⟶ U where
  toEquiv := refinementEquiv U label hpoly
  hasTable := by
    let V := refinement U label hpoly
    let c : Fin V.tracks → Chart (a:=a) V.tracks U.tracks := fun j =>
      ⟨j,((Fintype.equivFin (Fin U.tracks × κ)).symm j).1,0,V.cell j⟩
    refine ⟨Finset.univ.image c,?_,?_⟩
    · intro k hk
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hk
      intro x hx
      refine ⟨hx,?_⟩
      change (((Fintype.equivFin (Fin U.tracks × κ)).symm j).1,x)=
        (((Fintype.equivFin (Fin U.tracks × κ)).symm j).1,translate a 0 x)
      rw [translate_zero]
    · intro x
      exact ⟨c x.val.1,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl,x.property⟩

theorem refinementArrow_positional (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a) :
    Positional (refinementArrow U label hpoly) := fun _ => rfl

theorem refinementArrow_label (U : PolygonObject a) (label : U.Point → κ)
    (hpoly : ∀i k,{z | ∃hz : z∈(U.cell i).val,label ⟨(i,z),hz⟩=k}∈polygonAlgebra a)
    (x : (refinement U label hpoly).Point) :
    label ((refinementArrow U label hpoly).toEquiv x)=
      ((Fintype.equivFin (Fin U.tracks × κ)).symm x.val.1).2 := x.property.choose_spec

end PolygonObject
end PolygonObjectRefinement

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_FilteredHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.StageProductColimit.instEssSurjForallPowerMap _root_.OAI.StageProductColimit.instFullForallPowerMap _root_.OAI.StageProductColimit.instIsEquivalenceForallPowerMap _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits Opposite
namespace StageProductColimit

variable {C D E : Type} [Category.{0} C] [Category.{0} D] [Category.{0} E]
variable (κ : Type)
lemma powerMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    powerMap κ (F⋙G)=powerMap κ F ⋙ powerMap κ G := rfl
lemma powerMap_injective (F : C ⥤ D) (hF : Function.Injective F.obj) :
    Function.Injective (powerMap κ F).obj := by
  intro U V h; funext i; exact hF (congrFun h i)
end StageProductColimit

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageTripleHomology
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace SimpleAmenable.PolygonObject.LabelledStage.Stage
open StageProductColimit IntervalBar IntervalBar.Diagram ColimitTransfer

variable {a n : ℕ} (l m p q : ℕ)
noncomputable abbrev tripleDegree (C : Type) [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] :=
  Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (m+1))) (Fin (l+1))
end SimpleAmenable.PolygonObject.LabelledStage.Stage

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PolygonComponentCompletion
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.ladderProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_braided _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_monoidal _root_.OAI.SimpleAmenable.PolygonObject.positionalProperty_multiplicative _root_.OAI.SimpleAmenable.PolygonObject.stringGroupoid_isIso _root_.OAI.SimpleAmenable.PolygonObject.stringReindex_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instMetricSpaceGenericSquare _root_.OAI.SimpleAmenable.instTopologicalSpaceGenericSquare _root_.OAI.TranslationFiltered.regular_filtered
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
section PolygonComponentCompletion

open Classical _root_.CategoryTheory
namespace PolygonObject
variable {a : ℕ}

abbrev Component (a : ℕ) := Skeleton (PolygonObject a)
noncomputable abbrev component (U : PolygonObject a) : Component a := toSkeleton U

@[simp] theorem component_sum (U V : PolygonObject a) :
    component (sum U V)=component U*component V :=
  Skeleton.toSkeleton_tensorObj U V

theorem sum_standard (m n : ℕ) : sum (standard a m) (standard a n)=standard a (m+n) := by
  unfold sum standard
  congr 1
  funext i
  induction i using Fin.addCases <;> simp only [Fin.addCases_left,Fin.addCases_right]

@[simp] theorem component_standard_zero : component (standard a 0)=1 := by
  rw [Skeleton.one_eq]
  apply congrArg toSkeleton
  change standard a 0=empty
  unfold standard empty
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] theorem component_standard_add (m n : ℕ) :
    component (standard a (m+n))=component (standard a m)*component (standard a n) := by
  rw [←sum_standard,component_sum]

theorem component_standard_pow (n : ℕ) :
    component (standard a n)=component (standard a 1)^n := by
  induction n with
  | zero => simp
  | succ n hn => rw [component_standard_add,hn,pow_succ]

end PolygonObject
end PolygonComponentCompletion

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_PolygonComponentStable
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
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
noncomputable abbrev componentGenerator (a:ℕ) := PolygonObject.component (PolygonObject.standard a 1)
end SimpleAmenable.PolygonTracks

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_E2Descend
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits HomologicalComplex HomologicalComplex₂
namespace TotalProjection

universe u
variable {R : Type u} [CommRing R]
variable (K : HomologicalComplex₂ (ModuleCat.{u} R) c c)
noncomputable def edgeData (n : ℕ) : FilteredEdge.Data
    (R:=R) (D:=(K.total c).X (n+2)) (A:=(K.total c).X (n+1))
    (B:=(K.total c).X n) (C:=(K.total c).X (n-1)) where
  s := ((K.total c).d (n+2) (n+1)).hom
  d := ((K.total c).d (n+1) n).hom
  e := ((K.total c).d n (n-1)).hom
  ds := ModuleCat.hom_ext_iff.mp ((K.total c).d_comp_d (n+2) (n+1) n)
  ed := ModuleCat.hom_ext_iff.mp ((K.total c).d_comp_d (n+1) n (n-1))
  FD := filtration K (n+2)
  FA := filtration K (n+1)
  FB := filtration K n
  FC := filtration K (n-1)
  monoA := filtration_mono K (n+1)
  monoB := filtration_mono K n
end TotalProjection

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerInjectivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section PlaneCornerInjectivity
open Classical

@[simp] theorem cutForm_zero (a : ℕ) (j : Fin 4) : cutForm a j (0,0)=0 := by
  fin_cases j <;> simp [cutForm]

@[simp] theorem cutForm_neg (a : ℕ) (j : Fin 4) (v : ℝ × ℝ) :
    cutForm a j (-v) = -cutForm a j v := by
  fin_cases j <;> simp [cutForm] <;> ring

end PlaneCornerInjectivity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_PlaneCornerCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section PlaneCornerCoordinates
open Classical

noncomputable def planeDirectionSign (a : ℕ) (v : ℝ × ℝ) : PlaneSectorIndex :=
  fun j => decide (cutForm a j v<0)

end PlaneCornerCoordinates

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_LowerBarComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex SimplicialObject Simplicial Opposite AlgebraicTopology
namespace SimplicialDiagonal
open FreeChains

attribute [local instance 1200] Submodule.module Prod.instModule
variable (X:I ⥤ SSet)
noncomputable def segalTwo : X.obj (op ⦋2⦌) ⟶ X.obj (op ⦋1⦌) ⊗ X.obj (op ⦋1⦌) :=
  CartesianMonoidalCategory.lift (X.map (SimplexCategory.δ (0:Fin 3)).op) (X.map (SimplexCategory.δ (2:Fin 3)).op)
noncomputable def segalKernelMap (q:ℕ) :
    LinearMap.ker (SimplicialFirstFinite.outer (X⋙SSet.homologyFunctor Z q)) →ₗ[ℤ]
      LinearMap.ker (ConnectedProduct.projection (X.obj (op ⦋1⦌)) (X.obj (op ⦋1⦌)) q).hom :=
  ((SSet.homologyMap (segalTwo X) Z q).hom.comp
    (LinearMap.ker (SimplicialFirstFinite.outer (X⋙SSet.homologyFunctor Z q))).subtype).codRestrict _ (by
      intro x
      change ConnectedProduct.projection _ _ q (SSet.homologyMap (segalTwo X) Z q x.val)=0
      apply (ModuleCat.biprodIsoProd _ _).toLinearEquiv.injective
      simp only [map_zero]
      apply Prod.ext
      · change (SSet.homologyMap (segalTwo X) Z q ≫ ConnectedProduct.projection _ _ q ≫ biprod.fst) x.val=0
        simp only [ConnectedProduct.projection,biprod.lift_fst,←SSet.homologyMap_comp,
          segalTwo,CartesianMonoidalCategory.lift_fst]
        exact congrArg Prod.fst x.property
      · change (SSet.homologyMap (segalTwo X) Z q ≫ ConnectedProduct.projection _ _ q ≫ biprod.snd) x.val=0
        simp only [ConnectedProduct.projection,biprod.lift_snd,←SSet.homologyMap_comp,
          segalTwo,CartesianMonoidalCategory.lift_snd]
        exact congrArg Prod.snd x.property)
end SimplicialDiagonal

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_StageSimplicialColimit
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace SimplicialDiagonal

variable {J : Type} [Category.{0} J] [IsFiltered J]
noncomputable instance diagonal_preserves : PreservesColimitsOfShape J diagonal := by
  apply preservesColimitsOfShape_of_evaluation
  intro p
  change PreservesColimitsOfShape J (((evaluation I SSet).obj p) ⋙ (evaluation I (Type)).obj p)
  infer_instance
end SimplicialDiagonal

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TranslationNerve
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite
namespace TranslationNerve
open TranslationFiltered

variable (P:Type) [CommMonoid P]
lemma lift_project (n:ℕ) (q:Q P) (s:B P n) : lift P n q s ⋙ ActionCategory.π P (Q P)=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f; simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]; rfl
  · intro i; exact Subsingleton.elim _ _
lemma lift_recover (n:ℕ) (s:ComposableArrows (C P) n) :
    lift P n s.left.back (s ⋙ ActionCategory.π P (Q P))=s := by
  apply CategoryTheory.Functor.ext
  · intro i j f; apply Subtype.ext
    erw [CategoryOfElements.comp_val,CategoryOfElements.comp_val]
    simp only [SingleObj.comp_as_mul,eqToHom_val,one_mul,mul_one]
    rfl
  · intro i
    apply (ActionCategory.objEquiv P (Q P)).symm.injective
    exact (s.map (homOfLE (Fin.zero_le i))).property
noncomputable def coordinates (n:ℕ) : ComposableArrows (C P) n ≃ Q P × B P n where
  toFun s := (s.left.back,s ⋙ ActionCategory.π P (Q P))
  invFun x := lift P n x.1 x.2
  left_inv := lift_recover P n
  right_inv x := Prod.ext (lift_left P n x.1 x.2) (lift_project P n x.1 x.2)
lemma smul_left (n:ℕ) (q:Q P) (s:ComposableArrows (C P) n) :
    (q • s).left.back=q*s.left.back := rfl
lemma smul_project (n:ℕ) (q:Q P) (s:ComposableArrows (C P) n) :
    (q • s) ⋙ ActionCategory.π P (Q P)=s ⋙ ActionCategory.π P (Q P) := by
  apply CategoryTheory.Functor.ext
  · intro i j f; simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]; rfl
  · intro i; exact Subsingleton.elim _ _
lemma smul_lift (n:ℕ) (q r:Q P) (s:B P n) :
    q • lift P n r s=lift P n (q*r) s := by
  apply (coordinates P n).injective
  apply Prod.ext
  · change (q • lift P n r s).left.back=(lift P n (q*r) s).left.back
    rw [smul_left,lift_left,lift_left]
  · change (q • lift P n r s) ⋙ ActionCategory.π P (Q P)=lift P n (q*r) s ⋙ ActionCategory.π P (Q P)
    rw [smul_project,lift_project,lift_project]
noncomputable def simplicial : SimplicialObject (Action (Type) (Q P)) where
  obj n := Action.ofMulAction (Q P) (ComposableArrows (C P) n.unop.len)
  map f := { hom := (nerve (C P)).map f
             comm _ := by ext s; rfl }
  map_id _ := by ext s; rfl
  map_comp _ _ := by ext s; rfl
end TranslationNerve

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
noncomputable def actionCoordinates (n:ℕ) :
    (simplicial P).obj (op ⦋n⦌) ≅ Action.leftRegular (Q P) ⊗ Action.trivial (Q P) (B P n) :=
  Action.mkIso (coordinates P n).toIso (by
    intro q
    ext s
    exact Prod.ext (smul_left P n q s) (smul_project P n q s))
noncomputable def linear : SimplicialObject (Rep ℤ (Q P)) := simplicial P ⋙ Rep.linearization ℤ (Q P)
noncomputable def complex : ChainComplex (Rep ℤ (Q P)) ℕ := AlternatingFaceMapComplex.obj (linear P)
noncomputable def freeIso (n:ℕ) : (complex P).X n ≅ Rep.free ℤ (Q P) (B P n) :=
  (Rep.linearization ℤ (Q P)).mapIso (actionCoordinates P n) ≪≫
  (Functor.Monoidal.μIso (Rep.linearization ℤ (Q P)) _ _).symm ≪≫
  tensorIso (Rep.linearizationOfMulActionIso ℤ (Q P) (Q P))
    (Rep.linearizationTrivialIso ℤ (Q P) (B P n)) ≪≫
  Rep.leftRegularTensorTrivialIsoFree ℤ (Q P) (B P n)
noncomputable instance projective (n:ℕ) : Projective ((complex P).X n) :=
  Projective.of_iso (freeIso P n).symm inferInstance
abbrev forgetRep := forget₂ (Rep ℤ (Q P)) (ModuleCat ℤ)
end TranslationNerve

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TranslationCoinvariants
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains Representation

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
noncomputable def orbitRaw (n:ℕ) : ((complex P).X n).V →ₗ[ℤ] (B P n →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun s:ComposableArrows (C P) n=>s ⋙ ActionCategory.π P (Q P)) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap
lemma orbitRaw_single (n:ℕ) (s:ComposableArrows (C P) n) (z:ℤ) :
    orbitRaw P n (MonoidAlgebra.single s z)=Finsupp.single (s ⋙ ActionCategory.π P (Q P)) z := by
  change Finsupp.lmapDomain ℤ ℤ _ (Finsupp.single s z)=_
  simp only [Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
lemma orbitRaw_invariant (n:ℕ) (q:Q P) : orbitRaw P n ∘ₗ ((complex P).X n).ρ q=orbitRaw P n := by
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change orbitRaw P n (Representation.linearize ℤ (Q P) ((simplicial P).obj (op ⦋n⦌)) q
    (MonoidAlgebra.single s 1)) = orbitRaw P n (MonoidAlgebra.single s 1)
  erw [Representation.linearize_single,orbitRaw_single,orbitRaw_single]
  exact congrArg (fun t => Finsupp.single t (1:ℤ)) (smul_project P n q s)
noncomputable def orbitForward (n:ℕ) : (Rep.coinvariantsFunctor ℤ (Q P)).obj ((complex P).X n) ⟶
    (ModuleCat.free ℤ).obj (B P n) :=
  ModuleCat.ofHom (Coinvariants.lift _ (orbitRaw P n) (orbitRaw_invariant P n))
noncomputable def orbitBackward (n:ℕ) : (ModuleCat.free ℤ).obj (B P n) ⟶
    (Rep.coinvariantsFunctor ℤ (Q P)).obj ((complex P).X n) :=
  ModuleCat.freeDesc (↾fun s=>Coinvariants.mk _ (MonoidAlgebra.single (lift P n 1 s) 1))
lemma orbitForward_mk (n:ℕ) (s:ComposableArrows (C P) n) (z:ℤ) :
    orbitForward P n (Coinvariants.mk _ (MonoidAlgebra.single s z)) =
      Finsupp.single (s ⋙ ActionCategory.π P (Q P)) z := orbitRaw_single P n s z
lemma orbitBackward_mk (n:ℕ) (s:B P n) : orbitBackward P n (ModuleCat.freeMk s)=
    Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single (lift P n 1 s) 1) :=
  ModuleCat.freeDesc_apply _ s
lemma mk_lift_one (n:ℕ) (s:ComposableArrows (C P) n) :
    Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single (lift P n 1 (s ⋙ ActionCategory.π P (Q P))) 1) =
      Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single s 1) := by
  have h := Coinvariants.mk_self_apply ((complex P).X n).ρ s.left.back
    (MonoidAlgebra.single (lift P n 1 (s ⋙ ActionCategory.π P (Q P))) 1)
  change Coinvariants.mk _ (Representation.linearize ℤ (Q P) ((simplicial P).obj (op ⦋n⦌)) s.left.back _)=_ at h
  erw [Representation.linearize_single] at h
  change Coinvariants.mk ((complex P).X n).ρ
    (MonoidAlgebra.single (s.left.back • lift P n 1 (s ⋙ ActionCategory.π P (Q P))) 1)=_ at h
  erw [smul_lift,mul_one,lift_recover] at h
  exact h.symm
noncomputable def orbitIso (n:ℕ) : (Rep.coinvariantsFunctor ℤ (Q P)).obj ((complex P).X n) ≅
    (ModuleCat.free ℤ).obj (B P n) where
  hom := orbitForward P n
  inv := orbitBackward P n
  hom_inv_id := by
    apply Rep.coinvariantsFunctor_hom_ext
    apply ModuleCat.hom_ext
    apply MonoidAlgebra.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change orbitBackward P n (orbitForward P n (Coinvariants.mk _ (MonoidAlgebra.single s 1))) =
      Coinvariants.mk ((complex P).X n).ρ (MonoidAlgebra.single s 1)
    erw [orbitForward_mk]
    change orbitBackward P n (ModuleCat.freeMk _) = _
    rw [orbitBackward_mk]
    exact mk_lift_one P n s
  inv_hom_id := by
    apply ModuleCat.free_hom_ext
    intro s
    change orbitForward P n (orbitBackward P n (ModuleCat.freeMk s))=ModuleCat.freeMk s
    erw [orbitBackward_mk,orbitForward_mk,lift_project]
    rfl
lemma orbit_natural {n m:SimplexCategoryᵒᵖ} (f:n⟶m) :
    (orbitIso P n.unop.len).hom ≫ (ModuleCat.free ℤ).map ((nerve (SingleObj P)).map f)=
    (Rep.coinvariantsFunctor ℤ (Q P)).map ((linear P).map f) ≫ (orbitIso P m.unop.len).hom := by
  apply Rep.coinvariantsFunctor_hom_ext
  apply ModuleCat.hom_ext
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  change (ModuleCat.free ℤ).map ((nerve (SingleObj P)).map f)
    (orbitForward P n.unop.len (Coinvariants.mk _ (MonoidAlgebra.single s 1))) =
    orbitForward P m.unop.len (Coinvariants.mk _ (Representation.linearizeMap ((simplicial P).map f)
      (MonoidAlgebra.single s 1)))
  erw [orbitForward_mk,Representation.linearizeMap_single,orbitForward_mk]
  change (ModuleCat.free ℤ).map _ (ModuleCat.freeMk _) = ModuleCat.freeMk _
  erw [ModuleCat.free_map_apply]
  rfl
end TranslationNerve

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology
namespace TranslationNerve
open TranslationFiltered FreeChains

attribute [local instance 1200] Rep.hV2
variable (P:Type) [CommMonoid P]
noncomputable def unitCoinvariantsIso : (Rep.coinvariantsTensor ℤ (Q P)).obj (Rep.trivial ℤ (Q P) ℤ) ≅
    Rep.coinvariantsFunctor ℤ (Q P) :=
  Functor.isoWhiskerRight (leftUnitorNatIso (Rep ℤ (Q P))) (Rep.coinvariantsFunctor ℤ (Q P)) ≪≫
    Functor.leftUnitor _

end TranslationNerve

end

end OAI
end


