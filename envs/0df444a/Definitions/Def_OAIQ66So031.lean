-- Prove2me | Definitions.Def_OAIQ66So031
-- name    : OAIQ66So031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:46:51.82953+00:00
-- url     : https://prove2.me/theorems/531de06c-992d-4d1b-aa37-1ca71fa3b5da
-- title:
--   Definitions bundle OAIQ66So031 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 19 definitions, 9 instances and 21 theorems. The definitions and types are `OAI.SimpleFInftyOvergroups.SourceModel.Keys`, `OAI.SimpleFInftyOvergroups.SourceModel.P₃`, `OAI.SimpleFInftyOvergroups.SourceModel.Sigma`, `OAI.SimpleFInftyOvergroups.SourceModel.Syntax`, `OAI.SimpleFInftyOvergroups.SourceModel.wf`, `OAI.TwistedBrin.Basis.CutBasis.lowerEquiv`, `OAI.TwistedBrin.Basis.CutDown.nearInclude`, `OAI.TwistedBrin.Basis.CutDown.upperInterval`, `OAI.TwistedBrin.Basis.CutSelections.properBooleanFaces`, `OAI.TwistedBrin.Basis.CutSelections.properOfInterval`, `OAI.TwistedBrin.Basis.CutSelections.properToInterval`, `OAI.TwistedBrin.Basis.Matching.contractPair`, `OAI.TwistedBrin.Basis.Matching.fiberInclusion`, `OAI.TwistedBrin.Basis.Matching.fiberResolution`, `OAI.TwistedBrin.Basis.Matching.ground`, `OAI.TwistedBrin.Basis.Matching.projectPair`, `OAI.TwistedBrin.Basis.Matching.selectedPair`, `OAI.TwistedBrin.Basis.ancestor`, `OAI.TwistedBrin.Basis.properCore`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_FiniteIndexProducts`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/FiniteIndexProducts.lean), [`FiniteType_OrderChainsExactInOfDirected`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/OrderChainsExactInOfDirected.lean), [`FiniteType_TwistedBrinBasisCutBasis`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisCutBasis.lean), [`FiniteType_TwistedBrinBasisFirstCut`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisFirstCut.lean), [`FiniteType_TwistedBrinBasisGroundMatching`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinBasisGroundMatching.lean), [`FiniteType_TwistedBrinPattern`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinPattern.lean), [`FiniteType_TwistedBrinPatternFactor`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinPatternFactor.lean), [`FiniteType_TwistedBrinPrefix`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinPrefix.lean), [`FiniteType_TwistedBrinRangeChartRestricts`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/TwistedBrinRangeChartRestricts.lean), [`SimpleOvergroups_SourceModel`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/SimpleOvergroups/SourceModel.lean).
--
--   **Imports.** It imports the bundles `OAIQ66So027`, `OAIQ66So028` and `OAIQ66So029` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ66So032`; the statements `OAI.TwistedBrin.Basis.CutBasis.lower_exactSet` and `OAI.TwistedBrin.Basis.CutBasis.sublevel_cocycle_trivial`; the proofs of `OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented`, `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates`, `OAI.TwistedBrin.Basis.CutBasis.lower_exactSet` and `OAI.TwistedBrin.Basis.CutBasis.sublevel_cocycle_trivial`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So027
import Definitions.Def_OAIQ66So028
import Definitions.Def_OAIQ66So029

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinRangeChartRestricts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Basis.vertexPermutationHom_ker_finiteIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

instance instPartialOrder : PartialOrder (Basis ρ) where
  le := Refines ρ
  le_refl := refines_refl ρ
  le_trans := fun _ _ _ => refines_trans ρ
  le_antisymm := fun _ _ => refines_antisymm ρ

noncomputable def ancestor {B C : Basis ρ} (hBC : B ≤ C) (c : C) : B := (hBC c).choose
lemma ancestor_restricts {B C : Basis ρ} (hBC : B ≤ C) (c : C) :
    GermBrick.Restricts ρ c.1 (ancestor ρ hBC c).1 := (hBC c).choose_spec

lemma ancestor_surjective {B C : Basis ρ} (hBC : B ≤ C) : Function.Surjective (ancestor ρ hBC) := by
  intro b
  obtain ⟨x,hx⟩ := GermBrick.region_nonempty ρ b.1
  obtain ⟨c,hc,_⟩ := C.partition x
  refine ⟨c,?_⟩
  exact eq_of_common_point ρ B
    (GermBrick.region_subset_of_restricts ρ (ancestor_restricts ρ hBC c) hc) hx

lemma rank_mono {B C : Basis ρ} (hBC : B ≤ C) : rank ρ B ≤ rank ρ C := by
  rw [rank_eq_card,rank_eq_card]
  exact Fintype.card_le_of_surjective _ (ancestor_surjective ρ hBC)

lemma eq_of_le_of_rank_eq {B C : Basis ρ} (hBC : B ≤ C) (hr : rank ρ B = rank ρ C) : B = C := by
  classical
  have hi : Function.Injective (ancestor ρ hBC) := by
    exact ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨ancestor_surjective ρ hBC,by simpa only [rank_eq_card] using hr.symm⟩).injective
  have he (c : C) : c.1 = (ancestor ρ hBC c).1 := by
    apply GermBrick.eq_of_restricts_of_region_eq ρ (ancestor_restricts ρ hBC c)
    apply Set.Subset.antisymm (GermBrick.region_subset_of_restricts ρ (ancestor_restricts ρ hBC c))
    intro x hx
    obtain ⟨d,hd,_⟩ := C.partition x
    have ha : ancestor ρ hBC d = ancestor ρ hBC c := eq_of_common_point ρ B
      (GermBrick.region_subset_of_restricts ρ (ancestor_restricts ρ hBC d) hd) hx
    rwa [hi ha] at hd
  apply refines_antisymm ρ hBC
  intro b
  obtain ⟨c,hc⟩ := ancestor_surjective ρ hBC b
  refine ⟨c,?_⟩
  have hb : c.1 = b.1 := (he c).trans (congrArg Subtype.val hc)
  rw [hb]
  exact GermBrick.restricts_refl ρ _

lemma rank_strictMono : StrictMono (rank ρ) := by
  intro B C h
  apply lt_of_le_of_ne (rank_mono ρ h.le)
  intro he
  exact h.ne (eq_of_le_of_rank_eq ρ h.le he)

end Basis

end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPrefix
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
namespace Basis

namespace Forest
variable {ρ}

lemma refines {B C : Basis ρ} (F : Forest ρ B C) : B ≤ C := by
  intro c
  obtain ⟨i,rfl⟩ := F.leaves.surjective c
  refine ⟨i.1,chart ρ B i.1,Pattern.leafPrefix (F.pattern i.1) i.2,?_,(F.chart_eq i).symm⟩
  exact (GermBrick.mk_representative ρ i.1.val).symm

end Forest

lemma cutRefines_antisymm {B C : Basis ρ} (hBC : CutRefines ρ B C) (hCB : CutRefines ρ C B) : B = C :=
  le_antisymm hBC.some.refines hCB.some.refines
lemma le_of_cutRefines {B C : Basis ρ} (h : CutRefines ρ B C) : B ≤ C := h.some.refines

end Basis
end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPattern
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrder _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut _root_.OAI.TwistedBrin.Basis.pairPermutationHom_ker_finiteIndex _root_.OAI.TwistedBrin.Pattern.leavesNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin
section
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Basis.Forest
variable {B C : Basis ρ}

lemma eq_of_all_leaf (F : Forest ρ B C) (h : ∀ b, F.pattern b = .leaf) : B = C := by
  apply eq_of_le_of_rank_eq ρ F.refines
  rw [rank_eq_card,rank_eq_card]
  have hc := Fintype.card_congr F.leaves
  rw [Fintype.card_sigma] at hc
  have hf (b : B) : Fintype.card (Pattern.Leaves (F.pattern b)) = 1 := by
    rw [h b]
    change Fintype.card Unit = 1
    exact Fintype.card_unique
  simp_rw [hf] at hc
  simpa using hc

end Basis.Forest
end

end TwistedBrin

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinPatternFactor
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutSelections.instPartialOrderProper _root_.OAI.TwistedBrin.Basis.instFintypeFirstCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v

namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

lemma Forest.firstGrid_ne {B C : Basis ρ} (F : Forest ρ B C) (h : B ≠ C) :
    F.firstGrid ρ ≠ B := by
  intro he
  have hh : (fun b => Pattern.firstCoordinates (F.pattern b)) = (fun _ => ∅) :=
    gridExpansion_injective ρ B (he.trans (gridExpansion_empty ρ B).symm)
  apply h
  apply F.eq_of_all_leaf
  intro b
  by_contra hn
  have hb := Pattern.firstCoordinates_nonempty hn
  rw [congrFun hh b] at hb
  exact Finset.not_nonempty_empty hb

lemma firstCore_ne {B C : Basis ρ} (h : CutRefines ρ B C) (hne : B ≠ C) : firstCore ρ h ≠ B :=
  (Classical.choice h).firstGrid_ne ρ hne

end

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

namespace CutInterval
variable {ρ} {B C : Basis ρ}
instance instPartialOrder : PartialOrder (CutInterval ρ B C) where
  le D E := CutRefines ρ D.val E.val
  le_refl D := cutRefines_refl ρ D.val
  le_trans _ _ _ := cutRefines_trans ρ
  le_antisymm _ _ h k := ext (cutRefines_antisymm ρ h k)
lemma core_mono : Monotone (core : CutInterval ρ B C → CutInterval ρ B C) := by
  intro D E h
  exact firstCore_mono ρ D.lower h E.lower

lemma core_ne_bottom (D : CutInterval ρ B C) (h : D.val ≠ B) : D.core.val ≠ B :=
  firstCore_ne ρ D.lower h.symm
lemma core_ne_top (D : CutInterval ρ B C) (h : D.val ≠ C) : D.core.val ≠ C := by
  intro he
  apply h
  apply cutRefines_antisymm ρ D.upper
  have hh : CutRefines ρ D.core.val D.val := firstCore_upper ρ D.lower
  simpa only [he] using hh
end CutInterval

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)
lemma to_mono : Monotone (toInterval h) := by
  intro K L hKL
  exact gridExpansion_mono ρ B K.val L.val hKL
lemma of_mono : Monotone (ofInterval h) := by
  intro D E hDE
  exact firstCuts_mono ρ D.lower hDE E.lower

end CutSelections
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisFirstCut
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis

variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)

instance instPartialOrderProperCutInterval (B C : Basis ρ) : PartialOrder (ProperCutInterval ρ B C) :=
  inferInstanceAs (PartialOrder {D : CutInterval ρ B C // D.val ≠ B ∧ D.val ≠ C})

noncomputable def properCore {B C : Basis ρ} :
    ProperCutInterval ρ B C →o ProperCutInterval ρ B C where
  toFun D := ⟨D.val.core,D.val.core_ne_bottom D.property.1,D.val.core_ne_top D.property.2⟩
  monotone' := fun _ _ h => CutInterval.core_mono h

namespace CutSelections
variable {ρ} {B C : Basis ρ} (h : CutRefines ρ B C)

lemma grid_ne_top (htop : firstCore ρ h ≠ C) (K : CutSelections ρ h) :
    (toInterval h K).val ≠ C := by
  intro hk
  apply htop
  have hK : CutRefines ρ (toInterval h K).val (firstCore ρ h) :=
    gridExpansion_mono ρ B K.val (firstCuts ρ h) K.property
  have hC : CutRefines ρ C (firstCore ρ h) := by simpa only [hk] using hK
  exact cutRefines_antisymm ρ (firstCore_upper ρ h) hC

noncomputable def properToInterval : Proper h →o ProperCutInterval ρ B C where
  toFun K := ⟨toInterval h K.val,K.property⟩
  monotone' := fun _ _ hk => to_mono h hk
noncomputable def properOfInterval : ProperCutInterval ρ B C →o Proper h where
  toFun D := ⟨ofInterval h D.val,by
    rw [to_of]
    exact ⟨D.val.core_ne_bottom D.property.1,D.val.core_ne_top D.property.2⟩⟩
  monotone' := fun _ _ hd => of_mono h hd

noncomputable def properBooleanFaces (htop : firstCore ρ h ≠ C) :
    Proper h ≃o {T : Finset (FirstCut ρ h) // T ≠ ∅} where
  toFun K := ⟨selected h K.val,fun he => K.property.1 ((grid_eq_bottom_iff h K.val).mpr he)⟩
  invFun T := ⟨fromSelected h T.val,
    (fun he => T.property ((selected_fromSelected h T.val).symm.trans
      ((grid_eq_bottom_iff h _).mp he))),grid_ne_top h htop _⟩
  left_inv K := Subtype.ext (fromSelected_selected h K.val)
  right_inv T := Subtype.ext (selected_fromSelected h T.val)
  map_rel_iff' := (booleanEquiv h).map_rel_iff'
end CutSelections
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_OrderChainsExactInOfDirected
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin.Basis

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

lemma present_mono {B D : Basis ρ} (hBD : CutRefines ρ B D) (hDC : CutRefines ρ D C)
    {N : Finset I} (h : M.Present B N) : M.Present D N := by
  intro i hi q
  let e : B := ⟨((M.edge i).endpoint q).val,h i hi q⟩
  let c := (M.edge i).endpoint q
  let d := ancestor ρ hDC.some.refines c
  have hcd := ancestor_restricts ρ hDC.some.refines c
  obtain ⟨e',he'⟩ := hBD.some.refines d
  have hee : e = e' := refines_ancestor_unique ρ (C := C)
    (GermBrick.restricts_refl ρ c.val) (GermBrick.restricts_trans ρ hcd he')
  have hdc : GermBrick.Restricts ρ d.val c.val := by
    have hh : e'.val = c.val := (congrArg Subtype.val hee).symm
    rwa [hh] at he'
  have hreg : GermBrick.region ρ c.val = GermBrick.region ρ d.val :=
    Set.Subset.antisymm (GermBrick.region_subset_of_restricts ρ hcd)
      (GermBrick.region_subset_of_restricts ρ hdc)
  have he := GermBrick.eq_of_restricts_of_region_eq ρ hcd hreg
  exact he.symm ▸ d.property

lemma contract_mono {B D : Basis ρ} (F : Forest ρ B D) (hDC : CutRefines ρ D C) {N K : Finset I}
    (hKN : K ⊆ N) (hB : M.Present B N) (hD : M.Present D K) :
    CutRefines ρ (M.contract B N hB) (M.contract D K hD) := by
  classical
  let P : M.Roots B N → Pattern S := Sum.elim
    (fun i => if i.val ∈ K then .leaf else .split (M.edge i.val).coordinate .leaf .leaf)
    (fun b => F.pattern b.val)
  apply cutRefines_ofChartPartition ρ (M.rootChart B N) (M.rootPartition B N hB)
    (M.contract D K hD) P
  intro r j
  cases r with
  | inl i =>
    by_cases hi : i.val ∈ K
    · have hp : P (Sum.inl i) = .leaf := by simp [P,hi]
      have hj : Pattern.leafPrefix (P (Sum.inl i)) j = Prefix.empty := by
        revert j
        rw [hp]
        intro j
        rfl
      rw [hj,LocalEmbedding.ofPrefix_empty,LocalEmbedding.comp_identity]
      exact (M.mem_contract D K hD _).mpr (Or.inl ⟨i.val,hi,rfl⟩)
    · have hj : ∃ q : Bool, GermBrick.mk ρ (LocalEmbedding.comp ρ
          (M.rootChart B N (Sum.inl i)) (LocalEmbedding.ofPrefix ρ
            (Pattern.leafPrefix (P (Sum.inl i)) j))) = ((M.edge i.val).endpoint q).val := by
        have hp : P (Sum.inl i) = .split (M.edge i.val).coordinate .leaf .leaf := by simp [P,hi]
        revert j
        rw [hp]
        intro j
        cases j with
        | inl j => exact ⟨false,by simpa [Pattern.leafPrefix,Prefix.append_empty,rootChart,Merge.endpoint]
            using (M.edge i.val).left_eq⟩
        | inr j => exact ⟨true,by simpa [Pattern.leafPrefix,Prefix.append_empty,rootChart,Merge.endpoint]
            using (M.edge i.val).right_eq⟩
      obtain ⟨q,hj⟩ := hj
      rw [hj]
      apply (M.mem_contract D K hD _).mpr
      refine Or.inr ⟨?_,?_⟩
      · exact M.present_mono ⟨F⟩ hDC hB i.val i.property q
      · intro k hk p he
        exact hi ((M.endpoint_eq he).1.symm ▸ hk)
  | inr b =>
    have hj : GermBrick.mk ρ (LocalEmbedding.comp ρ (M.rootChart B N (Sum.inr b))
        (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P (Sum.inr b)) j))) =
        (F.leaves ⟨b.val,j⟩).val := F.chart_eq ⟨b.val,j⟩
    rw [hj]
    apply (M.mem_contract D K hD _).mpr
    refine Or.inr ⟨(F.leaves ⟨b.val,j⟩).property,?_⟩
    intro k hk q he
    have hrest : GermBrick.Restricts ρ (F.leaves ⟨b.val,j⟩).val b.val.val := by
      refine ⟨chart ρ B b.val,Pattern.leafPrefix (F.pattern b.val) j,
        (chart_germ ρ B b.val).symm,(F.chart_eq ⟨b.val,j⟩).symm⟩
    let e : B := ⟨((M.edge k).endpoint q).val,hB k (hKN hk) q⟩
    have heq : b.val = e := refines_ancestor_unique ρ (C := D) hrest (by
      rw [he]
      exact GermBrick.restricts_refl ρ e.val)
    exact b.property k (hKN hk) q (congrArg Subtype.val heq)
end Matching
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisGroundMatching
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroup _root_.OAI.TwistedBrin.Basis.CutBasis.instMulActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace CutDown
variable {C : Basis ρ}
instance instPartialOrder : PartialOrder (CutDown C) where
  le B D := CutRefines ρ B.val D.val
  le_refl B := cutRefines_refl ρ B.val
  le_trans _ _ _ := cutRefines_trans ρ
  le_antisymm _ _ h k := ext (cutRefines_antisymm ρ h k)
lemma rank_lt_top (B : CutDown C) : rank ρ B.val < rank ρ C :=
  (rank_strictMono ρ) (lt_of_le_of_ne (le_of_cutRefines ρ B.upper) B.ne)

noncomputable def upperInterval (B : CutDown C) : {D : CutDown C // B < D} ≃o
    ProperCutInterval ρ B.val C where
  toFun D := ⟨⟨D.val.val,D.property.le,D.val.upper⟩,
    (fun he => D.property.ne (ext he.symm)),D.val.ne⟩
  invFun D := ⟨⟨D.val.val,D.val.upper,D.property.2⟩,
    lt_of_le_of_ne D.val.lower (fun he => D.property.1 (congrArg CutDown.val he).symm)⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_rel_iff' := Iff.rfl

def nearInclude (C : Basis ρ) (m : ℕ) : Near C m →o CutDown C := ⟨Subtype.val,fun _ _ h => h⟩

end CutDown

namespace Matching
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)

namespace Pair
variable {M} {m : ℕ}
instance instPartialOrder : PartialOrder (M.Pair m) where
  le x y := x.base ≤ y.base ∧ y.selected ⊆ x.selected
  le_refl _ := ⟨le_rfl,Finset.Subset.refl _⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1,k.2.trans h.2⟩
  le_antisymm _ _ h k := ext (le_antisymm h.1 k.1) (Finset.Subset.antisymm k.2 h.2)
end Pair

def projectPair (m : ℕ) : M.Pair m →o CutDown.Near C m := ⟨Pair.base,fun _ _ h => h.1⟩

noncomputable def contractPair (m : ℕ) : M.Pair m →o CutDown C where
  toFun x := ⟨M.contract x.base.val.val x.selected x.present,
    cutRefines_trans ρ (M.contract_cutRefines _ _ _) x.base.val.upper,by
      intro he
      have hr := M.rank_contract x.base.val.val x.selected x.present
      have hp := Finset.card_pos.mpr x.nonempty
      have hb := x.base.val.rank_lt_top
      rw [he] at hr
      omega⟩
  monotone' := by
    intro x y h
    exact M.contract_mono h.1.some y.base.val.upper h.2 x.present y.present

noncomputable def ground : GroundFaces (I := I) →o CutDown C where
  toFun N := ⟨M.contract C N.val (M.present_top N.val),M.contract_cutRefines _ _ _,by
    intro he
    have hr := M.rank_contract C N.val (M.present_top N.val)
    have hp := Finset.card_pos.mpr N.property
    rw [he] at hr
    omega⟩
  monotone' := by
    intro N K h
    exact M.contract_mono (Forest.refl C) (cutRefines_refl ρ C) h (M.present_top _) (M.present_top _)

def selectedPair (m : ℕ) : M.Pair m →o GroundFaces (I := I) :=
  ⟨fun x => ⟨x.selected,x.nonempty⟩,fun _ _ h => h.2⟩

noncomputable def fiberResolution (m : ℕ) (B : CutDown.Near C m) :
    {x : M.Pair m // M.projectPair m x ≤ B} →o M.AvailableFaces B.val where
  toFun x := ⟨x.val.selected,x.val.nonempty,by
    intro i hi
    apply (M.mem_available B.val.val Finset.univ i).mpr
    exact ⟨Finset.mem_univ _,M.present_mono x.property B.val.upper x.val.present i hi⟩⟩
  monotone' := fun _ _ h => h.2

noncomputable def fiberInclusion (m : ℕ) (B : CutDown.Near C m) :
    M.AvailableFaces B.val →o {x : M.Pair m // M.projectPair m x ≤ B} where
  toFun N := ⟨⟨B,N.val,N.property.1,fun i hi =>
    ((M.mem_available B.val.val Finset.univ i).mp (N.property.2 hi)).2⟩,le_rfl⟩
  monotone' := fun _ _ h => ⟨le_rfl,h⟩

end Matching
end TwistedBrin.Basis

namespace TwistedBrin.Basis
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace CutBasis
instance instPartialOrder : PartialOrder (CutBasis ρ) where
  le B C := CutRefines ρ B.val C.val
  le_refl B := cutRefines_refl ρ B.val
  le_trans _ _ _ := cutRefines_trans ρ
  le_antisymm _ _ h k := ext (cutRefines_antisymm ρ h k)
noncomputable def lowerEquiv (C : CutBasis ρ) : Set.Iio C ≃o CutDown C.val where
  toFun B := ⟨B.val.val,(show B.val < C from B.property).le,
    fun he => (show B.val < C from B.property).ne (ext he)⟩
  invFun B := ⟨⟨B.val⟩,lt_of_le_of_ne B.upper (fun he => B.ne (congrArg CutBasis.val he))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
end CutBasis
end TwistedBrin.Basis

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TwistedBrinBasisCutBasis
attribute [-instance] _root_.OAI.EquivariantOrderChains.covariantPosetAction _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
universe u v
namespace TwistedBrin.Basis.CutBasis
open ActionTransport PosetTransport
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
instance instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroup : IsMonotoneAction (localGroup ρ) (CutBasis ρ) where
  mono g _ _ h := translate_cutRefines ρ g h
instance instIsMonotoneActionSubtypePermBoxMemSubgroupLocalGroupElemSublevel (h : ℕ) : IsMonotoneAction (localGroup ρ) (Sublevel (ρ := ρ) h) where
  mono g _ _ h := translate_cutRefines ρ g h
end TwistedBrin.Basis.CutBasis

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexProducts
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

namespace TwistedBrin.Basis.CutBasis
open OrderChainComplex EquivariantOrderChains ActionTransport PosetTransport
variable {A S : Type} [Group A] {ρ : A →* Equiv.Perm S}

instance sublevel_covariant (h : ℕ) :
    CovariantClass (localGroup ρ) (Sublevel (ρ := ρ) h) HSMul.hSMul LE.le where
  elim g _ _ hBC := translate_cutRefines ρ g hBC

end TwistedBrin.Basis.CutBasis

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

abbrev Sigma := ContextualEncoding.Source.Sigma
abbrev P₃ := IdempotentNames.Index (ZMod 3)
abbrev Syntax := ContextualEncoding.Source.Syntax (Γ:=family.Γ) (Q:=family.Q)
local instance instDecidableRelSigmaRel_r4a3fe7_1 : DecidableRel ContextualEncoding.Source.rel := fun _ _ => inferInstanceAs (Decidable (_ < _))
local instance instTrichotomousSigmaRel : Std.Trichotomous ContextualEncoding.Source.rel := ⟨fun a b hab hba => by
  apply Encodable.encode_injective
  change ¬ Encodable.encode a < Encodable.encode b at hab
  change ¬ Encodable.encode b < Encodable.encode a at hba
  omega⟩

abbrev Keys (k : ℕ) := ContextualEncoding.Source.Keys (Γ:=family.Γ) (Q:=family.Q) k
abbrev wf := ContextualEncoding.Source.wf_rel

end
end SimpleFInftyOvergroups.SourceModel

end OAI
end


