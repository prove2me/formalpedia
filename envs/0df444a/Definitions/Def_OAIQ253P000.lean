-- Prove2me | Definitions.Def_OAIQ253P000
-- name    : OAIQ253P000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:43:49.766829+00:00
-- url     : https://prove2.me/theorems/56af5365-c730-4163-a149-f11da0ed8559
-- title:
--   Definitions bundle OAIQ253P000 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1161 declarations of OpenAI's Lean: 491 definitions, 52 inductive types or structures, 4 instances and 614 theorems. The definitions and types are `OAI.PartitionPilot.Attachment.ComponentMeets`, `OAI.PartitionPilot.Attachment.Data`, `OAI.PartitionPilot.Attachment.FreshLe`, `OAI.PartitionPilot.Attachment.IsMeet`, `OAI.PartitionPilot.Attachment.Le`, `OAI.PartitionPilot.Attachment.Templates`, `OAI.PartitionPilot.Attachment.Templates.Fresh`, `OAI.PartitionPilot.Attachment.Templates.Inside`, `OAI.PartitionPilot.Attachment.Templates.base`, `OAI.PartitionPilot.Attachment.Templates.cap`, `OAI.PartitionPilot.Attachment.Templates.data`, `OAI.PartitionPilot.Attachment.Templates.extension`, `OAI.PartitionPilot.Attachment.Templates.oldEmbedding`, `OAI.PartitionPilot.Attachment.Templates.originalFamily`, `OAI.PartitionPilot.Attachment.Templates.represent`, `OAI.PartitionPilot.Attachment.Templates.shadow`, `OAI.PartitionPilot.Attachment.Templates.templateEmbedding`, `OAI.PartitionPilot.Attachment.cut`, `OAI.PartitionPilot.Attachment.idealOrder`, `OAI.PartitionPilot.Attachment.meetOrder`, `OAI.PartitionPilot.Attachment.oldEmbedding`, `OAI.PartitionPilot.Compression.MeetFilter`, `OAI.PartitionPilot.Compression.MeetIso`, `OAI.PartitionPilot.Compression.RecursiveMaps.ActionRectangle`, `OAI.PartitionPilot.Compression.RecursiveMaps.ActionRectangle.toInput`, `OAI.PartitionPilot.Compression.RecursiveMaps.AttachmentHeight.extend`, `OAI.PartitionPilot.Compression.RecursiveMaps.AttachmentHeight.value`, `OAI.PartitionPilot.Compression.RecursiveMaps.BinaryTiles.compression`, `OAI.PartitionPilot.Compression.RecursiveMaps.BinaryTiles.separation`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.IsMeet`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.Label`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.Le`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.Node`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.Related`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.nodeLe`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.order`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.part`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.point`, `OAI.PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data.setoid` and 503 more.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_AssignmentQueryFormulas`, `PartitionPrinciple_Definability_AttachmentOldCodeLaws`, `PartitionPrinciple_Definability_BatchAttachmentRealization`, `PartitionPrinciple_Definability_BoundedChronologyCodes`, `PartitionPrinciple_Definability_BoundedMeetOrderCodes`, `PartitionPrinciple_Definability_CodedTemplateShadowLaws`, `PartitionPrinciple_Definability_CountableSetFormulas`, `PartitionPrinciple_Definability_DecodedFunctionGraphs`, `PartitionPrinciple_Definability_ExternalCopyRelations`, `PartitionPrinciple_Definability_ExternalWordRewriteFormulas`, `PartitionPrinciple_Definability_ExternalWordRewriteRelations`, `PartitionPrinciple_Definability_FiniteWordMapCodes`, `PartitionPrinciple_Definability_FixedTopCodes`, `PartitionPrinciple_Definability_FlatLimitConditionFormulas`, `PartitionPrinciple_Definability_ForcingHistoryOutputFormulas`, `PartitionPrinciple_Definability_GreedyAntichainStepFormulas`, `PartitionPrinciple_Definability_GroundBatchAttachmentGraphs`, `PartitionPrinciple_Definability_GroundDepthSlotCodes`, `PartitionPrinciple_Definability_GroundExternalRequestSetRecognition`, `PartitionPrinciple_Definability_GroundFlatCopyGraphs`, `PartitionPrinciple_Definability_GroundPairCompositions`, `PartitionPrinciple_Definability_GroundPartialFunctionSpaces`, `PartitionPrinciple_Definability_GroundRefinementPairClassGraphs`, `PartitionPrinciple_Definability_GroundTaggedComponentGraphs`, `PartitionPrinciple_Definability_IndexedAttachmentCodes`, `PartitionPrinciple_Definability_LinkedMainTransitionRawCodes`, `PartitionPrinciple_Definability_MainLimitCoverageFormulas`, `PartitionPrinciple_Definability_MainTransitionValidityCodes`, `PartitionPrinciple_Definability_MapFamilyApplicationGraphs`, `PartitionPrinciple_Definability_NatUnionCodes`, `PartitionPrinciple_Definability_NaturalSetCodes`, `PartitionPrinciple_Definability_NaturalStepFormulas`, `PartitionPrinciple_Definability_NonemptyTupleFields`, `PartitionPrinciple_Definability_ParentSupportCodes`, `PartitionPrinciple_Definability_PreparedCertificateCodes`, `PartitionPrinciple_Definability_PresentedGroupCodes`, `PartitionPrinciple_Definability_SeparationFulfillmentCodes`, `PartitionPrinciple_Definability_SerializedChronologyFormulas`, `PartitionPrinciple_Definability_SetPresentations`, `PartitionPrinciple_Definability_StrictLexHeightFormulas`, `PartitionPrinciple_Definability_TaggedExtensionCodes`, `PartitionPrinciple_Definability_TaggedGrowthLayerFormulas`, `PartitionPrinciple_Definability_TaggedSumPresentations`, `PartitionPrinciple_Definability_TaskCapFamilyCodes`, `PartitionPrinciple_Definability_TaskRepresentativeCodes`, `PartitionPrinciple_Definability_TaskTransportFormulas`, `PartitionPrinciple_Definability_UnionEntryFormula`, `PartitionPrinciple_Forcing_DenseInterpolation`, `PartitionPrinciple_Forcing_ExternalAction`, `PartitionPrinciple_Forcing_GroundActionFilterImages`, `PartitionPrinciple_Forcing_GroundActionPostcomposition`, `PartitionPrinciple_Forcing_GroundFilterCopies`, `PartitionPrinciple_Forcing_GroundFixedTopStep`, `PartitionPrinciple_Forcing_GroundMixtureNames`, `PartitionPrinciple_Forcing_GroundNameSequenceValues`, `PartitionPrinciple_Forcing_GroundProductActions`, `PartitionPrinciple_Forcing_GroundRecursiveActions`, `PartitionPrinciple_Forcing_GroundSizeWitnesses`, `PartitionPrinciple_Forcing_GroundSmallFunctionPermutations`, `PartitionPrinciple_Forcing_GroundStoredPreparedFamilyActions`, `PartitionPrinciple_Forcing_GroundUnionSizeWitnesses`, `PartitionPrinciple_Forcing_IdealChain`, `PartitionPrinciple_Forcing_InitialRowForcing`, `PartitionPrinciple_Forcing_OrbitPairGraphNames`, `PartitionPrinciple_Forcing_ProfileTransport`, `PartitionPrinciple_Forcing_RecursiveAction`, `PartitionPrinciple_Forcing_RefinementCoarseImageNames`, `PartitionPrinciple_Forcing_RequestedSupportOwners`, `PartitionPrinciple_Forcing_RootedSupportOwners`, `PartitionPrinciple_Geometry_BinaryTiles`, `PartitionPrinciple_Geometry_CompatibleCopies`, `PartitionPrinciple_Geometry_Compression`, `PartitionPrinciple_Geometry_DecodedGroundGroups`, `PartitionPrinciple_Geometry_ExternalCopyDescent`, `PartitionPrinciple_Geometry_ExternalTranslation`, `PartitionPrinciple_Geometry_FiniteIterationTraces`, `PartitionPrinciple_Geometry_GluingHeights`, `PartitionPrinciple_Geometry_GroundAttachmentEmbeddings`, `PartitionPrinciple_Geometry_GroundBatchAttachment`, `PartitionPrinciple_Geometry_GroundBatchHeightGraphs`, `PartitionPrinciple_Geometry_GroundCompressionHeightSteps`, `PartitionPrinciple_Geometry_GroundConstantBatchLayers`, `PartitionPrinciple_Geometry_GroundContainmentOrders`, `PartitionPrinciple_Geometry_GroundExternalProfilePreservation`, `PartitionPrinciple_Geometry_GroundMainTransitionValidity`, `PartitionPrinciple_Geometry_GroundNaturalNumbers`, `PartitionPrinciple_Geometry_GroundSingleAttachment`, `PartitionPrinciple_Geometry_GroundTemplateIntervalFamilies`, `PartitionPrinciple_Geometry_GrowthLayerSourceCongruence`, `PartitionPrinciple_Geometry_HeightAttachment`, `PartitionPrinciple_Geometry_MainRectangles`, `PartitionPrinciple_Geometry_NodeCoding`, `PartitionPrinciple_Geometry_OutwardSchedule`, `PartitionPrinciple_Geometry_PrincipalBatch`, `PartitionPrinciple_Geometry_RationalOrderBounds`, `PartitionPrinciple_Geometry_RectangleFulfillmentAtBound`, `PartitionPrinciple_Geometry_RectangleTile`, `PartitionPrinciple_Geometry_RepresentativeIndexSteps`, `PartitionPrinciple_Geometry_RequestedOwnerSlotLaws`, `PartitionPrinciple_Geometry_RootedSupportOrder`, `PartitionPrinciple_Geometry_SeparationTileCodes`, `PartitionPrinciple_Geometry_TaskSystem`, `PartitionPrinciple_Geometry_TileStarIncomingCodes`, `PartitionPrinciple_Geometry_TileTreeGluing`, `PartitionPrinciple_Models_CopyQuotient`, `PartitionPrinciple_Models_ExternalCopyQuotient`, `PartitionPrinciple_Models_GroundChoiceEnumerationSteps`, `PartitionPrinciple_Models_GroundCountableQuotients`, `PartitionPrinciple_Models_GroundSuccessorInjections`, `PartitionPrinciple_Models_IncidenceQuotient`, `PartitionPrinciple_Models_RootedGluingQuotient`, `PartitionPrinciple_Transfinite_CountableCoding`, `PartitionPrinciple_Transfinite_ExternalChronologyStageLaws`, `PartitionPrinciple_Transfinite_GluingBirthRanges`, `PartitionPrinciple_Transfinite_GroundBatchBirths`, `PartitionPrinciple_Transfinite_GroundChronologicalBasis`, `PartitionPrinciple_Transfinite_GroundChronologyLayerRelation`, `PartitionPrinciple_Transfinite_GroundChronologyPairs`, `PartitionPrinciple_Transfinite_GroundCoinitialOperations`, `PartitionPrinciple_Transfinite_GroundCompressionBirths`, `PartitionPrinciple_Transfinite_GroundCountableLayerCodes`, `PartitionPrinciple_Transfinite_GroundInvariantSuccessors`, `PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws`, `PartitionPrinciple_Transfinite_GroundMainStageCandidates`, `PartitionPrinciple_Transfinite_GroundMainStageFromCodes`, `PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality`, `PartitionPrinciple_Transfinite_GroundSmallFunctionSpaces`, `PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram`, `PartitionPrinciple_Transfinite_InaccessibleBounds`, `PartitionPrinciple_Transfinite_RecursiveLiftAgreement`, `PartitionPrinciple_Transfinite_RecursiveMaps`, `PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness`, `PartitionPrinciple_Transfinite_StageOneDataBoundLaws`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ253P002` and `OAIQ253P003`.
-- source:
--   OpenAI, The Partition Principle does not imply Choice, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 244; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Partition-Principle-does-not-imply-Choice-September-24-2026/partition-principle-without-choice.pdf; Apache License 2.0); definitions carved from lean/OAI/SetTheory at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple

section
-- module Solutions.OAIQ253_PP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SetPresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization

open Cardinal
open scoped Cardinal
universe u

structure Presentation (A : Type u) where
  carrier : ZFSet.{u}
  encode : A → ZFSet.{u}
  injective : Function.Injective encode
  mem_carrier : ∀ x, x ∈ carrier ↔ ∃ a, encode a = x

namespace Presentation
variable {A B : Type u}

theorem encode_mem (s : Presentation A) (a : A) : s.encode a ∈ s.carrier :=
  (s.mem_carrier _).2 ⟨a, rfl⟩

noncomputable def product (s : Presentation A) (t : Presentation B) : Presentation (A × B) where
  carrier := ZFSet.prod s.carrier t.carrier
  encode a := ZFSet.pair (s.encode a.1) (t.encode a.2)
  injective := by
    intro a b eq
    have parts := ZFSet.pair_inj.1 eq
    exact Prod.ext (s.injective parts.1) (t.injective parts.2)
  mem_carrier x := by
    rw [ZFSet.mem_prod]
    constructor
    · rintro ⟨y, hy, z, hz, eq⟩
      rcases (s.mem_carrier y).1 hy with ⟨a, ha⟩
      rcases (t.mem_carrier z).1 hz with ⟨b, hb⟩
      exact ⟨(a, b), by rw [ha, hb]; exact eq.symm⟩
    · rintro ⟨a, eq⟩
      exact ⟨s.encode a.1, s.encode_mem a.1, t.encode a.2, t.encode_mem a.2, eq.symm⟩

noncomputable def subset (s : Presentation A) (p : A → Prop) : ZFSet.{u} :=
  ZFSet.range (fun a : Subtype p => s.encode a.val)

theorem mem_subset (s : Presentation A) (p : A → Prop) (x : ZFSet.{u}) :
    x ∈ s.subset p ↔ ∃ a, p a ∧ s.encode a = x := by
  rw [subset, ZFSet.mem_range]
  constructor
  · rintro ⟨a, eq⟩
    exact ⟨a.val, a.property, eq⟩
  · rintro ⟨a, h, eq⟩
    exact ⟨⟨a, h⟩, eq⟩

theorem encode_mem_subset (s : Presentation A) (p : A → Prop) (a : A) :
    s.encode a ∈ s.subset p ↔ p a := by
  rw [mem_subset]
  constructor
  · rintro ⟨b, hb, eq⟩
    exact s.injective eq ▸ hb
  · intro h
    exact ⟨a, h, rfl⟩

theorem subset_carrier (s : Presentation A) (p : A → Prop) : s.subset p ⊆ s.carrier := by
  intro x hx
  rcases (s.mem_subset p x).1 hx with ⟨a, _, eq⟩
  exact eq ▸ s.encode_mem a

end Presentation
end PartitionPilot.SetRealization

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedExtensionCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

def taggedExtension (P N : ZFSet.{u}) : ZFSet.{u} :=
  P ∪ ZFSet.prod {P} N

theorem pair_tag_not_mem (P q : ZFSet.{u}) : ZFSet.pair P q ∉ P := by
  intro member
  have first : ZFSet.rank P < ZFSet.rank ({P} : ZFSet.{u}) :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_singleton.2 rfl)
  have second : ZFSet.rank ({P} : ZFSet.{u}) < ZFSet.rank (ZFSet.pair P q) :=
    ZFSet.rank_lt_of_mem (ZFSet.mem_pair.2 (Or.inl rfl))
  exact (lt_irrefl (ZFSet.rank P))
    (first.trans (second.trans (ZFSet.rank_lt_of_mem member)))

theorem mem_taggedExtension {P N z : ZFSet.{u}} :
    z ∈ taggedExtension P N ↔ z ∈ P ∨ ∃ q ∈ N, z = ZFSet.pair P q := by
  constructor
  · intro hz
    rcases ZFSet.mem_union.1 hz with hz | hz
    · exact Or.inl hz
    · obtain ⟨p, hp, q, hq, eq⟩ := ZFSet.mem_prod.1 hz
      exact Or.inr ⟨q, hq, (ZFSet.mem_singleton.1 hp) ▸ eq⟩
  · intro hz
    rcases hz with hz | ⟨q, hq, rfl⟩
    · exact ZFSet.mem_union.2 (Or.inl hz)
    · exact ZFSet.mem_union.2
        (Or.inr (ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩))

theorem old_mem_taggedExtension {P N z : ZFSet.{u}} (hz : z ∈ P) :
    z ∈ taggedExtension P N :=
  mem_taggedExtension.2 (Or.inl hz)

theorem pair_mem_taggedExtension {P N q : ZFSet.{u}} :
    ZFSet.pair P q ∈ taggedExtension P N ↔ q ∈ N := by
  constructor
  · intro h
    rcases mem_taggedExtension.1 h with old | ⟨r, hr, eq⟩
    · exact False.elim (pair_tag_not_mem P q old)
    · exact (ZFSet.pair_inj.1 eq).2.symm ▸ hr
  · intro hq
    exact mem_taggedExtension.2 (Or.inr ⟨q, hq, rfl⟩)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_Compression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot

section

universe u v

structure MeetOrder (α : Type u) where
  le : α → α → Prop
  meet : α → α → α
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b
  meet_le_left : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_meet : ∀ {a b c}, le a b → le a c → le a (meet b c)

theorem meet_comm {α : Type u} (P : MeetOrder α) (a b : α) :
    P.meet a b = P.meet b a := by
  apply P.antisymm
  · exact P.le_meet (P.meet_le_right a b) (P.meet_le_left a b)
  · exact P.le_meet (P.meet_le_right b a) (P.meet_le_left b a)

structure MeetEmbedding {α : Type u} {β : Type v}
    (P : MeetOrder α) (Q : MeetOrder β) where
  toFun : α → β
  le_iff : ∀ a b, Q.le (toFun a) (toFun b) ↔ P.le a b
  map_meet : ∀ a b, toFun (P.meet a b) = Q.meet (toFun a) (toFun b)

def Positive {α : Type u} (P : MeetOrder α) (F : α → Prop) (x : α) : Prop :=
  ∃ f, F f ∧ P.le f x

def Profile {α : Type u} (P : MeetOrder α) (c e K : α) (F : α → Prop) : Prop :=
  ∀ x, P.le e x →
    (Positive P F x → P.le K x) ∧
    (¬ Positive P F x → P.meet K x = c)

def PositiveOver {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (F : α → Prop) (x : β) : Prop :=
  ∃ f, F f ∧ Q.le (i.toFun f) x

def ProfileOver {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (c e K : α) (F : α → Prop) : Prop :=
  ∀ x, Q.le (i.toFun e) x →
    (PositiveOver i F x → Q.le (i.toFun K) x) ∧
    (¬ PositiveOver i F x → Q.meet (i.toFun K) x = i.toFun c)

end



namespace Attachment

universe u v w

structure Data {O : Type u} (P : MeetOrder O) (N : Type v) (I : Type w) where
  component : N → I
  base : I → O
  upper : I → O → Prop
  upper_up : ∀ i {a b}, upper i a → P.le a b → upper i b
  upper_meet : ∀ i {a b}, upper i a → upper i b → upper i (P.meet a b)
  base_le_upper : ∀ i a, upper i a → P.le (base i) a
  base_not_upper : ∀ i, ¬ upper i (base i)
  shadow : N → O
  shadow_le_base : ∀ x, P.le (shadow x) (base (component x))
  inside : N → N → Prop
  inside_refl : ∀ x, inside x x
  inside_trans : ∀ {x y z}, inside x y → inside y z → inside x z
  inside_antisymm : ∀ {x y}, inside x y → inside y x → x = y
  inside_component : ∀ {x y}, inside x y → component x = component y
  inside_shadow : ∀ {x y}, inside x y → P.le (shadow x) (shadow y)

variable {O : Type u} {N : Type v} {I : Type w} {P : MeetOrder O}

def FreshLe (d : Data P N I) (x y : N) : Prop :=
  d.inside x y ∨ d.upper (d.component x) (d.shadow y)

def Le (d : Data P N I) : O ⊕ N → O ⊕ N → Prop
  | .inl a, .inl b => P.le a b
  | .inl a, .inr y => P.le a (d.shadow y)
  | .inr x, .inl b => d.upper (d.component x) b
  | .inr x, .inr y => FreshLe d x y

theorem not_upper_shadow (d : Data P N I) (x : N) :
    ¬ d.upper (d.component x) (d.shadow x) := by
  intro h
  exact d.base_not_upper _ (d.upper_up _ h (d.shadow_le_base x))

theorem fresh_shadow_mono (d : Data P N I) {x y : N}
    (h : FreshLe d x y) : P.le (d.shadow x) (d.shadow y) := by
  cases h with
  | inl h => exact d.inside_shadow h
  | inr h => exact P.trans (d.shadow_le_base x) (d.base_le_upper _ _ h)

theorem fresh_trans (d : Data P N I) {x y z : N}
    (hxy : FreshLe d x y) (hyz : FreshLe d y z) : FreshLe d x z := by
  cases hxy with
  | inl hxy =>
    cases hyz with
    | inl hyz => exact Or.inl (d.inside_trans hxy hyz)
    | inr hyz =>
      exact Or.inr ((d.inside_component hxy).symm ▸ hyz)
  | inr hxy => exact Or.inr (d.upper_up _ hxy (fresh_shadow_mono d hyz))

theorem fresh_antisymm (d : Data P N I) {x y : N}
    (hxy : FreshLe d x y) (hyx : FreshLe d y x) : x = y := by
  cases hxy with
  | inl hxy =>
    cases hyx with
    | inl hyx => exact d.inside_antisymm hxy hyx
    | inr hyx =>
      exact False.elim (not_upper_shadow d x ((d.inside_component hxy).symm ▸ hyx))
  | inr hxy =>
    exact False.elim (not_upper_shadow d x (d.upper_up _ hxy (fresh_shadow_mono d hyx)))

theorem le_refl (d : Data P N I) (x : O ⊕ N) : Le d x x := by
  cases x with
  | inl a => exact P.refl a
  | inr x => exact Or.inl (d.inside_refl x)

theorem le_trans (d : Data P N I) {x y z : O ⊕ N}
    (hxy : Le d x y) (hyz : Le d y z) : Le d x z := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      cases z with
      | inl c => exact P.trans hxy hyz
      | inr z => exact P.trans hxy hyz
    | inr y =>
      cases z with
      | inl c => exact P.trans hxy (P.trans (d.shadow_le_base y) (d.base_le_upper _ _ hyz))
      | inr z => exact P.trans hxy (fresh_shadow_mono d hyz)
  | inr x =>
    cases y with
    | inl b =>
      cases z with
      | inl c => exact d.upper_up _ hxy hyz
      | inr z => exact Or.inr (d.upper_up _ hxy hyz)
    | inr y =>
      cases z with
      | inl c =>
        cases hxy with
        | inl hxy =>
          change d.upper (d.component x) c
          exact (d.inside_component hxy).symm ▸ hyz
        | inr hxy =>
          exact d.upper_up _ hxy (P.trans (d.shadow_le_base y) (d.base_le_upper _ _ hyz))
      | inr z => exact fresh_trans d hxy hyz

theorem le_antisymm (d : Data P N I) {x y : O ⊕ N}
    (hxy : Le d x y) (hyx : Le d y x) : x = y := by
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (P.antisymm hxy hyx)
    | inr y => exact False.elim (not_upper_shadow d y (d.upper_up _ hyx hxy))
  | inr x =>
    cases y with
    | inl b => exact False.elim (not_upper_shadow d x (d.upper_up _ hxy hyx))
    | inr y => exact congrArg Sum.inr (fresh_antisymm d hxy hyx)

theorem fresh_same_component (d : Data P N I) {x y : N}
    (same : d.component x = d.component y) :
    FreshLe d x y ↔ d.inside x y := by
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact False.elim (not_upper_shadow d y (same ▸ h))
  · exact Or.inl

theorem fresh_different_components (d : Data P N I) {x y : N}
    (different : d.component x ≠ d.component y) :
    FreshLe d x y ↔ d.upper (d.component x) (d.shadow y) := by
  constructor
  · intro h
    cases h with
    | inl h => exact False.elim (different (d.inside_component h))
    | inr h => exact h
  · exact Or.inr

def IsMeet (d : Data P N I) (a b m : O ⊕ N) : Prop :=
  Le d m a ∧ Le d m b ∧ ∀ t, Le d t a → Le d t b → Le d t m

theorem old_meet (d : Data P N I) (a b : O) :
    IsMeet d (.inl a) (.inl b) (.inl (P.meet a b)) := by
  refine ⟨P.meet_le_left a b, P.meet_le_right a b, ?_⟩
  intro t hta htb
  cases t with
  | inl c => exact P.le_meet hta htb
  | inr x => exact d.upper_meet _ hta htb

theorem shadow_meet (d : Data P N I) (x : N) (a : O)
    (not_above : ¬ d.upper (d.component x) a) :
    IsMeet d (.inr x) (.inl a) (.inl (P.meet (d.shadow x) a)) := by
  refine ⟨P.meet_le_left _ _, P.meet_le_right _ _, ?_⟩
  intro t htx hta
  cases t with
  | inl b => exact P.le_meet htx hta
  | inr y =>
    cases htx with
    | inl inside => exact False.elim (not_above (d.inside_component inside ▸ hta))
    | inr mediated => exact d.upper_meet _ mediated hta

theorem cross_meet (d : Data P N I) (x z : N)
    (different : d.component x ≠ d.component z)
    (not_xz : ¬ FreshLe d x z) (not_zx : ¬ FreshLe d z x) :
    IsMeet d (.inr x) (.inr z) (.inl (P.meet (d.shadow x) (d.shadow z))) := by
  refine ⟨P.meet_le_left _ _, P.meet_le_right _ _, ?_⟩
  intro t htx htz
  cases t with
  | inl b => exact P.le_meet htx htz
  | inr y =>
    cases htx with
    | inl hyx =>
      cases htz with
      | inl hyz =>
        exact False.elim (different ((d.inside_component hyx).symm.trans (d.inside_component hyz)))
      | inr hyz => exact False.elim (not_xz (Or.inr (d.inside_component hyx ▸ hyz)))
    | inr hyx =>
      cases htz with
      | inl hyz => exact False.elim (not_zx (Or.inr (d.inside_component hyz ▸ hyx)))
      | inr hyz => exact d.upper_meet _ hyx hyz

def ComponentMeets (d : Data P N I) : Prop :=
  ∀ x z, d.component x = d.component z →
    (∃ m, d.inside m x ∧ d.inside m z ∧
      (∀ y, d.inside y x → d.inside y z → d.inside y m) ∧
      d.shadow m = P.meet (d.shadow x) (d.shadow z)) ∨
    (∀ y, d.inside y x → d.inside y z → False)

theorem inside_mediated_impossible (d : Data P N I) {y x z : N}
    (inside : d.inside y x) (same : d.component x = d.component z)
    (mediated : d.upper (d.component y) (d.shadow z)) : False := by
  exact not_upper_shadow d z ((d.inside_component inside).trans same ▸ mediated)

theorem component_fresh_meet (d : Data P N I) (x z m : N)
    (same : d.component x = d.component z)
    (hmx : d.inside m x) (hmz : d.inside m z)
    (greatest : ∀ y, d.inside y x → d.inside y z → d.inside y m)
    (shadows : d.shadow m = P.meet (d.shadow x) (d.shadow z)) :
    IsMeet d (.inr x) (.inr z) (.inr m) := by
  refine ⟨Or.inl hmx, Or.inl hmz, ?_⟩
  intro t htx htz
  cases t with
  | inl a =>
    change P.le a (d.shadow m)
    rw [shadows]
    exact P.le_meet htx htz
  | inr y =>
    cases htx with
    | inl hyx =>
      cases htz with
      | inl hyz => exact Or.inl (greatest y hyx hyz)
      | inr hyz => exact False.elim (inside_mediated_impossible d hyx same hyz)
    | inr hyx =>
      cases htz with
      | inl hyz => exact False.elim (inside_mediated_impossible d hyz same.symm hyx)
      | inr hyz =>
        apply Or.inr
        rw [shadows]
        exact d.upper_meet _ hyx hyz

theorem component_old_meet (d : Data P N I) (x z : N)
    (same : d.component x = d.component z)
    (no_new_lower : ∀ y, d.inside y x → d.inside y z → False) :
    IsMeet d (.inr x) (.inr z) (.inl (P.meet (d.shadow x) (d.shadow z))) := by
  refine ⟨P.meet_le_left _ _, P.meet_le_right _ _, ?_⟩
  intro t htx htz
  cases t with
  | inl a => exact P.le_meet htx htz
  | inr y =>
    cases htx with
    | inl hyx =>
      cases htz with
      | inl hyz => exact False.elim (no_new_lower y hyx hyz)
      | inr hyz => exact False.elim (inside_mediated_impossible d hyx same hyz)
    | inr hyx =>
      cases htz with
      | inl hyz => exact False.elim (inside_mediated_impossible d hyz same.symm hyx)
      | inr hyz => exact d.upper_meet _ hyx hyz

theorem meet_of_le (d : Data P N I) {a b : O ⊕ N} (h : Le d a b) :
    IsMeet d a b a := ⟨le_refl d a, h, fun _ hta _ => hta⟩

theorem meet_symm (d : Data P N I) {a b m : O ⊕ N}
    (h : IsMeet d a b m) : IsMeet d b a m :=
  ⟨h.right.left, h.left, fun t htb hta => h.right.right t hta htb⟩

theorem all_meets (d : Data P N I) (local_meets : ComponentMeets d)
    (a b : O ⊕ N) : ∃ m, IsMeet d a b m := by
  classical
  cases a with
  | inl a =>
    cases b with
    | inl b => exact ⟨_, old_meet d a b⟩
    | inr y =>
      by_cases h : d.upper (d.component y) a
      · exact ⟨_, meet_symm d (meet_of_le d h)⟩
      · exact ⟨_, meet_symm d (shadow_meet d y a h)⟩
  | inr x =>
    cases b with
    | inl b =>
      by_cases h : d.upper (d.component x) b
      · exact ⟨_, meet_of_le d h⟩
      · exact ⟨_, shadow_meet d x b h⟩
    | inr z =>
      by_cases same : d.component x = d.component z
      · cases local_meets x z same with
        | inl fresh =>
          rcases fresh with ⟨m, hmx, hmz, greatest, shadows⟩
          exact ⟨_, component_fresh_meet d x z m same hmx hmz greatest shadows⟩
        | inr old => exact ⟨_, component_old_meet d x z same old⟩
      · by_cases h : FreshLe d x z
        · exact ⟨_, meet_of_le d h⟩
        · by_cases h' : FreshLe d z x
          · exact ⟨_, meet_symm d (meet_of_le d h')⟩
          · exact ⟨_, cross_meet d x z same h h'⟩

noncomputable def meetOrder (d : Data P N I) (local_meets : ComponentMeets d) :
    MeetOrder (O ⊕ N) where
  le := Le d
  meet a b := Classical.choose (all_meets d local_meets a b)
  refl := le_refl d
  trans := le_trans d
  antisymm := le_antisymm d
  meet_le_left a b := (Classical.choose_spec (all_meets d local_meets a b)).left
  meet_le_right a b := (Classical.choose_spec (all_meets d local_meets a b)).right.left
  le_meet hab hac := (Classical.choose_spec (all_meets d local_meets _ _)).right.right _ hab hac

theorem meet_eq (d : Data P N I) (local_meets : ComponentMeets d)
    {a b m : O ⊕ N} (h : IsMeet d a b m) :
    (meetOrder d local_meets).meet a b = m := by
  let Q := meetOrder d local_meets
  apply le_antisymm d
  · exact h.right.right _ (Q.meet_le_left a b) (Q.meet_le_right a b)
  · exact Q.le_meet h.left h.right.left

noncomputable def oldEmbedding (d : Data P N I) (local_meets : ComponentMeets d) :
    MeetEmbedding P (meetOrder d local_meets) where
  toFun := Sum.inl
  le_iff _ _ := Iff.rfl
  map_meet a b := (meet_eq d local_meets (old_meet d a b)).symm

end Attachment



namespace Attachment

universe u v w

def idealOrder {A : Type v} (Q : MeetOrder A) (a : A) :
    MeetOrder {x : A // Q.le x a} where
  le x y := Q.le x.val y.val
  meet x y := ⟨Q.meet x.val y.val, Q.trans (Q.meet_le_left _ _) x.property⟩
  refl x := Q.refl x.val
  trans hxy hyz := Q.trans hxy hyz
  antisymm hxy hyx := Subtype.ext (Q.antisymm hxy hyx)
  meet_le_left x y := Q.meet_le_left x.val y.val
  meet_le_right x y := Q.meet_le_right x.val y.val
  le_meet hxy hxz := Q.le_meet hxy hxz

def cut {A : Type v} (Q : MeetOrder A) (a x : A) : {y : A // Q.le y a} :=
  ⟨Q.meet x a, Q.meet_le_right x a⟩

theorem cut_mono {A : Type v} (Q : MeetOrder A) (a : A) {x y : A}
    (h : Q.le x y) : (idealOrder Q a).le (cut Q a x) (cut Q a y) :=
  Q.le_meet (Q.trans (Q.meet_le_left x a) h) (Q.meet_le_right x a)

theorem cut_meet {A : Type v} (Q : MeetOrder A) (a x y : A) :
    cut Q a (Q.meet x y) = (idealOrder Q a).meet (cut Q a x) (cut Q a y) := by
  apply Subtype.ext
  change Q.meet (Q.meet x y) a = Q.meet (Q.meet x a) (Q.meet y a)
  apply Q.antisymm
  · apply Q.le_meet
    · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_left x y)) (Q.meet_le_right _ _)
    · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_right x y)) (Q.meet_le_right _ _)
  · apply Q.le_meet
    · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_left x a))
        (Q.trans (Q.meet_le_right _ _) (Q.meet_le_left y a))
    · exact Q.trans (Q.meet_le_left _ _) (Q.meet_le_right x a)

theorem cut_of_le {A : Type v} (Q : MeetOrder A) (a x : A) (h : Q.le x a) :
    cut Q a x = ⟨x, h⟩ := by
  apply Subtype.ext
  exact Q.antisymm (Q.meet_le_left x a) (Q.le_meet (Q.refl x) h)

structure Templates {O : Type u} (P : MeetOrder O) (I : Type w) where
  Space : I → Type v
  order : ∀ i, MeetOrder (Space i)
  anchor : ∀ i, Space i
  embed : ∀ i, MeetEmbedding (idealOrder (order i) (anchor i)) P
  upper : I → O → Prop
  upper_nonempty : ∀ i, ∃ a, upper i a
  upper_up : ∀ i {a b}, upper i a → P.le a b → upper i b
  upper_meet : ∀ i {a b}, upper i a → upper i b → upper i (P.meet a b)
  separator : I → O
  base_le_separator : ∀ i,
    P.le ((embed i).toFun ⟨anchor i, (order i).refl _⟩) (separator i)
  separator_not_le_base : ∀ i,
    ¬ P.le (separator i) ((embed i).toFun ⟨anchor i, (order i).refl _⟩)
  separator_le_upper : ∀ i a, upper i a → P.le (separator i) a

namespace Templates

variable {O : Type u} {I : Type w} {P : MeetOrder O} (b : Templates.{u,v,w} P I)

def Fresh := (i : I) × {y : b.Space i // ¬ (b.order i).le y (b.anchor i)}

def base (i : I) : O := (b.embed i).toFun ⟨b.anchor i, (b.order i).refl _⟩

def shadow (x : b.Fresh) : O := (b.embed x.1).toFun (cut (b.order x.1) (b.anchor x.1) x.2.val)

def Inside (x y : b.Fresh) : Prop :=
  ∃ h : x.1 = y.1, (b.order x.1).le x.2.val (h.symm ▸ y.2.val)

theorem inside_refl (x : b.Fresh) : b.Inside x x := ⟨rfl, (b.order x.1).refl x.2.val⟩

theorem inside_trans {x y z : b.Fresh} (hxy : b.Inside x y) (hyz : b.Inside y z) :
    b.Inside x z := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  rcases hxy with ⟨hij, hxy⟩
  cases hij
  rcases hyz with ⟨hjk, hyz⟩
  cases hjk
  exact ⟨rfl, (b.order i).trans hxy hyz⟩

theorem inside_antisymm {x y : b.Fresh} (hxy : b.Inside x y) (hyx : b.Inside y x) :
    x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases hxy with ⟨hij, hxy⟩
  cases hij
  rcases hyx with ⟨hii, hyx⟩
  cases hii
  exact congrArg (Sigma.mk i) (Subtype.ext ((b.order i).antisymm hxy hyx))

theorem inside_shadow {x y : b.Fresh} (hxy : b.Inside x y) :
    P.le (b.shadow x) (b.shadow y) := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases hxy with ⟨hij, hxy⟩
  cases hij
  exact ((b.embed i).le_iff _ _).mpr (cut_mono (b.order i) (b.anchor i) hxy)

def data : Data P b.Fresh I where
  component := Sigma.fst
  base := b.base
  upper := b.upper
  upper_up := b.upper_up
  upper_meet := b.upper_meet
  base_le_upper i a h := P.trans (b.base_le_separator i) (b.separator_le_upper i a h)
  base_not_upper i h := b.separator_not_le_base i (b.separator_le_upper i (b.base i) h)
  shadow := b.shadow
  shadow_le_base x := ((b.embed x.1).le_iff _ _).mpr ((b.order x.1).meet_le_right _ _)
  inside := b.Inside
  inside_refl := b.inside_refl
  inside_trans := b.inside_trans
  inside_antisymm := b.inside_antisymm
  inside_component h := h.choose
  inside_shadow := b.inside_shadow

theorem mapped_cut_meet (i : I) (x y : b.Space i) :
    (b.embed i).toFun (cut (b.order i) (b.anchor i) ((b.order i).meet x y)) =
    P.meet ((b.embed i).toFun (cut (b.order i) (b.anchor i) x))
      ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) := by
  rw [cut_meet]
  exact (b.embed i).map_meet _ _

theorem component_meets : ComponentMeets b.data := by
  classical
  intro x z same
  rcases x with ⟨i, x⟩
  rcases z with ⟨j, z⟩
  change i = j at same
  cases same
  by_cases old : (b.order i).le ((b.order i).meet x.val z.val) (b.anchor i)
  · apply Or.inr
    intro y hyx hyz
    rcases y with ⟨k, y⟩
    rcases hyx with ⟨hki, hyx⟩
    cases hki
    rcases hyz with ⟨hkk, hyz⟩
    cases hkk
    exact y.property ((b.order i).trans ((b.order i).le_meet hyx hyz) old)
  · apply Or.inl
    let m : b.Fresh := ⟨i, ⟨(b.order i).meet x.val z.val, old⟩⟩
    refine ⟨m, ⟨rfl, (b.order i).meet_le_left _ _⟩, ⟨rfl, (b.order i).meet_le_right _ _⟩, ?_, ?_⟩
    · intro y hyx hyz
      rcases y with ⟨k, y⟩
      rcases hyx with ⟨hki, hyx⟩
      cases hki
      rcases hyz with ⟨hkk, hyz⟩
      cases hkk
      exact ⟨rfl, (b.order i).le_meet hyx hyz⟩
    · exact b.mapped_cut_meet i x.val z.val

noncomputable def extension : MeetOrder (O ⊕ b.Fresh) := meetOrder b.data b.component_meets

noncomputable def oldEmbedding : MeetEmbedding P b.extension :=
  Attachment.oldEmbedding b.data b.component_meets

noncomputable def represent (i : I) (y : b.Space i) : O ⊕ b.Fresh := by
  classical
  exact if h : (b.order i).le y (b.anchor i) then
    .inl ((b.embed i).toFun ⟨y, h⟩)
  else .inr ⟨i, ⟨y, h⟩⟩

theorem represent_old (i : I) (y : b.Space i) (h : (b.order i).le y (b.anchor i)) :
    b.represent i y = .inl ((b.embed i).toFun ⟨y, h⟩) := by
  simp only [represent, dite_eq_left h]

theorem represent_new (i : I) (y : b.Space i) (h : ¬ (b.order i).le y (b.anchor i)) :
    b.represent i y = .inr ⟨i, ⟨y, h⟩⟩ := by
  simp only [represent, dite_eq_right h]

theorem represent_le_iff (i : I) (x y : b.Space i) :
    Le b.data (b.represent i x) (b.represent i y) ↔ (b.order i).le x y := by
  classical
  by_cases hx : (b.order i).le x (b.anchor i)
  · rw [b.represent_old i x hx]
    by_cases hy : (b.order i).le y (b.anchor i)
    · rw [b.represent_old i y hy]
      exact (b.embed i).le_iff _ _
    · rw [b.represent_new i y hy]
      change P.le ((b.embed i).toFun ⟨x, hx⟩)
        ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) ↔ _
      rw [(b.embed i).le_iff]
      constructor
      · intro h
        exact (b.order i).trans h ((b.order i).meet_le_left y (b.anchor i))
      · intro h
        exact (b.order i).le_meet h hx
  · rw [b.represent_new i x hx]
    by_cases hy : (b.order i).le y (b.anchor i)
    · rw [b.represent_old i y hy]
      constructor
      · intro h
        have hbase : P.le ((b.embed i).toFun ⟨y, hy⟩) (b.base i) :=
          ((b.embed i).le_iff _ _).mpr hy
        exact False.elim (b.data.base_not_upper i (b.upper_up i h hbase))
      · intro h
        exact False.elim (hx ((b.order i).trans h hy))
    · rw [b.represent_new i y hy]
      change FreshLe b.data ⟨i, ⟨x, hx⟩⟩ ⟨i, ⟨y, hy⟩⟩ ↔ _
      rw [fresh_same_component b.data (x := ⟨i, ⟨x, hx⟩⟩) (y := ⟨i, ⟨y, hy⟩⟩) rfl]
      constructor
      · rintro ⟨h, hxy⟩
        cases h
        exact hxy
      · intro hxy
        exact ⟨rfl, hxy⟩

theorem old_below_represent (i : I) (y : b.Space i) (a : O) :
    Le b.data (.inl a) (b.represent i y) ↔
    P.le a ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) := by
  classical
  by_cases hy : (b.order i).le y (b.anchor i)
  · rw [b.represent_old i y hy, cut_of_le _ _ _ hy]
    exact Iff.rfl
  · rw [b.represent_new i y hy]
    exact Iff.rfl

theorem upper_shadow_below_represent (i : I) (y : b.Space i) (x : b.Fresh)
    (h : b.upper x.1 ((b.embed i).toFun (cut (b.order i) (b.anchor i) y))) :
    Le b.data (.inr x) (b.represent i y) := by
  classical
  by_cases hy : (b.order i).le y (b.anchor i)
  · rw [b.represent_old i y hy]
    rw [cut_of_le _ _ _ hy] at h
    exact h
  · rw [b.represent_new i y hy]
    exact Or.inr h

theorem foreign_below_represent (i : I) (y : b.Space i) (x : b.Fresh)
    (different : x.1 ≠ i)
    (h : Le b.data (.inr x) (b.represent i y)) :
    b.upper x.1 ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) := by
  classical
  by_cases hy : (b.order i).le y (b.anchor i)
  · rw [b.represent_old i y hy] at h
    rw [cut_of_le _ _ _ hy]
    exact h
  · rw [b.represent_new i y hy] at h
    exact (fresh_different_components b.data (x := x) (y := ⟨i, ⟨y, hy⟩⟩) different).mp h

theorem represented_meet (i : I) (x z : b.Space i) :
    IsMeet b.data (b.represent i x) (b.represent i z)
      (b.represent i ((b.order i).meet x z)) := by
  classical
  refine ⟨(b.represent_le_iff i _ _).mpr ((b.order i).meet_le_left x z),
    (b.represent_le_iff i _ _).mpr ((b.order i).meet_le_right x z), ?_⟩
  intro t htx htz
  cases t with
  | inl a =>
    apply (b.old_below_represent i _ a).mpr
    rw [b.mapped_cut_meet]
    exact P.le_meet ((b.old_below_represent i x a).mp htx)
      ((b.old_below_represent i z a).mp htz)
  | inr y =>
    rcases y with ⟨j, y⟩
    by_cases same : j = i
    · cases same
      have repr_y := b.represent_new i y.val y.property
      rw [← repr_y] at htx htz ⊢
      apply (b.represent_le_iff i _ _).mpr
      exact (b.order i).le_meet ((b.represent_le_iff i _ _).mp htx)
        ((b.represent_le_iff i _ _).mp htz)
    · apply b.upper_shadow_below_represent
      rw [b.mapped_cut_meet]
      exact b.upper_meet j (b.foreign_below_represent i x ⟨j, y⟩ same htx)
        (b.foreign_below_represent i z ⟨j, y⟩ same htz)

noncomputable def templateEmbedding (i : I) : MeetEmbedding (b.order i) b.extension where
  toFun := b.represent i
  le_iff := b.represent_le_iff i
  map_meet x z := (meet_eq b.data b.component_meets (b.represented_meet i x z)).symm

theorem greatest_preserved (T : O) (top : ∀ a, P.le a T) :
    ∀ x, b.extension.le x (.inl T) := by
  intro x
  cases x with
  | inl a => exact top a
  | inr x =>
    rcases b.upper_nonempty x.1 with ⟨a, ha⟩
    exact b.upper_up x.1 ha (top a)

theorem least_preserved (zero : O) (bottom : ∀ a, P.le zero a) :
    ∀ x, b.extension.le (.inl zero) x := by
  intro x
  cases x with
  | inl a => exact bottom a
  | inr x => exact bottom (b.shadow x)

theorem cross_meet_eq (x z : b.Fresh) (different : x.1 ≠ z.1)
    (not_xz : ¬ b.extension.le (.inr x) (.inr z))
    (not_zx : ¬ b.extension.le (.inr z) (.inr x)) :
    b.extension.meet (.inr x) (.inr z) = .inl (P.meet (b.shadow x) (b.shadow z)) :=
  meet_eq b.data b.component_meets (cross_meet b.data x z different not_xz not_zx)

theorem cross_le_iff (x z : b.Fresh) (different : x.1 ≠ z.1) :
    b.extension.le (.inr x) (.inr z) ↔ b.upper x.1 (b.shadow z) :=
  fresh_different_components b.data (x := x) (y := z) different

theorem shadow_meet_eq (x : b.Fresh) (a : O)
    (not_above : ¬ b.extension.le (.inr x) (.inl a)) :
    b.extension.meet (.inr x) (.inl a) = .inl (P.meet (b.shadow x) a) :=
  meet_eq b.data b.component_meets (shadow_meet b.data x a not_above)

end Templates
end Attachment




universe u v w

theorem meet_eq_left_of_le {A : Type u} (P : MeetOrder A) {x y : A}
    (h : P.le x y) : P.meet x y = x :=
  P.antisymm (P.meet_le_left x y) (P.le_meet (P.refl x) h)

namespace Attachment.Templates

variable {O : Type u} {I : Type w} {P : MeetOrder O} (b : Templates.{u,v,w} P I)

def originalFamily (i : I) : O ⊕ b.Fresh → Prop
  | .inl a => b.upper i a
  | .inr _ => False

def cap (i : I) (t : b.Space i) (outside : ¬ (b.order i).le t (b.anchor i)) : b.Fresh :=
  ⟨i, ⟨t, outside⟩⟩

end Attachment.Templates

namespace Compression

structure MeetFilter {A : Type u} (P : MeetOrder A) where
  mem : A → Prop
  nonempty : ∃ x, mem x
  upward : ∀ {x y}, mem x → P.le x y → mem y
  closed_meet : ∀ {x y}, mem x → mem y → mem (P.meet x y)

def pushFilter {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) (F : MeetFilter P) : MeetFilter Q where
  mem y := ∃ x, F.mem x ∧ Q.le (s.toFun x) y
  nonempty := by
    rcases F.nonempty with ⟨x, hx⟩
    exact ⟨s.toFun x, x, hx, Q.refl _⟩
  upward := by
    rintro a b ⟨x, hx, hxa⟩ hab
    exact ⟨x, hx, Q.trans hxa hab⟩
  closed_meet := by
    rintro a b ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩
    refine ⟨P.meet x y, F.closed_meet hx hy, ?_⟩
    rw [s.map_meet]
    exact Q.le_meet (Q.trans (Q.meet_le_left _ _) hxa)
      (Q.trans (Q.meet_le_right _ _) hyb)

theorem pushFilter_trace {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) (F : MeetFilter P) (x : A) :
    (pushFilter s F).mem (s.toFun x) ↔ F.mem x := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact F.upward hy ((s.le_iff y x).mp hyx)
  · intro hx
    exact ⟨x, hx, Q.refl _⟩

theorem pushFilter_lower_bound {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) (F : MeetFilter P) (e : A)
    (lower : ∀ f, F.mem f → P.le e f) :
    ∀ y, (pushFilter s F).mem y → Q.le (s.toFun e) y := by
  rintro y ⟨f, hf, hfy⟩
  exact Q.trans ((s.le_iff e f).mpr (lower f hf)) hfy

structure MeetIso {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B)
    extends MeetEmbedding P Q where
  inverse : B → A
  left_inverse : ∀ x, inverse (toFun x) = x
  right_inverse : ∀ y, toFun (inverse y) = y

theorem meet_insert_upper {A : Type u} (P : MeetOrder A) (x y a : A)
    (hya : P.le y a) : P.meet x y = P.meet (P.meet x a) y := by
  apply P.antisymm
  · exact P.le_meet (P.le_meet (P.meet_le_left x y) (P.trans (P.meet_le_right x y) hya))
      (P.meet_le_right x y)
  · exact P.le_meet (P.trans (P.meet_le_left _ _) (P.meet_le_left x a))
      (P.meet_le_right _ _)

theorem base_meet_patch {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B)
    (s : A → B) (g : MeetEmbedding P Q) (a : A) (c : B)
    (ga : g.toFun a = c)
    (agree : ∀ y, P.le y a → s y = g.toFun y)
    (cut_law : ∀ x, Q.meet (s x) c = s (P.meet x a))
    (x y : A) (hya : P.le y a) : Q.meet (s x) (s y) = s (P.meet x y) := by
  have syc : Q.le (s y) c := by
    rw [agree y hya, ← ga]
    exact (g.le_iff y a).mpr hya
  calc
    Q.meet (s x) (s y) = Q.meet (Q.meet (s x) c) (s y) := meet_insert_upper Q _ _ _ syc
    _ = Q.meet (s (P.meet x a)) (s y) := by rw [cut_law]
    _ = Q.meet (g.toFun (P.meet x a)) (g.toFun y) := by
      rw [agree _ (P.meet_le_right x a), agree y hya]
    _ = g.toFun (P.meet (P.meet x a) y) := (g.map_meet _ _).symm
    _ = g.toFun (P.meet x y) := congrArg g.toFun (meet_insert_upper P x y a hya).symm
    _ = s (P.meet x y) := (agree _ (P.trans (P.meet_le_right x y) hya)).symm

theorem embedding_injective {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) {x y : A} (h : s.toFun x = s.toFun y) : x = y := by
  apply P.antisymm
  · apply (s.le_iff x y).mp
    rw [h]
    exact Q.refl _
  · apply (s.le_iff y x).mp
    rw [h]
    exact Q.refl _

noncomputable def isoOntoIdeal {A : Type u} (P : MeetOrder A)
    (s : MeetEmbedding P P) (k : A)
    (below : ∀ x, P.le (s.toFun x) k)
    (onto : ∀ z, P.le z k → ∃ x, s.toFun x = z) :
    MeetIso P (Attachment.idealOrder P k) where
  toFun x := ⟨s.toFun x, below x⟩
  le_iff x y := s.le_iff x y
  map_meet x y := Subtype.ext (s.map_meet x y)
  inverse z := Classical.choose (onto z.val z.property)
  left_inverse x := embedding_injective s (Classical.choose_spec (onto (s.toFun x) (below x)))
  right_inverse z := Subtype.ext (Classical.choose_spec (onto z.val z.property))

end Compression

end PartitionPilot

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

def compose {A : Type u} {B : Type v} {C : Type w}
    {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}
    (f : MeetEmbedding P Q) (g : MeetEmbedding Q R) : MeetEmbedding P R where
  toFun x := g.toFun (f.toFun x)
  le_iff x y := (g.le_iff _ _).trans (f.le_iff x y)
  map_meet x y := by rw [f.map_meet, g.map_meet]

def componentFilter {O : Type u} {I : Type w} {P : MeetOrder O}
    (b : Templates.{u,v,w} P I) (h : I) : MeetFilter P where
  mem := b.upper h
  nonempty := b.upper_nonempty h
  upward := b.upper_up h
  closed_meet := b.upper_meet h

structure Inputs {O : Type u} {I : Type w} {P : MeetOrder O}
    (b : Templates.{u,v,w} P I) (Task : Type z) where
  source : Task → O
  previous : Task → MeetEmbedding P b.extension
  representative : Task → MeetIso b.extension b.extension
  agree : ∀ i p, P.le p (source i) →
    (previous i).toFun p = (representative i).toFun (.inl p)

namespace Inputs

variable {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} (d : Inputs b Task)

def Eligible (i : Task) := {h : I // ¬ b.upper h (d.source i)}
def Labels := (i : Task) × d.Eligible i

noncomputable def nextBatch : Templates b.extension d.Labels where
  Space label := b.Space label.2.val
  order label := b.order label.2.val
  anchor label := b.anchor label.2.val
  embed label := compose (b.embed label.2.val) (d.previous label.1)
  upper label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).mem
  upper_nonempty label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).nonempty
  upper_up label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).upward
  upper_meet label := (pushFilter (d.previous label.1) (componentFilter b label.2.val)).closed_meet
  separator label := (d.previous label.1).toFun (b.separator label.2.val)
  base_le_separator label := ((d.previous label.1).le_iff _ _).mpr (b.base_le_separator label.2.val)
  separator_not_le_base label h :=
    b.separator_not_le_base label.2.val (((d.previous label.1).le_iff _ _).mp h)
  separator_le_upper label y h :=
    pushFilter_lower_bound (d.previous label.1) (componentFilter b label.2.val)
      (b.separator label.2.val) (b.separator_le_upper label.2.val) y h

def freshImage (i : Task) (x : b.Fresh) (eligible : ¬ b.upper x.1 (d.source i)) :
    d.nextBatch.Fresh := ⟨⟨i, ⟨x.1, eligible⟩⟩, x.2⟩

noncomputable def lift (i : Task) : O ⊕ b.Fresh → (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh := by
  classical
  exact fun x => match x with
    | .inl p => .inl ((d.previous i).toFun p)
    | .inr y => if h : b.upper y.1 (d.source i) then
        .inl ((d.representative i).toFun (.inr y))
      else .inr (d.freshImage i y h)

theorem lift_old (i : Task) (p : O) :
    d.lift i (.inl p) = .inl ((d.previous i).toFun p) := rfl

theorem lift_new_inside (i : Task) (x : b.Fresh) (h : b.upper x.1 (d.source i)) :
    d.lift i (.inr x) = .inl ((d.representative i).toFun (.inr x)) := by
  simp only [lift, dite_eq_left h]

theorem lift_new_outside (i : Task) (x : b.Fresh) (h : ¬ b.upper x.1 (d.source i)) :
    d.lift i (.inr x) = .inr (d.freshImage i x h) := by
  simp only [lift, dite_eq_right h]

theorem fresh_old_iff (i : Task) (x : b.Fresh) (h : ¬ b.upper x.1 (d.source i)) (p : O) :
    d.nextBatch.extension.le (.inr (d.freshImage i x h)) (.inl ((d.previous i).toFun p)) ↔
    b.extension.le (.inr x) (.inl p) :=
  pushFilter_trace (d.previous i) (componentFilter b x.1) p

theorem old_fresh_iff (i : Task) (x : b.Fresh) (h : ¬ b.upper x.1 (d.source i)) (p : O) :
    d.nextBatch.extension.le (.inl ((d.previous i).toFun p)) (.inr (d.freshImage i x h)) ↔
    b.extension.le (.inl p) (.inr x) :=
  (d.previous i).le_iff p (b.shadow x)

theorem lift_agrees_on_base (i : Task) (x : O ⊕ b.Fresh)
    (h : b.extension.le x (.inl (d.source i))) :
    d.lift i x = .inl ((d.representative i).toFun x) := by
  cases x with
  | inl p => exact congrArg Sum.inl (d.agree i p h)
  | inr x => exact d.lift_new_inside i x h

theorem lift_template (i : Task) (h : I) (eligible : ¬ b.upper h (d.source i))
    (y : b.Space h) :
    d.lift i (b.represent h y) = d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ y := by
  classical
  by_cases old : (b.order h).le y (b.anchor h)
  · rw [b.represent_old h y old, d.lift_old,
      d.nextBatch.represent_old ⟨i, ⟨h, eligible⟩⟩ y old]
    rfl
  · rw [b.represent_new h y old, d.lift_new_outside i ⟨h, ⟨y, old⟩⟩ eligible,
      d.nextBatch.represent_new ⟨i, ⟨h, eligible⟩⟩ y old]
    rfl

theorem fresh_pair_iff (i : Task) (x y : b.Fresh)
    (hx : ¬ b.upper x.1 (d.source i)) (hy : ¬ b.upper y.1 (d.source i)) :
    d.nextBatch.extension.le (.inr (d.freshImage i x hx)) (.inr (d.freshImage i y hy)) ↔
    b.extension.le (.inr x) (.inr y) := by
  classical
  by_cases same : x.1 = y.1
  · rcases x with ⟨h, x, xout⟩
    rcases y with ⟨k, y, yout⟩
    change h = k at same
    cases same
    have tx := d.nextBatch.represent_new ⟨i, ⟨h, hx⟩⟩ x xout
    have ty := d.nextBatch.represent_new ⟨i, ⟨h, hy⟩⟩ y yout
    have sx := b.represent_new h x xout
    have sy := b.represent_new h y yout
    change d.nextBatch.extension.le (Sum.inr ⟨⟨i, ⟨h, hx⟩⟩, ⟨x, xout⟩⟩)
      (Sum.inr ⟨⟨i, ⟨h, hy⟩⟩, ⟨y, yout⟩⟩) ↔ _
    rw [← tx, ← ty, ← sx, ← sy]
    exact (d.nextBatch.represent_le_iff ⟨i, ⟨h, hx⟩⟩ x y).trans
      (b.represent_le_iff h x y).symm
  · have different : (d.freshImage i x hx).1 ≠ (d.freshImage i y hy).1 := by
      intro h
      exact same (congrArg (fun label : d.Labels => label.2.val) h)
    rw [d.nextBatch.cross_le_iff _ _ different, b.cross_le_iff x y same]
    exact pushFilter_trace (d.previous i) (componentFilter b x.1) (b.shadow y)

theorem meet_lift_old_old (i : Task) (p q : O) :
    d.nextBatch.extension.meet (d.lift i (.inl p)) (d.lift i (.inl q)) =
    d.lift i (b.extension.meet (.inl p) (.inl q)) := by
  calc
    d.nextBatch.extension.meet (d.lift i (.inl p)) (d.lift i (.inl q)) =
        .inl (b.extension.meet ((d.previous i).toFun p) ((d.previous i).toFun q)) :=
      (d.nextBatch.oldEmbedding.map_meet _ _).symm
    _ = .inl ((d.previous i).toFun (P.meet p q)) :=
      congrArg Sum.inl ((d.previous i).map_meet p q).symm
    _ = d.lift i (.inl (P.meet p q)) := rfl
    _ = d.lift i (b.extension.meet (.inl p) (.inl q)) :=
      congrArg (d.lift i) (b.oldEmbedding.map_meet p q)

theorem meet_lift_fresh_old (i : Task) (x : b.Fresh)
    (eligible : ¬ b.upper x.1 (d.source i)) (p : O) :
    d.nextBatch.extension.meet (d.lift i (.inr x)) (d.lift i (.inl p)) =
    d.lift i (b.extension.meet (.inr x) (.inl p)) := by
  classical
  by_cases hp : b.upper x.1 p
  · rw [meet_eq_left_of_le b.extension (x := .inr x) (y := .inl p) hp,
      d.lift_new_outside i x eligible, d.lift_old]
    exact meet_eq_left_of_le d.nextBatch.extension ((d.fresh_old_iff i x eligible p).mpr hp)
  · have target_not : ¬ d.nextBatch.extension.le (.inr (d.freshImage i x eligible))
        (.inl ((d.previous i).toFun p)) :=
      fun h => hp ((d.fresh_old_iff i x eligible p).mp h)
    rw [d.lift_new_outside i x eligible, d.lift_old]
    calc
      d.nextBatch.extension.meet (.inr (d.freshImage i x eligible))
          (.inl ((d.previous i).toFun p)) =
          .inl (b.extension.meet ((d.previous i).toFun (b.shadow x)) ((d.previous i).toFun p)) :=
        d.nextBatch.shadow_meet_eq _ _ target_not
      _ = .inl ((d.previous i).toFun (P.meet (b.shadow x) p)) :=
        congrArg Sum.inl ((d.previous i).map_meet _ _).symm
      _ = d.lift i (.inl (P.meet (b.shadow x) p)) := rfl
      _ = d.lift i (b.extension.meet (.inr x) (.inl p)) :=
        congrArg (d.lift i) (b.shadow_meet_eq x p hp).symm

theorem meet_lift_template (i : Task) (h : I) (eligible : ¬ b.upper h (d.source i))
    (x y : b.Space h) :
    d.nextBatch.extension.meet (d.lift i (b.represent h x)) (d.lift i (b.represent h y)) =
    d.lift i (b.extension.meet (b.represent h x) (b.represent h y)) := by
  rw [d.lift_template i h eligible x, d.lift_template i h eligible y]
  calc
    d.nextBatch.extension.meet (d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ x)
        (d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ y) =
        d.nextBatch.represent ⟨i, ⟨h, eligible⟩⟩ ((b.order h).meet x y) :=
      ((d.nextBatch.templateEmbedding ⟨i, ⟨h, eligible⟩⟩).map_meet x y).symm
    _ = d.lift i (b.represent h ((b.order h).meet x y)) :=
      (d.lift_template i h eligible _).symm
    _ = d.lift i (b.extension.meet (b.represent h x) (b.represent h y)) :=
      congrArg (d.lift i) ((b.templateEmbedding h).map_meet x y)

theorem meet_lift_fresh_pair (i : Task) (x y : b.Fresh)
    (hx : ¬ b.upper x.1 (d.source i)) (hy : ¬ b.upper y.1 (d.source i)) :
    d.nextBatch.extension.meet (d.lift i (.inr x)) (d.lift i (.inr y)) =
    d.lift i (b.extension.meet (.inr x) (.inr y)) := by
  classical
  by_cases same : x.1 = y.1
  · rcases x with ⟨h, x, xout⟩
    rcases y with ⟨k, y, yout⟩
    change h = k at same
    cases same
    rw [← b.represent_new h x xout, ← b.represent_new h y yout]
    exact d.meet_lift_template i h hx x y
  · by_cases hxy : b.extension.le (.inr x) (.inr y)
    · rw [meet_eq_left_of_le b.extension hxy, d.lift_new_outside i x hx,
        d.lift_new_outside i y hy]
      exact meet_eq_left_of_le d.nextBatch.extension ((d.fresh_pair_iff i x y hx hy).mpr hxy)
    · by_cases hyx : b.extension.le (.inr y) (.inr x)
      · rw [meet_comm b.extension (.inr x) (.inr y), meet_eq_left_of_le b.extension hyx,
          d.lift_new_outside i x hx, d.lift_new_outside i y hy,
          meet_comm d.nextBatch.extension]
        exact meet_eq_left_of_le d.nextBatch.extension ((d.fresh_pair_iff i y x hy hx).mpr hyx)
      · have different : (d.freshImage i x hx).1 ≠ (d.freshImage i y hy).1 := by
          intro h
          exact same (congrArg (fun label : d.Labels => label.2.val) h)
        have target_xy := fun h => hxy ((d.fresh_pair_iff i x y hx hy).mp h)
        have target_yx := fun h => hyx ((d.fresh_pair_iff i y x hy hx).mp h)
        rw [d.lift_new_outside i x hx, d.lift_new_outside i y hy]
        calc
          d.nextBatch.extension.meet (.inr (d.freshImage i x hx)) (.inr (d.freshImage i y hy)) =
              .inl (b.extension.meet ((d.previous i).toFun (b.shadow x))
                ((d.previous i).toFun (b.shadow y))) :=
            d.nextBatch.cross_meet_eq _ _ different target_xy target_yx
          _ = .inl ((d.previous i).toFun (P.meet (b.shadow x) (b.shadow y))) :=
            congrArg Sum.inl ((d.previous i).map_meet _ _).symm
          _ = d.lift i (.inl (P.meet (b.shadow x) (b.shadow y))) := rfl
          _ = d.lift i (b.extension.meet (.inr x) (.inr y)) :=
            congrArg (d.lift i) (b.cross_meet_eq x y same hxy hyx).symm

theorem image_base_iff (i : Task) (x : O ⊕ b.Fresh) :
    d.nextBatch.extension.le (d.lift i x) (.inl ((d.previous i).toFun (d.source i))) ↔
    b.extension.le x (.inl (d.source i)) := by
  classical
  cases x with
  | inl p => exact (d.previous i).le_iff p (d.source i)
  | inr x =>
    by_cases hx : b.upper x.1 (d.source i)
    · rw [d.lift_new_inside i x hx]
      constructor
      · intro _
        exact hx
      · intro _
        change b.extension.le ((d.representative i).toFun (.inr x))
          ((d.previous i).toFun (d.source i))
        rw [d.agree i (d.source i) (P.refl _)]
        exact ((d.representative i).le_iff _ _).mpr hx
    · rw [d.lift_new_outside i x hx]
      exact d.fresh_old_iff i x hx (d.source i)

theorem cut_identity (i : Task) (x : O ⊕ b.Fresh) :
    d.nextBatch.extension.meet (d.lift i x) (.inl ((d.previous i).toFun (d.source i))) =
    d.lift i (b.extension.meet x (.inl (d.source i))) := by
  classical
  cases x with
  | inl p => exact d.meet_lift_old_old i p (d.source i)
  | inr x =>
    by_cases hx : b.upper x.1 (d.source i)
    · rw [meet_eq_left_of_le b.extension (x := .inr x) (y := .inl (d.source i)) hx]
      exact meet_eq_left_of_le d.nextBatch.extension ((d.image_base_iff i (.inr x)).mpr hx)
    · exact d.meet_lift_fresh_old i x hx (d.source i)

noncomputable def baseEmbedding (i : Task) : MeetEmbedding b.extension d.nextBatch.extension :=
  compose (d.representative i).toMeetEmbedding d.nextBatch.oldEmbedding

theorem meet_lift_with_base (i : Task) (x y : O ⊕ b.Fresh)
    (hy : b.extension.le y (.inl (d.source i))) :
    d.nextBatch.extension.meet (d.lift i x) (d.lift i y) = d.lift i (b.extension.meet x y) := by
  apply base_meet_patch b.extension d.nextBatch.extension (d.lift i) (d.baseEmbedding i)
    (.inl (d.source i)) (.inl ((d.previous i).toFun (d.source i)))
  · exact congrArg Sum.inl (d.agree i (d.source i) (P.refl _)).symm
  · exact d.lift_agrees_on_base i
  · exact d.cut_identity i
  · exact hy

theorem lift_preserves_meets (i : Task) (x y : O ⊕ b.Fresh) :
    d.nextBatch.extension.meet (d.lift i x) (d.lift i y) = d.lift i (b.extension.meet x y) := by
  classical
  by_cases hy : b.extension.le y (.inl (d.source i))
  · exact d.meet_lift_with_base i x y hy
  · by_cases hx : b.extension.le x (.inl (d.source i))
    · calc
        d.nextBatch.extension.meet (d.lift i x) (d.lift i y) =
            d.nextBatch.extension.meet (d.lift i y) (d.lift i x) := meet_comm _ _ _
        _ = d.lift i (b.extension.meet y x) := d.meet_lift_with_base i y x hx
        _ = d.lift i (b.extension.meet x y) := congrArg (d.lift i) (meet_comm _ _ _)
    · cases x with
      | inl p =>
        cases y with
        | inl q => exact d.meet_lift_old_old i p q
        | inr y =>
          calc
            d.nextBatch.extension.meet (d.lift i (.inl p)) (d.lift i (.inr y)) =
                d.nextBatch.extension.meet (d.lift i (.inr y)) (d.lift i (.inl p)) := meet_comm _ _ _
            _ = d.lift i (b.extension.meet (.inr y) (.inl p)) := d.meet_lift_fresh_old i y hy p
            _ = d.lift i (b.extension.meet (.inl p) (.inr y)) := congrArg (d.lift i) (meet_comm _ _ _)
      | inr x =>
        cases y with
        | inl q => exact d.meet_lift_fresh_old i x hx q
        | inr y => exact d.meet_lift_fresh_pair i x y hx hy

theorem lift_monotone (i : Task) {x y : O ⊕ b.Fresh}
    (h : b.extension.le x y) : d.nextBatch.extension.le (d.lift i x) (d.lift i y) := by
  have hm := (d.lift_preserves_meets i x y).trans
    (congrArg (d.lift i) (meet_eq_left_of_le b.extension h))
  have lower := d.nextBatch.extension.meet_le_right (d.lift i x) (d.lift i y)
  rw [hm] at lower
  exact lower

theorem lift_reflects_order (i : Task) {x y : O ⊕ b.Fresh}
    (h : d.nextBatch.extension.le (d.lift i x) (d.lift i y)) : b.extension.le x y := by
  classical
  by_cases hx : b.extension.le x (.inl (d.source i))
  · have hxc := (d.image_base_iff i x).mpr hx
    have hcut : d.nextBatch.extension.le (d.lift i x)
        (d.lift i (b.extension.meet y (.inl (d.source i)))) := by
      rw [← d.cut_identity i y]
      exact d.nextBatch.extension.le_meet h hxc
    rw [d.lift_agrees_on_base i x hx,
      d.lift_agrees_on_base i _ (b.extension.meet_le_right y (.inl (d.source i)))] at hcut
    have source_cut := ((d.representative i).le_iff x (b.extension.meet y (.inl (d.source i)))).mp hcut
    exact b.extension.trans source_cut (b.extension.meet_le_left _ _)
  · by_cases hy : b.extension.le y (.inl (d.source i))
    · exact False.elim (hx ((d.image_base_iff i x).mp
        (d.nextBatch.extension.trans h ((d.image_base_iff i y).mpr hy))))
    · cases x with
      | inl p =>
        cases y with
        | inl q => exact ((d.previous i).le_iff p q).mp h
        | inr y =>
          rw [d.lift_old, d.lift_new_outside i y hy] at h
          exact (d.old_fresh_iff i y hy p).mp h
      | inr x =>
        cases y with
        | inl q =>
          rw [d.lift_new_outside i x hx, d.lift_old] at h
          exact (d.fresh_old_iff i x hx q).mp h
        | inr y =>
          rw [d.lift_new_outside i x hx, d.lift_new_outside i y hy] at h
          exact (d.fresh_pair_iff i x y hx hy).mp h

noncomputable def liftedEmbedding (i : Task) : MeetEmbedding b.extension d.nextBatch.extension where
  toFun := d.lift i
  le_iff _ _ := ⟨d.lift_reflects_order i, d.lift_monotone i⟩
  map_meet x y := (d.lift_preserves_meets i x y).symm

theorem lift_injective (i : Task) {x y : O ⊕ b.Fresh} (h : d.lift i x = d.lift i y) : x = y :=
  embedding_injective (d.liftedEmbedding i) h

theorem fresh_below_cap (i : Task) (x : b.Fresh) (eligible : ¬ b.upper x.1 (d.source i))
    (T : O) (top : ∀ p, P.le p T) :
    d.nextBatch.extension.le (.inr (d.freshImage i x eligible)) (.inl ((d.previous i).toFun T)) := by
  apply (d.fresh_old_iff i x eligible T).mpr
  rcases b.upper_nonempty x.1 with ⟨p, hp⟩
  exact b.upper_up x.1 hp (top p)

theorem fresh_outside_base (i : Task) (x : b.Fresh) (eligible : ¬ b.upper x.1 (d.source i)) :
    ¬ d.nextBatch.extension.le (.inr (d.freshImage i x eligible))
      (.inl ((d.previous i).toFun (d.source i))) :=
  fun h => eligible ((d.fresh_old_iff i x eligible (d.source i)).mp h)

end Inputs
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RecursiveAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

def isoOfOrder {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (f : A → B) (g : B → A) (left : ∀ x, g (f x) = x)
    (right : ∀ y, f (g y) = y)
    (order : ∀ x y, Q.le (f x) (f y) ↔ P.le x y) : MeetIso P Q where
  toFun := f
  le_iff := order
  map_meet x y := by
    apply Q.antisymm
    · exact Q.le_meet ((order _ _).mpr (P.meet_le_left x y))
        ((order _ _).mpr (P.meet_le_right x y))
    · have hx : P.le (g (Q.meet (f x) (f y))) x := by
        apply (order _ _).mp
        rw [right]
        exact Q.meet_le_left _ _
      have hy : P.le (g (Q.meet (f x) (f y))) y := by
        apply (order _ _).mp
        rw [right]
        exact Q.meet_le_right _ _
      have h := (order _ _).mpr (P.le_meet hx hy)
      rw [right] at h
      exact h
  inverse := g
  left_inverse := left
  right_inverse := right

def inverseIso {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (f : MeetIso P Q) : MeetIso Q P :=
  isoOfOrder f.inverse f.toFun f.right_inverse f.left_inverse (by
    intro x y
    have h := f.le_iff (f.inverse x) (f.inverse y)
    rw [f.right_inverse, f.right_inverse] at h
    exact h.symm)

structure TaskSymmetry {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} (d : Inputs b Task) where
  perm : Task → Task
  inverse : Task → Task
  left_inverse : ∀ i, inverse (perm i) = i
  right_inverse : ∀ i, perm (inverse i) = i
  current : MeetIso b.extension b.extension
  source : ∀ i, d.source (perm i) = d.source i
  intertwine : ∀ i p, current.toFun ((d.previous i).toFun p) =
    (d.previous (perm i)).toFun p

namespace TaskSymmetry

variable {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} {d : Inputs b Task}
    (s : TaskSymmetry d)

noncomputable def symm : TaskSymmetry d where
  perm := s.inverse
  inverse := s.perm
  left_inverse := s.right_inverse
  right_inverse := s.left_inverse
  current := inverseIso s.current
  source i := by
    have h := s.source (s.inverse i)
    rw [s.right_inverse] at h
    exact h.symm
  intertwine i p := by
    have h := congrArg s.current.inverse (s.intertwine (s.inverse i) p)
    rw [s.current.left_inverse, s.right_inverse] at h
    exact h.symm

def renameLabel (label : d.Labels) : d.Labels :=
  ⟨s.perm label.1, ⟨label.2.val, by
    rw [s.source]
    exact label.2.property⟩⟩

def renameFresh (x : d.nextBatch.Fresh) : d.nextBatch.Fresh :=
  ⟨s.renameLabel x.1, x.2⟩

def act : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh →
    (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh
  | .inl x => .inl (s.current.toFun x)
  | .inr x => .inr (s.renameFresh x)

theorem fresh_task_eq {i j : Task} {h : I}
    {hi : ¬ b.upper h (d.source i)} {hj : ¬ b.upper h (d.source j)}
    {y : b.Space h} {outside : ¬ (b.order h).le y (b.anchor h)} (eq : i = j) :
    (⟨⟨i, ⟨h, hi⟩⟩, ⟨y, outside⟩⟩ : d.nextBatch.Fresh) =
      ⟨⟨j, ⟨h, hj⟩⟩, ⟨y, outside⟩⟩ := by
  cases eq
  rfl

theorem rename_left (x : d.nextBatch.Fresh) :
    s.symm.renameFresh (s.renameFresh x) = x := by
  rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, ⟨y, outside⟩⟩
  change (⟨⟨s.inverse (s.perm i), ⟨h, _⟩⟩, ⟨y, outside⟩⟩ : d.nextBatch.Fresh) = _
  exact fresh_task_eq (s.left_inverse i)

theorem rename_right (x : d.nextBatch.Fresh) :
    s.renameFresh (s.symm.renameFresh x) = x := by
  rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, ⟨y, outside⟩⟩
  change (⟨⟨s.perm (s.inverse i), ⟨h, _⟩⟩, ⟨y, outside⟩⟩ : d.nextBatch.Fresh) = _
  exact fresh_task_eq (s.right_inverse i)

theorem act_left (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    s.symm.act (s.act x) = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (s.current.left_inverse x)
  | inr x => exact congrArg Sum.inr (s.rename_left x)

theorem act_right (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    s.act (s.symm.act x) = x := by
  cases x with
  | inl x => exact congrArg Sum.inl (s.current.right_inverse x)
  | inr x => exact congrArg Sum.inr (s.rename_right x)

theorem shadow_covariant (x : d.nextBatch.Fresh) :
    d.nextBatch.shadow (s.renameFresh x) =
      s.current.toFun (d.nextBatch.shadow x) :=
  (s.intertwine x.1.1
    ((b.embed x.1.2.val).toFun (cut (b.order x.1.2.val)
      (b.anchor x.1.2.val) x.2.val))).symm

theorem upper_covariant (label : d.Labels) (x : O ⊕ b.Fresh) :
    d.nextBatch.upper (s.renameLabel label) (s.current.toFun x) ↔
      d.nextBatch.upper label x := by
  change (∃ p, b.upper label.2.val p ∧
    b.extension.le ((d.previous (s.perm label.1)).toFun p) (s.current.toFun x)) ↔
    (∃ p, b.upper label.2.val p ∧ b.extension.le ((d.previous label.1).toFun p) x)
  constructor
  · rintro ⟨p, hp, hpx⟩
    rw [← s.intertwine] at hpx
    exact ⟨p, hp, (s.current.le_iff _ _).mp hpx⟩
  · rintro ⟨p, hp, hpx⟩
    refine ⟨p, hp, ?_⟩
    rw [← s.intertwine]
    exact (s.current.le_iff _ _).mpr hpx

theorem inside_forward {x y : d.nextBatch.Fresh} (h : d.nextBatch.Inside x y) :
    d.nextBatch.Inside (s.renameFresh x) (s.renameFresh y) := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases h with ⟨eq, h⟩
  cases eq
  exact ⟨rfl, h⟩

theorem inside_iff (x y : d.nextBatch.Fresh) :
    d.nextBatch.Inside (s.renameFresh x) (s.renameFresh y) ↔
      d.nextBatch.Inside x y := by
  constructor
  · intro h
    have h' := s.symm.inside_forward h
    rw [s.rename_left, s.rename_left] at h'
    exact h'
  · exact s.inside_forward

theorem act_order (x y : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh) :
    d.nextBatch.extension.le (s.act x) (s.act y) ↔ d.nextBatch.extension.le x y := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact s.current.le_iff x y
    | inr y =>
      change b.extension.le (s.current.toFun x) (d.nextBatch.shadow (s.renameFresh y)) ↔ _
      rw [s.shadow_covariant]
      exact s.current.le_iff _ _
  | inr x =>
    cases y with
    | inl y => exact s.upper_covariant x.1 y
    | inr y =>
      change (d.nextBatch.Inside (s.renameFresh x) (s.renameFresh y) ∨
        d.nextBatch.upper (s.renameLabel x.1) (d.nextBatch.shadow (s.renameFresh y))) ↔
        (d.nextBatch.Inside x y ∨ d.nextBatch.upper x.1 (d.nextBatch.shadow y))
      rw [s.inside_iff, s.shadow_covariant, s.upper_covariant]

noncomputable def nextIso : MeetIso d.nextBatch.extension d.nextBatch.extension :=
  isoOfOrder s.act s.symm.act s.act_left s.act_right s.act_order

theorem nextIso_old (x : O ⊕ b.Fresh) :
    s.nextIso.toFun (.inl x) = .inl (s.current.toFun x) := rfl

theorem nextIso_fresh (x : d.nextBatch.Fresh) :
    s.nextIso.toFun (.inr x) = .inr (s.renameFresh x) := rfl

theorem lift_equivariant
    (compatible : ∀ i x, b.extension.le x (.inl (d.source i)) →
      s.current.toFun ((d.representative i).toFun x) =
        (d.representative (s.perm i)).toFun x)
    (i : Task) (x : O ⊕ b.Fresh) :
    s.nextIso.toFun (d.lift i x) = d.lift (s.perm i) x := by
  cases x with
  | inl p => exact congrArg Sum.inl (s.intertwine i p)
  | inr x =>
    classical
    by_cases h : b.upper x.1 (d.source i)
    · have h' : b.upper x.1 (d.source (s.perm i)) := by rw [s.source]; exact h
      rw [d.lift_new_inside i x h, d.lift_new_inside (s.perm i) x h', s.nextIso_old]
      exact congrArg Sum.inl (compatible i (.inr x) h)
    · have h' : ¬ b.upper x.1 (d.source (s.perm i)) := by rw [s.source]; exact h
      rw [d.lift_new_outside i x h, d.lift_new_outside (s.perm i) x h', s.nextIso_fresh]
      rfl

theorem fresh_positive (T : O) (top : ∀ p, P.le p T) (v : O)
    (positive : Task → Prop)
    (negative : ∀ i, ¬ positive i →
      b.extension.le (b.extension.meet ((d.previous i).toFun T) (.inl v))
        ((d.previous i).toFun (d.source i)))
    (x : d.nextBatch.Fresh)
    (below : d.nextBatch.extension.le (.inr x) (.inl (.inl v))) :
    positive x.1.1 := by
  classical
  apply Classical.byContradiction
  intro hn
  rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, y⟩
  have cap := d.fresh_below_cap i ⟨h, y⟩ eligible T top
  have lower := d.nextBatch.extension.le_meet cap below
  have hm : d.nextBatch.extension.meet (.inl ((d.previous i).toFun T)) (.inl (.inl v)) =
      .inl (b.extension.meet ((d.previous i).toFun T) (.inl v)) :=
    (d.nextBatch.oldEmbedding.map_meet _ _).symm
  rw [hm] at lower
  have neg := (d.nextBatch.oldEmbedding.le_iff _ _).mpr (negative i hn)
  exact d.fresh_outside_base i ⟨h, y⟩ eligible (d.nextBatch.extension.trans lower neg)

theorem agreement_persists (t : TaskSymmetry d)
    (T : O) (top : ∀ p, P.le p T) (v : O) (positive : Task → Prop)
    (negative : ∀ i, ¬ positive i →
      b.extension.le (b.extension.meet ((d.previous i).toFun T) (.inl v))
        ((d.previous i).toFun (d.source i)))
    (current_agree : ∀ x, b.extension.le x (.inl v) →
      s.current.toFun x = t.current.toFun x)
    (task_agree : ∀ i, positive i → s.perm i = t.perm i)
    (x : (O ⊕ b.Fresh) ⊕ d.nextBatch.Fresh)
    (below : d.nextBatch.extension.le x (.inl (.inl v))) :
    s.nextIso.toFun x = t.nextIso.toFun x := by
  cases x with
  | inl x => exact congrArg Sum.inl (current_agree x below)
  | inr x =>
    have pos := fresh_positive T top v positive negative x below
    have eq := task_agree x.1.1 pos
    rcases x with ⟨⟨i, ⟨h, eligible⟩⟩, ⟨y, outside⟩⟩
    apply congrArg Sum.inr
    exact fresh_task_eq eq

end TaskSymmetry

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TaskSystem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z r q

def identityIso {A : Type u} (P : MeetOrder A) : MeetIso P P :=
  isoOfOrder (fun x => x) (fun x => x) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => Iff.rfl)

end PartitionPilot.Compression.RecursiveMaps



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_NodeCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps



section

universe u

def imageFamily {A B : Type u} {P : MeetOrder A} {Q : MeetOrder B}
    (e : MeetEmbedding P Q) (F : A → Prop) (x : B) : Prop :=
  ∃ a, F a ∧ e.toFun a = x

end



end PartitionPilot.Compression.RecursiveMaps

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CountableCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u

def natPair (a b : Nat) : Nat := (a + b) * (a + b) + a

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableSetFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing


namespace SetFormula

universe u v

theorem realize_ex (U : Set ZFSet.{u}) {n : Nat} (φ : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) :
    Realize U (ex φ) env ↔ ∃ x ∈ U, Realize U φ (extend x env) := by
  classical
  simp only [ex, Realize, not_forall, not_not, exists_prop]

theorem realize_disj (U : Set ZFSet.{u}) {n : Nat} (φ ψ : SetFormula n)
    (env : Fin n → ZFSet.{u}) :
    Realize U (disj φ ψ) env ↔ Realize U φ env ∨ Realize U ψ env := by
  classical
  simp only [disj, Realize, not_and_or, not_not]

theorem realize_imp (U : Set ZFSet.{u}) {n : Nat} (φ ψ : SetFormula n)
    (env : Fin n → ZFSet.{u}) :
    Realize U (imp φ ψ) env ↔ (Realize U φ env → Realize U ψ env) := by
  classical
  simp only [imp, Realize, not_and, not_not]

end SetFormula



namespace SetFormula

universe u

def liftIndex {n m : Nat} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

end SetFormula



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NatUnionCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.SetRealization.Presentation

universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B) (f : A → B)

noncomputable def graph : ZFSet.{u} :=
  (s.product t).subset (fun a => f a.1 = a.2)

theorem pair_mem_graph (a : A) (b : B) :
    ZFSet.pair (s.encode a) (t.encode b) ∈ s.graph t f ↔ f a = b :=
  (s.product t).encode_mem_subset (fun a => f a.1 = a.2) (a, b)

theorem mem_graph (x : ZFSet.{u}) :
    x ∈ s.graph t f ↔ ∃ a, ZFSet.pair (s.encode a) (t.encode (f a)) = x := by
  rw [graph, mem_subset]
  constructor
  · rintro ⟨⟨a, b⟩, h, eq⟩
    change f a = b at h
    subst b
    exact ⟨a, eq⟩
  · rintro ⟨a, eq⟩
    exact ⟨(a, f a), rfl, eq⟩

theorem graph_isFunc : ZFSet.IsFunc s.carrier t.carrier (s.graph t f) := by
  refine ⟨(s.product t).subset_carrier _, ?_⟩
  intro x hx
  rcases (s.mem_carrier x).1 hx with ⟨a, rfl⟩
  refine ⟨t.encode (f a), (s.pair_mem_graph t f a (f a)).2 rfl, ?_⟩
  intro y hy
  rcases (s.mem_graph t f _).1 hy with ⟨b, eq⟩
  have parts := ZFSet.pair_inj.1 eq
  have ba := s.injective parts.1
  simpa only [ba] using parts.2.symm

end PartitionPilot.SetRealization.Presentation



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

def FunctionGraphOn (A f : ZFSet.{u}) : Prop :=
  ∃ B, ZFSet.IsFunc A B f

theorem pair_second_mem_doubleUnion {x y f : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ f) : y ∈ ⋃₀ ⋃₀ f := by
  exact ZFSet.mem_sUnion.2 ⟨{x, y}, ZFSet.mem_sUnion.2
    ⟨ZFSet.pair x y, entry, ZFSet.mem_pair.2 (Or.inr rfl)⟩,
    ZFSet.mem_pair.2 (Or.inr rfl)⟩

namespace FunctionGraphOn

theorem to_isFunc {A f : ZFSet.{u}} (h : FunctionGraphOn A f) :
    ZFSet.IsFunc A (⋃₀ ⋃₀ f) f := by
  obtain ⟨B, shape, total⟩ := h
  refine ⟨?_, total⟩
  intro z hz
  obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
  exact ZFSet.pair_mem_prod.2 ⟨hx, pair_second_mem_doubleUnion hz⟩

theorem shape {A f : ZFSet.{u}} (h : FunctionGraphOn A f) :
    ∀ z ∈ f, ∃ x ∈ A, ∃ y, z = ZFSet.pair x y := by
  intro z hz
  obtain ⟨x, hx, y, _, eq⟩ := ZFSet.mem_prod.1 (h.to_isFunc.1 hz)
  exact ⟨x, hx, y, eq⟩

theorem total {A f x : ZFSet.{u}} (h : FunctionGraphOn A f) (hx : x ∈ A) :
    ∃ y, ZFSet.pair x y ∈ f := by
  obtain ⟨y, entry, _⟩ := h.to_isFunc.2 x hx
  exact ⟨y, entry⟩

theorem pair_source {A f x y : ZFSet.{u}} (h : FunctionGraphOn A f)
    (entry : ZFSet.pair x y ∈ f) : x ∈ A :=
  (ZFSet.pair_mem_prod.1 (h.to_isFunc.1 entry)).1

theorem unique {A f x y z : ZFSet.{u}} (h : FunctionGraphOn A f)
    (hy : ZFSet.pair x y ∈ f) (hz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨w, _, unique⟩ := h.to_isFunc.2 x (h.pair_source hy)
  exact (unique y hy).trans (unique z hz).symm

end FunctionGraphOn

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_HeightAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

structure HeightOrder (H : Type v) where
  lt : H → H → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z

namespace HeightOrder

variable {H : Type v} (R : HeightOrder H)

def Weak (x y : H) : Prop := x = y ∨ R.lt x y

theorem weak_lt {x y z : H} (h : R.Weak x y) (h' : R.lt y z) : R.lt x z := by
  rcases h with eq | h
  · cases eq
    exact h'
  · exact R.trans h h'

theorem lt_weak {x y z : H} (h : R.lt x y) (h' : R.Weak y z) : R.lt x z := by
  rcases h' with eq | h'
  · cases eq
    exact h
  · exact R.trans h h'

end HeightOrder

structure StrictHeight {A : Type u} {H : Type v} (P : MeetOrder A) (R : HeightOrder H) where
  value : A → H
  strict : ∀ x y, P.le x y → x ≠ y → R.lt (value x) (value y)

namespace StrictHeight

variable {A : Type u} {H : Type v} {P : MeetOrder A} {R : HeightOrder H}

theorem mono (h : StrictHeight P R) {x y : A} (lower : P.le x y) : R.Weak (h.value x) (h.value y) := by
  classical
  by_cases eq : x = y
  · exact Or.inl (congrArg h.value eq)
  · exact Or.inr (h.strict x y lower eq)

end StrictHeight

namespace AttachmentHeight

variable {O : Type u} {I : Type w} {H : Type z} {P : MeetOrder O} {R : HeightOrder H}
    (b : Templates.{u,v,w} P I) (old : StrictHeight P R)
    (component : ∀ i, StrictHeight (b.order i) R)

def value : O ⊕ b.Fresh → H
  | .inl x => old.value x
  | .inr x => (component x.1).value x.2.val

theorem strict
    (lower : ∀ x : b.Fresh, R.lt (old.value (b.base x.1)) ((component x.1).value x.2.val))
    (upper : ∀ x : b.Fresh, R.lt ((component x.1).value x.2.val) (old.value (b.separator x.1)))
    (x y : O ⊕ b.Fresh) (le : b.extension.le x y) (different : x ≠ y) :
    R.lt (value b old component x) (value b old component y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => exact old.strict x y le (fun eq => different (congrArg Sum.inl eq))
    | inr y =>
      have below : P.le x (b.base y.1) := P.trans le (b.data.shadow_le_base y)
      exact R.weak_lt (old.mono below) (lower y)
  | inr x =>
    cases y with
    | inl y => exact R.lt_weak (upper x) (old.mono (b.separator_le_upper x.1 y le))
    | inr y =>
      rcases le with inside | cross
      · rcases x with ⟨i, x, hx⟩
        rcases y with ⟨j, y, hy⟩
        rcases inside with ⟨same, inside⟩
        cases same
        apply (component i).strict x y inside
        intro eq
        cases eq
        exact different rfl
      · have middle : P.le (b.separator x.1) (b.base y.1) :=
          P.trans (b.separator_le_upper x.1 (b.shadow y) cross) (b.data.shadow_le_base y)
        exact R.trans (upper x) (R.weak_lt (old.mono middle) (lower y))

def extend
    (lower : ∀ x : b.Fresh, R.lt (old.value (b.base x.1)) ((component x.1).value x.2.val))
    (upper : ∀ x : b.Fresh, R.lt ((component x.1).value x.2.val) (old.value (b.separator x.1))) :
    StrictHeight b.extension R where
  value := value b old component
  strict := strict b old component lower upper

end AttachmentHeight
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_DenseInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u v w

structure LinearHeightOrder (A : Type u) extends HeightOrder A where
  compare : ∀ x y, lt x y ∨ x = y ∨ lt y x

structure DenseHeightOrder (A : Type u) extends LinearHeightOrder A where
  between : ∀ x y, lt x y → ∃ z, lt x z ∧ lt z y

namespace LinearHeightOrder

variable {A : Type u} (R : LinearHeightOrder A)

def reverse : LinearHeightOrder A where
  lt x y := R.lt y x
  irrefl := R.irrefl
  trans h h' := R.trans h' h
  compare x y := by
    rcases R.compare y x with h | eq | h
    · exact Or.inl h
    · exact Or.inr (Or.inl eq.symm)
    · exact Or.inr (Or.inr h)

end LinearHeightOrder

namespace CountableInterpolation

variable {A : Type u} {D : Type v} (S : LinearHeightOrder A)
    (R : DenseHeightOrder D) (enumerate : Nat → A) (lo hi : D)

structure Partial (n : Nat) where
  value : Nat → D
  lower : ∀ i, i < n → R.lt lo (value i)
  upper : ∀ i, i < n → R.lt (value i) hi
  strict : ∀ i j, i < n → j < n → S.lt (enumerate i) (enumerate j) → R.lt (value i) (value j)
  equal : ∀ i j, i < n → j < n → enumerate i = enumerate j → value i = value j

end CountableInterpolation

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RationalOrderBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Compression.RecursiveMaps.RationalHeights

structure Fraction where
  num : Int
  den : Nat
  positive : 0 < den

namespace Fraction

def Lt (a b : Fraction) : Prop := a.num * (b.den : Int) < b.num * (a.den : Int)
def Equiv (a b : Fraction) : Prop := a.num * (b.den : Int) = b.num * (a.den : Int)

theorem den_pos (a : Fraction) : 0 < (a.den : Int) := Int.natCast_pos.mpr a.positive

theorem cancel_lt {a b c : Int} (pos : 0 < c) (h : a * c < b * c) : a < b := by
  apply Classical.byContradiction
  intro hn
  have ba : b ≤ a := by omega
  have hc : 0 ≤ c := by omega
  have hb := Int.mul_le_mul_of_nonneg_right ba hc
  omega

theorem equiv_trans {a b c : Fraction} (ab : Equiv a b) (bc : Equiv b c) : Equiv a c := by
  apply Int.eq_of_mul_eq_mul_right (a := (b.den : Int)) (by have := b.den_pos; omega)
  change (a.num * (c.den : Int)) * b.den = (c.num * (a.den : Int)) * b.den
  calc
    _ = (a.num * (b.den : Int)) * c.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (b.num * (a.den : Int)) * c.den := congrArg (fun x => x * (c.den : Int)) ab
    _ = (b.num * (c.den : Int)) * a.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    _ = (c.num * (b.den : Int)) * a.den := congrArg (fun x => x * (a.den : Int)) bc
    _ = _ := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem lt_left {a b c : Fraction} (eq : Equiv a b) (h : Lt a c) : Lt b c := by
  have scaled := Int.mul_lt_mul_of_pos_right h b.den_pos
  have lhs : (a.num * (c.den : Int)) * b.den = (b.num * (c.den : Int)) * a.den := by
    calc
      _ = (a.num * (b.den : Int)) * c.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (b.num * (a.den : Int)) * c.den := congrArg (fun x => x * (c.den : Int)) eq
      _ = _ := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have rhs : (c.num * (a.den : Int)) * b.den = (c.num * (b.den : Int)) * a.den := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [lhs, rhs] at scaled
  exact cancel_lt a.den_pos scaled

theorem lt_right {a b c : Fraction} (eq : Equiv b c) (h : Lt a b) : Lt a c := by
  have scaled := Int.mul_lt_mul_of_pos_right h c.den_pos
  have lhs : (a.num * (b.den : Int)) * c.den = (a.num * (c.den : Int)) * b.den := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  have rhs : (b.num * (a.den : Int)) * c.den = (c.num * (a.den : Int)) * b.den := by
    calc
      _ = (b.num * (c.den : Int)) * a.den := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      _ = (c.num * (b.den : Int)) * a.den := congrArg (fun x => x * (a.den : Int)) eq
      _ = _ := by simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [lhs, rhs] at scaled
  exact cancel_lt b.den_pos scaled

def setoid : Setoid Fraction where
  r := Equiv
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h h' => equiv_trans h h'⟩

def mediant (a b : Fraction) : Fraction :=
  ⟨a.num + b.num, a.den + b.den, by have := a.positive; omega⟩

def above (a : Fraction) : Fraction := ⟨a.num + a.den, a.den, a.positive⟩

def intCode : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

theorem intCode_injective (a b : Int) (h : intCode a = intCode b) : a = b := by
  cases a <;> cases b <;> simp only [intCode] at h <;> congr 1 <;> omega

end Fraction

def Rational := Quotient Fraction.setoid

namespace Rational

def mk (a : Fraction) : Rational := Quotient.mk Fraction.setoid a

def lt : Rational → Rational → Prop :=
  Quotient.lift₂ Fraction.Lt (fun _ _ _ _ ha hb =>
    propext ⟨fun h => Fraction.lt_right hb (Fraction.lt_left ha h),
      fun h => Fraction.lt_right hb.symm (Fraction.lt_left ha.symm h)⟩)

noncomputable def representative (a : Rational) : Fraction :=
  Classical.choose (Quotient.exists_rep a)

theorem representative_eq (a : Rational) : mk (representative a) = a :=
  Classical.choose_spec (Quotient.exists_rep a)

end Rational

namespace Fraction

def below (a : Fraction) : Fraction := ⟨a.num - a.den, a.den, a.positive⟩

end Fraction

namespace Rational

theorem mk_eq_iff (a b : Fraction) : mk a = mk b ↔ Fraction.Equiv a b := by
  exact ⟨fun h => Quotient.exact h, fun h => @Quotient.sound Fraction Fraction.setoid a b h⟩

theorem representative_equiv (a : Fraction) :
    Fraction.Equiv (representative (mk a)) a :=
  (mk_eq_iff _ _).1 (representative_eq (mk a))

end Rational

end PartitionPilot.Compression.RecursiveMaps.RationalHeights

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_InaccessibleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

universe u v w

namespace LinearHeightOrder

variable {Column : Type v} {Coord : Type w}

def lex (C : LinearHeightOrder Column) (D : LinearHeightOrder Coord) :
    LinearHeightOrder (Column × Coord) where
  lt x y := C.lt x.1 y.1 ∨ x.1 = y.1 ∧ D.lt x.2 y.2
  irrefl x h := by
    rcases h with h | ⟨_, h⟩
    · exact C.irrefl x.1 h
    · exact D.irrefl x.2 h
  trans h h' := by
    rcases h with h | ⟨eq, h⟩
    · rcases h' with h' | ⟨eq, _⟩
      · exact Or.inl (C.trans h h')
      · exact Or.inl (eq ▸ h)
    · rcases h' with h' | ⟨eq', h'⟩
      · exact Or.inl (eq ▸ h')
      · exact Or.inr ⟨eq.trans eq', D.trans h h'⟩
  compare x y := by
    rcases C.compare x.1 y.1 with h | eq | h
    · exact Or.inl (Or.inl h)
    · rcases D.compare x.2 y.2 with h | eq' | h
      · exact Or.inl (Or.inr ⟨eq, h⟩)
      · exact Or.inr (Or.inl (Prod.ext eq eq'))
      · exact Or.inr (Or.inr (Or.inr ⟨eq.symm, h⟩))
    · exact Or.inr (Or.inr (Or.inl h))

end LinearHeightOrder

end PartitionPilot.Compression.RecursiveMaps



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_BinaryTiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation

open Attachment

universe u v

structure Input {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B) where
  leftAnchor : A
  rightAnchor : B
  overlap : MeetIso (idealOrder Q rightAnchor) (idealOrder P leftAnchor)

namespace Input

variable {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B} (g : Input P Q)

def Fresh := {b : B // ¬ Q.le b g.rightAnchor}

def Node := A ⊕ g.Fresh

def shadow (b : B) : A := (g.overlap.toFun (cut Q g.rightAnchor b)).val

theorem shadow_le_anchor (b : B) : P.le (g.shadow b) g.leftAnchor :=
  (g.overlap.toFun (cut Q g.rightAnchor b)).property

theorem shadow_mono {b c : B} (h : Q.le b c) : P.le (g.shadow b) (g.shadow c) :=
  (g.overlap.le_iff _ _).mpr (cut_mono Q g.rightAnchor h)

theorem shadow_meet (b c : B) : g.shadow (Q.meet b c) = P.meet (g.shadow b) (g.shadow c) := by
  unfold shadow
  rw [cut_meet, g.overlap.map_meet]
  rfl

def data : Data P g.Fresh Unit where
  component _ := ()
  base _ := g.leftAnchor
  upper _ _ := False
  upper_up := by intro _ _ _ h _; exact h
  upper_meet := by intro _ _ _ h _; exact h
  base_le_upper _ _ h := False.elim h
  base_not_upper _ h := h
  shadow x := g.shadow x.val
  shadow_le_base x := g.shadow_le_anchor x.val
  inside x y := Q.le x.val y.val
  inside_refl x := Q.refl x.val
  inside_trans := Q.trans
  inside_antisymm hxy hyx := Subtype.ext (Q.antisymm hxy hyx)
  inside_component _ := rfl
  inside_shadow := g.shadow_mono

theorem component_meets : ComponentMeets g.data := by
  classical
  intro x y _
  by_cases old : Q.le (Q.meet x.val y.val) g.rightAnchor
  · exact Or.inr (fun z hx hy => z.property (Q.trans (Q.le_meet hx hy) old))
  · exact Or.inl ⟨⟨Q.meet x.val y.val, old⟩, Q.meet_le_left _ _, Q.meet_le_right _ _,
      fun _ hx hy => Q.le_meet hx hy, g.shadow_meet x.val y.val⟩

noncomputable def order : MeetOrder g.Node := meetOrder g.data g.component_meets

noncomputable def left : MeetEmbedding P g.order := oldEmbedding g.data g.component_meets

noncomputable def represent (b : B) : g.Node := by
  classical
  exact if h : Q.le b g.rightAnchor then .inl (g.overlap.toFun ⟨b, h⟩).val
    else .inr ⟨b, h⟩

theorem represent_old (b : B) (h : Q.le b g.rightAnchor) :
    g.represent b = .inl (g.overlap.toFun ⟨b, h⟩).val := by
  unfold represent
  exact dite_eq_left h

theorem represent_new (b : B) (h : ¬ Q.le b g.rightAnchor) :
    g.represent b = .inr ⟨b, h⟩ := by
  unfold represent
  exact dite_eq_right h

theorem represent_le_iff (b c : B) : g.order.le (g.represent b) (g.represent c) ↔ Q.le b c := by
  classical
  by_cases hb : Q.le b g.rightAnchor
  · rw [g.represent_old b hb]
    by_cases hc : Q.le c g.rightAnchor
    · rw [g.represent_old c hc]
      exact g.overlap.le_iff _ _
    · rw [g.represent_new c hc]
      change P.le (g.overlap.toFun ⟨b, hb⟩).val (g.overlap.toFun (cut Q g.rightAnchor c)).val ↔ _
      change (idealOrder P g.leftAnchor).le (g.overlap.toFun ⟨b, hb⟩)
        (g.overlap.toFun (cut Q g.rightAnchor c)) ↔ _
      rw [g.overlap.le_iff]
      exact ⟨fun h => Q.trans h (Q.meet_le_left _ _), fun h => Q.le_meet h hb⟩
  · rw [g.represent_new b hb]
    by_cases hc : Q.le c g.rightAnchor
    · rw [g.represent_old c hc]
      exact ⟨False.elim, fun h => hb (Q.trans h hc)⟩
    · rw [g.represent_new c hc]
      exact ⟨fun h => h.elim id False.elim, Or.inl⟩

theorem old_below_represent (a : A) (b : B) :
    g.order.le (.inl a) (g.represent b) ↔ P.le a (g.shadow b) := by
  classical
  by_cases h : Q.le b g.rightAnchor
  · rw [g.represent_old b h]
    unfold shadow
    rw [cut_of_le Q g.rightAnchor b h]
    exact Iff.rfl
  · rw [g.represent_new b h]
    exact Iff.rfl

theorem represented_meet (b c : B) :
    IsMeet g.data (g.represent b) (g.represent c) (g.represent (Q.meet b c)) := by
  refine ⟨(g.represent_le_iff _ _).mpr (Q.meet_le_left _ _),
    (g.represent_le_iff _ _).mpr (Q.meet_le_right _ _), ?_⟩
  intro x hx hy
  cases x with
  | inl a =>
    apply (g.old_below_represent a _).mpr
    rw [g.shadow_meet]
    exact P.le_meet ((g.old_below_represent a b).mp hx) ((g.old_below_represent a c).mp hy)
  | inr x =>
    have represented : g.represent x.val = Sum.inr x := g.represent_new x.val x.property
    rw [← represented] at hx hy ⊢
    exact (g.represent_le_iff _ _).mpr
      (Q.le_meet ((g.represent_le_iff _ _).mp hx) ((g.represent_le_iff _ _).mp hy))

noncomputable def right : MeetEmbedding Q g.order where
  toFun := g.represent
  le_iff := g.represent_le_iff
  map_meet b c := (meet_eq g.data g.component_meets (g.represented_meet b c)).symm

theorem cover (x : g.Node) : (∃ a, g.left.toFun a = x) ∨ (∃ b, g.right.toFun b = x) := by
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr b => exact Or.inr ⟨b.val, g.represent_new b.val b.property⟩

theorem left_ideal (a : A) (x : g.Node) (h : g.order.le x (g.left.toFun a)) :
    ∃ b, g.left.toFun b = x := by
  cases x with
  | inl b => exact ⟨b, rfl⟩
  | inr x => exact False.elim h

theorem overlap_exact (a : A) (b : B) :
    g.right.toFun b = g.left.toFun a ↔
      ∃ h : Q.le b g.rightAnchor, (g.overlap.toFun ⟨b, h⟩).val = a := by
  classical
  change g.represent b = Sum.inl a ↔ _
  by_cases h : Q.le b g.rightAnchor
  · rw [g.represent_old b h]
    constructor
    · intro eq
      exact ⟨h, Sum.inl.inj eq⟩
    · rintro ⟨_, eq⟩
      exact congrArg Sum.inl eq
  · rw [g.represent_new b h]
    exact ⟨(fun eq => by cases eq), fun ⟨hb, _⟩ => False.elim (h hb)⟩

theorem old_in_right (a : A) :
    (∃ b, g.right.toFun b = g.left.toFun a) ↔ P.le a g.leftAnchor := by
  constructor
  · rintro ⟨b, eq⟩
    rcases (g.overlap_exact a b).mp eq with ⟨hb, val⟩
    exact val ▸ (g.overlap.toFun ⟨b, hb⟩).property
  · intro ha
    let b := g.overlap.inverse ⟨a, ha⟩
    refine ⟨b.val, (g.overlap_exact a b.val).mpr ⟨b.property, ?_⟩⟩
    exact congrArg Subtype.val (g.overlap.right_inverse ⟨a, ha⟩)

theorem right_ideal (b : B) (x : g.Node) (h : g.order.le x (g.right.toFun b)) :
    ∃ c, g.right.toFun c = x := by
  cases x with
  | inl a =>
    apply (g.old_in_right a).mpr
    exact P.trans ((g.old_below_represent a b).mp h) (g.shadow_le_anchor b)
  | inr x => exact ⟨x.val, g.represent_new x.val x.property⟩

end Input

end PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation



namespace PartitionPilot.Compression.RecursiveMaps.BinaryTiles

open Attachment PrincipalAmalgamation

universe u

variable {A : Type u} (P : MeetOrder A)

def separation (W : A) : Input P P where
  leftAnchor := W
  rightAnchor := W
  overlap :=
    { toFun := id
      le_iff := fun _ _ => Iff.rfl
      map_meet := fun _ _ => rfl
      inverse := id
      left_inverse := fun _ => rfl
      right_inverse := fun _ => rfl }

def compression (T K : A) (top : ∀ x, P.le x T) (S : MeetIso P (idealOrder P K)) :
    Input P P where
  leftAnchor := K
  rightAnchor := T
  overlap :=
    { toFun := fun x => S.toFun x.val
      le_iff := fun x y => S.le_iff x.val y.val
      map_meet := fun x y => S.map_meet x.val y.val
      inverse := fun y => ⟨S.inverse y, top _⟩
      left_inverse := fun x => Subtype.ext (S.left_inverse x.val)
      right_inverse := fun y => S.right_inverse y }

theorem compression_identification (T K : A) (top : ∀ x, P.le x T)
    (S : MeetIso P (idealOrder P K)) (x : A) :
    (compression P T K top S).right.toFun x =
      (compression P T K top S).left.toFun (S.toFun x).val :=
  (compression P T K top S).represent_old x (top x)

end PartitionPilot.Compression.RecursiveMaps.BinaryTiles

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompatibleCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CompatibleCopies

universe u v

structure Data {A : Type u} (P : MeetOrder A) (I : Type v) where
  top : A
  greatest : ∀ x, P.le x top
  anchor : I → I → A
  change : I → I → MeetIso P P
  self_anchor : ∀ i, anchor i i = top
  self_change : ∀ i x, (change i i).toFun x = x
  reverse : ∀ i j x, (change j i).toFun ((change i j).toFun x) = x
  anchor_change : ∀ i j, (change i j).toFun (anchor i j) = anchor j i
  triangle_domain : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x, P.le x (anchor i j) →
    (P.le ((change i j).toFun x) (anchor j k) ↔ P.le x (anchor i k))
  triangle_change : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x,
    P.le x (anchor i j) → P.le x (anchor i k) →
    (change j k).toFun ((change i j).toFun x) = (change i k).toFun x

namespace Data

variable {A : Type u} {I : Type v} {P : MeetOrder A} (d : Data P I)

theorem change_anchor_bound (i j : I) (x : A) (h : P.le x (d.anchor i j)) :
    P.le ((d.change i j).toFun x) (d.anchor j i) := by
  rw [← d.anchor_change i j]
  exact ((d.change i j).le_iff _ _).mpr h

theorem domain (i j k : I) (x : A) (h : P.le x (d.anchor i j)) :
    P.le ((d.change i j).toFun x) (d.anchor j k) ↔ P.le x (d.anchor i k) := by
  classical
  by_cases ij : i = j
  · subst j
    rw [d.self_change]
  · by_cases jk : j = k
    · subst k
      rw [d.self_anchor]
      exact ⟨fun _ => h, fun _ => d.greatest _⟩
    · by_cases ik : i = k
      · subst k
        rw [d.self_anchor]
        exact ⟨fun _ => d.greatest _, fun _ => d.change_anchor_bound i j x h⟩
      · exact d.triangle_domain i j k ij jk ik x h

theorem cocycle (i j k : I) (x : A)
    (hij : P.le x (d.anchor i j)) (hik : P.le x (d.anchor i k)) :
    (d.change j k).toFun ((d.change i j).toFun x) = (d.change i k).toFun x := by
  classical
  by_cases ij : i = j
  · subst j
    rw [d.self_change]
  · by_cases jk : j = k
    · subst k
      rw [d.self_change]
    · by_cases ik : i = k
      · subst k
        rw [d.reverse, d.self_change]
      · exact d.triangle_change i j k ij jk ik x hij hik

def Label (_d : Data P I) := I × A

def Related (x y : d.Label) : Prop :=
  P.le x.2 (d.anchor x.1 y.1) ∧ (d.change x.1 y.1).toFun x.2 = y.2

theorem related_refl (x : d.Label) : d.Related x x := by
  constructor
  · rw [d.self_anchor]
    exact d.greatest _
  · exact d.self_change _ _

theorem related_symm {x y : d.Label} (h : d.Related x y) : d.Related y x := by
  constructor
  · rw [← h.2]
    exact d.change_anchor_bound _ _ _ h.1
  · rw [← h.2, d.reverse]

theorem related_trans {x y z : d.Label} (hxy : d.Related x y) (hyz : d.Related y z) :
    d.Related x z := by
  have changed : P.le ((d.change x.1 y.1).toFun x.2) (d.anchor y.1 z.1) := by
    rw [hxy.2]
    exact hyz.1
  have hxz := (d.domain x.1 y.1 z.1 x.2 hxy.1).mp changed
  refine ⟨hxz, ?_⟩
  rw [← d.cocycle x.1 y.1 z.1 x.2 hxy.1 hxz, hxy.2]
  exact hyz.2

def setoid : Setoid d.Label where
  r := d.Related
  iseqv := ⟨d.related_refl, d.related_symm, d.related_trans⟩

def Le (x y : d.Label) : Prop :=
  P.le x.2 (d.anchor x.1 y.1) ∧ P.le ((d.change x.1 y.1).toFun x.2) y.2

theorem le_refl (x : d.Label) : d.Le x x :=
  ⟨(d.related_refl x).1, (d.self_change _ _).symm ▸ P.refl x.2⟩

theorem related_le {x y : d.Label} (h : d.Related x y) : d.Le x y :=
  ⟨h.1, h.2.symm ▸ P.refl y.2⟩

theorem le_trans {x y z : d.Label} (hxy : d.Le x y) (hyz : d.Le y z) : d.Le x z := by
  have changed := P.trans hxy.2 hyz.1
  have hxz := (d.domain x.1 y.1 z.1 x.2 hxy.1).mp changed
  refine ⟨hxz, ?_⟩
  rw [← d.cocycle x.1 y.1 z.1 x.2 hxy.1 hxz]
  exact P.trans (((d.change y.1 z.1).le_iff _ _).mpr hxy.2) hyz.2

theorem le_antisymm_related {x y : d.Label} (hxy : d.Le x y) (hyx : d.Le y x) :
    d.Related x y := by
  refine ⟨hxy.1, P.antisymm hxy.2 ?_⟩
  have lower := ((d.change x.1 y.1).le_iff _ _).mpr hyx.2
  rw [d.reverse] at lower
  exact lower

theorem same_vertex_le (i : I) (x y : A) : d.Le (i, x) (i, y) ↔ P.le x y := by
  constructor
  · intro h
    simpa only [d.self_change] using h.2
  · intro h
    exact ⟨(d.self_anchor i).symm ▸ d.greatest x, (d.self_change i x).symm ▸ h⟩

def part (i j : I) (y : A) : A := (d.change j i).toFun (P.meet y (d.anchor j i))

theorem part_anchor (i j : I) (y : A) : P.le (d.part i j y) (d.anchor i j) :=
  d.change_anchor_bound j i _ (P.meet_le_right _ _)

theorem part_below (i j : I) (y : A) : d.Le (i, d.part i j y) (j, y) := by
  refine ⟨d.part_anchor i j y, ?_⟩
  change P.le ((d.change i j).toFun ((d.change j i).toFun _)) y
  rw [d.reverse]
  exact P.meet_le_left _ _

theorem below_iff_part (i j : I) (x y : A) : d.Le (i, x) (j, y) ↔ P.le x (d.part i j y) := by
  constructor
  · intro h
    have lower := ((d.change j i).le_iff _ _).mpr
      (P.le_meet h.2 (d.change_anchor_bound i j x h.1))
    rw [d.reverse] at lower
    exact lower
  · intro h
    exact d.le_trans ((d.same_vertex_le i _ _).mpr h) (d.part_below i j y)

theorem move_to_upper_vertex {x y : d.Label} (lower : d.Le x y) :
    d.Related x (y.1, (d.change x.1 y.1).toFun x.2) ∧
      P.le ((d.change x.1 y.1).toFun x.2) y.2 :=
  ⟨⟨lower.1, rfl⟩, lower.2⟩

end Data
end PartitionPilot.Compression.RecursiveMaps.CompatibleCopies

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_CopyQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data

universe u v

variable {A : Type u} {I : Type v} {P : MeetOrder A} (d : Data P I)

def Node := Quotient d.setoid

def point (i : I) (x : A) : d.Node := Quotient.mk d.setoid (i, x)

def nodeLe : d.Node → d.Node → Prop :=
  Quotient.lift₂ d.Le (fun _ _ _ _ ha hb => propext
    ⟨fun h => d.le_trans (d.related_le (d.related_symm ha)) (d.le_trans h (d.related_le hb)),
     fun h => d.le_trans (d.related_le ha) (d.le_trans h (d.related_le (d.related_symm hb)))⟩)

theorem mk_eq_mk (i j : I) (x y : A) : d.point i x = d.point j y ↔ d.Related (i, x) (j, y) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem node_refl (x : d.Node) : d.nodeLe x x := by
  induction x using Quotient.ind with
  | _ x => exact d.le_refl x

theorem node_trans {x y z : d.Node} (hxy : d.nodeLe x y) (hyz : d.nodeLe y z) : d.nodeLe x z := by
  induction x, y, z using Quotient.inductionOn₃ with
  | _ x y z => exact d.le_trans hxy hyz

theorem node_antisymm {x y : d.Node} (hxy : d.nodeLe x y) (hyx : d.nodeLe y x) : x = y := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact Quotient.sound (d.le_antisymm_related hxy hyx)

theorem vertex_le (i : I) (x y : A) : d.nodeLe (d.point i x) (d.point i y) ↔ P.le x y :=
  d.same_vertex_le i x y

theorem vertex_below (i j : I) (x y : A) :
    d.nodeLe (d.point i x) (d.point j y) ↔ P.le x (d.part i j y) :=
  d.below_iff_part i j x y

theorem cover (x : d.Node) : ∃ i y, d.point i y = x := by
  induction x using Quotient.ind with
  | _ x => exact ⟨x.1, x.2, rfl⟩

theorem vertex_ideal (i : I) (y : A) (x : d.Node) (lower : d.nodeLe x (d.point i y)) :
    ∃ z, d.point i z = x := by
  induction x using Quotient.ind with
  | _ x =>
    have moved := d.move_to_upper_vertex lower
    exact ⟨(d.change x.1 i).toFun x.2, (Quotient.sound moved.1).symm⟩

def IsMeet (x y m : d.Node) : Prop :=
  d.nodeLe m x ∧ d.nodeLe m y ∧ ∀ z, d.nodeLe z x → d.nodeLe z y → d.nodeLe z m

theorem cross_meet_spec (i j : I) (x y : A) :
    d.IsMeet (d.point i x) (d.point j y) (d.point i (P.meet x (d.part i j y))) := by
  refine ⟨(d.vertex_le i _ _).mpr (P.meet_le_left _ _),
    (d.vertex_below i j _ _).mpr (P.meet_le_right _ _), ?_⟩
  intro z hx hy
  rcases d.vertex_ideal i x z hx with ⟨a, rfl⟩
  exact (d.vertex_le i _ _).mpr
    (P.le_meet ((d.vertex_le i _ _).mp hx) ((d.vertex_below i j _ _).mp hy))

theorem all_meets (x y : d.Node) : ∃ m, d.IsMeet x y m := by
  induction x, y using Quotient.inductionOn₂ with
  | _ x y => exact ⟨_, d.cross_meet_spec x.1 y.1 x.2 y.2⟩

noncomputable def order : MeetOrder d.Node where
  le := d.nodeLe
  meet x y := Classical.choose (d.all_meets x y)
  refl := d.node_refl
  trans := d.node_trans
  antisymm := d.node_antisymm
  meet_le_left x y := (Classical.choose_spec (d.all_meets x y)).1
  meet_le_right x y := (Classical.choose_spec (d.all_meets x y)).2.1
  le_meet hx hy := (Classical.choose_spec (d.all_meets _ _)).2.2 _ hx hy

theorem meet_eq {x y m : d.Node} (h : d.IsMeet x y m) : d.order.meet x y = m :=
  d.node_antisymm (h.2.2 _ (d.order.meet_le_left x y) (d.order.meet_le_right x y))
    (d.order.le_meet h.1 h.2.1)

theorem vertex_meet_spec (i : I) (x y : A) :
    d.IsMeet (d.point i x) (d.point i y) (d.point i (P.meet x y)) := by
  refine ⟨(d.vertex_le i _ _).mpr (P.meet_le_left _ _),
    (d.vertex_le i _ _).mpr (P.meet_le_right _ _), ?_⟩
  intro z hx hy
  rcases d.vertex_ideal i x z hx with ⟨a, rfl⟩
  exact (d.vertex_le i _ _).mpr
    (P.le_meet ((d.vertex_le i _ _).mp hx) ((d.vertex_le i _ _).mp hy))

noncomputable def vertex (i : I) : MeetEmbedding P d.order where
  toFun := d.point i
  le_iff := d.vertex_le i
  map_meet x y := (d.meet_eq (d.vertex_meet_spec i x y)).symm

theorem exact_overlap (i j : I) (x y : A) :
    (d.vertex i).toFun x = (d.vertex j).toFun y ↔
      P.le x (d.anchor i j) ∧ (d.change i j).toFun x = y :=
  d.mk_eq_mk i j x y

end PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleTile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Rectangle

universe u

inductive Vertex where
  | root | one | two
  deriving DecidableEq

instance instCountableVertex : Countable Vertex := by
  apply Function.Injective.countable
    (f := fun v => match v with | .root => (0 : Nat) | .one => 1 | .two => 2)
  intro x y eq
  cases x <;> cases y <;> simp_all

structure Input {A : Type u} (P : MeetOrder A) where
  top : A
  greatest : ∀ x, P.le x top
  C : A
  B : A
  D : A
  C_le_D : P.le C D
  B_le_D : P.le B D
  g1 : MeetIso P P
  g2 : MeetIso P P
  agree : ∀ x, P.le x (P.meet C B) → g1.toFun x = g2.toFun x
  separated : P.meet (g1.toFun D) (g2.toFun D) = g1.toFun (P.meet C B)

namespace Input

variable {A : Type u} {P : MeetOrder A} (r : Input P)

def W : A := P.meet r.C r.B

theorem agree_W : r.g1.toFun r.W = r.g2.toFun r.W := r.agree r.W (P.refl r.W)

theorem root_intersection : P.meet (r.g1.toFun r.C) (r.g2.toFun r.C) = r.g1.toFun r.W := by
  apply P.antisymm
  · have separated : P.meet (r.g1.toFun r.D) (r.g2.toFun r.D) = r.g1.toFun r.W := r.separated
    rw [← separated]
    exact P.le_meet
      (P.trans (P.meet_le_left _ _) ((r.g1.le_iff _ _).mpr r.C_le_D))
      (P.trans (P.meet_le_right _ _) ((r.g2.le_iff _ _).mpr r.C_le_D))
  · apply P.le_meet
    · exact (r.g1.le_iff _ _).mpr (P.meet_le_left _ _)
    · rw [r.agree_W]
      exact (r.g2.le_iff _ _).mpr (P.meet_le_left _ _)

theorem image_bound (f g : MeetIso P P)
    (intersection : P.meet (f.toFun r.C) (g.toFun r.C) = f.toFun r.W)
    (x : A) (hx : P.le x r.C) : P.le (f.toFun x) (g.toFun r.C) ↔ P.le x r.B := by
  constructor
  · intro h
    have lower := P.le_meet ((f.le_iff _ _).mpr hx) h
    rw [intersection] at lower
    exact P.trans ((f.le_iff _ _).mp lower) (P.meet_le_right _ _)
  · intro h
    have lower : P.le (f.toFun x) (f.toFun r.W) := (f.le_iff _ _).mpr (P.le_meet hx h)
    rw [← intersection] at lower
    exact P.trans lower (P.meet_le_right _ _)

theorem g1_bound (x : A) (hx : P.le x r.C) :
    P.le (r.g1.toFun x) (r.g2.toFun r.C) ↔ P.le x r.B :=
  r.image_bound r.g1 r.g2 r.root_intersection x hx

theorem g2_bound (x : A) (hx : P.le x r.C) :
    P.le (r.g2.toFun x) (r.g1.toFun r.C) ↔ P.le x r.B := by
  apply r.image_bound r.g2 r.g1
  rw [meet_comm, r.root_intersection, r.agree_W]
  exact hx

theorem inverse1_C (x : A) (hx : P.le x (r.g1.toFun r.C)) : P.le (r.g1.inverse x) r.C := by
  apply (r.g1.le_iff _ _).mp
  rw [r.g1.right_inverse]
  exact hx

theorem inverse2_C (x : A) (hx : P.le x (r.g2.toFun r.C)) : P.le (r.g2.inverse x) r.C := by
  apply (r.g2.le_iff _ _).mp
  rw [r.g2.right_inverse]
  exact hx

theorem root_domain1 (x : A) (hx : P.le x (r.g1.toFun r.C)) :
    P.le (r.g1.inverse x) r.B ↔ P.le x (r.g2.toFun r.C) := by
  have h := (r.g1_bound (r.g1.inverse x) (r.inverse1_C x hx)).symm
  rw [r.g1.right_inverse] at h
  exact h

theorem root_domain2 (x : A) (hx : P.le x (r.g2.toFun r.C)) :
    P.le (r.g2.inverse x) r.B ↔ P.le x (r.g1.toFun r.C) := by
  have h := (r.g2_bound (r.g2.inverse x) (r.inverse2_C x hx)).symm
  rw [r.g2.right_inverse] at h
  exact h

theorem inverses_agree (x : A) (h1 : P.le x (r.g1.toFun r.C))
    (h2 : P.le x (r.g2.toFun r.C)) : r.g1.inverse x = r.g2.inverse x := by
  have hx : P.le (r.g1.inverse x) r.W :=
    P.le_meet (r.inverse1_C x h1) ((r.root_domain1 x h1).mpr h2)
  have eq : r.g2.toFun (r.g1.inverse x) = x :=
    (r.agree _ hx).symm.trans (r.g1.right_inverse x)
  have inv := congrArg r.g2.inverse eq
  rw [r.g2.left_inverse] at inv
  exact inv

def anchor : Vertex → Vertex → A
  | .root, .root => r.top
  | .one, .one => r.top
  | .two, .two => r.top
  | .root, .one => r.g1.toFun r.C
  | .one, .root => r.C
  | .root, .two => r.g2.toFun r.C
  | .two, .root => r.C
  | .one, .two => r.B
  | .two, .one => r.B

def transition : Vertex → Vertex → MeetIso P P
  | .root, .one => inverseIso r.g1
  | .one, .root => r.g1
  | .root, .two => inverseIso r.g2
  | .two, .root => r.g2
  | _, _ => identityIso P

theorem triangle_domain (i j k : Vertex) (ij : i ≠ j) (jk : j ≠ k) (ik : i ≠ k)
    (x : A) (hx : P.le x (r.anchor i j)) :
    P.le ((r.transition i j).toFun x) (r.anchor j k) ↔ P.le x (r.anchor i k) := by
  cases i <;> cases j <;> cases k <;> try contradiction
  · exact r.root_domain1 x hx
  · exact r.root_domain2 x hx
  · exact r.g1_bound x hx
  · exact Iff.rfl
  · exact r.g2_bound x hx
  · exact Iff.rfl

theorem triangle_change (i j k : Vertex) (ij : i ≠ j) (jk : j ≠ k) (ik : i ≠ k)
    (x : A) (hx : P.le x (r.anchor i j)) (hy : P.le x (r.anchor i k)) :
    (r.transition j k).toFun ((r.transition i j).toFun x) = (r.transition i k).toFun x := by
  cases i <;> cases j <;> cases k <;> try contradiction
  · exact r.inverses_agree x hx hy
  · exact (r.inverses_agree x hy hx).symm
  · change r.g2.inverse (r.g1.toFun x) = x
    rw [r.agree x (P.le_meet hx hy), r.g2.left_inverse]
  · exact (r.agree x (P.le_meet hy hx)).symm
  · change r.g1.inverse (r.g2.toFun x) = x
    rw [← r.agree x (P.le_meet hx hy), r.g1.left_inverse]
  · exact r.agree x (P.le_meet hy hx)

def copies : CompatibleCopies.Data P Vertex where
  top := r.top
  greatest := r.greatest
  anchor := r.anchor
  change := r.transition
  self_anchor := by intro i; cases i <;> rfl
  self_change := by intro i x; cases i <;> rfl
  reverse := by
    intro i j x
    cases i <;> cases j
    · rfl
    · exact r.g1.right_inverse x
    · exact r.g2.right_inverse x
    · exact r.g1.left_inverse x
    · rfl
    · rfl
    · exact r.g2.left_inverse x
    · rfl
    · rfl
  anchor_change := by
    intro i j
    cases i <;> cases j
    · rfl
    · exact r.g1.left_inverse r.C
    · exact r.g2.left_inverse r.C
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  triangle_domain := r.triangle_domain
  triangle_change := r.triangle_change

end Input
end PartitionPilot.Compression.RecursiveMaps.Rectangle

end

section

namespace PartitionPilot.Compression.RecursiveMaps.Rectangle.Input

universe u

variable {A : Type u} {P : MeetOrder A} (r : Input P)

noncomputable def root : MeetEmbedding P r.copies.order := r.copies.vertex .root
noncomputable def first : MeetEmbedding P r.copies.order := r.copies.vertex .one
noncomputable def second : MeetEmbedding P r.copies.order := r.copies.vertex .two

theorem first_root_intersection (x y : A) :
    r.first.toFun x = r.root.toFun y ↔ P.le x r.C ∧ r.g1.toFun x = y :=
  r.copies.exact_overlap .one .root x y

theorem second_root_intersection (x y : A) :
    r.second.toFun x = r.root.toFun y ↔ P.le x r.C ∧ r.g2.toFun x = y :=
  r.copies.exact_overlap .two .root x y

theorem children_intersection (x y : A) :
    r.first.toFun x = r.second.toFun y ↔ P.le x r.B ∧ x = y :=
  r.copies.exact_overlap .one .two x y

theorem three_vertex_cover (x : r.copies.Node) :
    ∃ i y, (r.copies.vertex i).toFun y = x := r.copies.cover x

end PartitionPilot.Compression.RecursiveMaps.Rectangle.Input

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalWordRewriteRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry

universe u

variable (J S : Type u) [Group J]

def Factor : Bool → Type u
  | false => J
  | true => FreeGroup S

instance factorGroup (b : Bool) : Group (Factor J S b) := by
  cases b <;> dsimp [Factor] <;> infer_instance

abbrev External := Monoid.CoprodI (Factor J S)

def old : J →* External J S := Monoid.CoprodI.of (M := Factor J S) (i := false)
def free : FreeGroup S →* External J S := Monoid.CoprodI.of (M := Factor J S) (i := true)
def generator (s : S) : External J S := free J S (FreeGroup.of s)
def signed (a : S × Bool) : External J S := free J S (FreeGroup.mk [a])

theorem old_injective : Function.Injective (old J S) := Monoid.CoprodI.of_injective (M := Factor J S) false

def Cancel (a b : S × Bool) : Prop := a.1 = b.1 ∧ a.2 = !b.2

def Reduced : List ((S × Bool) × J) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => (x.2 = 1 → ¬ Cancel S x.1 y.1) ∧ Reduced (y :: rest)

def eval : List ((S × Bool) × J) → External J S
  | [] => 1
  | (a, j) :: rest => signed J S a * old J S j * eval rest

open Monoid.CoprodI

noncomputable def oldWord (j : J) : Word (Factor J S) := by
  classical
  exact if h : j = 1 then Word.empty else Word.cons (i := false) j Word.empty (by simp [Word.fstIdx, Word.empty]) h

theorem oldWord_prod (j : J) : (oldWord J S j).prod = old J S j := by
  classical
  by_cases h : j = 1
  · subst j
    rw [oldWord, dite_eq_left rfl]
    exact (map_one (old J S)).symm
  · rw [oldWord, dite_eq_right h]
    exact (Word.prod_cons (M := Factor J S) false j Word.empty h _).trans (mul_one _)

theorem oldWord_not_free (j : J) : (oldWord J S j).fstIdx ≠ some true := by
  classical
  by_cases h : j = 1
  · simp [oldWord, h, Word.fstIdx, Word.empty]
  · rw [oldWord, dite_eq_right h]
    change (some false : Option Bool) ≠ some true
    decide

theorem free_head_not_old (w : Word (Factor J S)) (head : w.fstIdx = some true) (j : J) :
    w.prod ≠ old J S j := by
  classical
  intro eq
  have same : w = oldWord J S j := by
    apply (Word.equiv (M := Factor J S)).symm.injective
    exact eq.trans (oldWord_prod J S j).symm
  exact oldWord_not_free J S j (same ▸ head)

variable [DecidableEq S]

theorem free_prepend (a b : S × Bool) (f : FreeGroup S)
    (head : f.toWord.head? = some b) (safe : ¬ Cancel S a b) :
    (FreeGroup.mk (a :: f.toWord)).toWord = a :: f.toWord := by
  classical
  rw [FreeGroup.toWord_mk, FreeGroup.reduce.cons, FreeGroup.reduce_toWord]
  cases h : f.toWord with
  | nil => simp [h] at head
  | cons c rest =>
    have cb : c = b := by simpa [h] using head
    subst c
    change (if a.1 = b.1 ∧ a.2 = !b.2 then rest else a :: b :: rest) = a :: b :: rest
    change ¬ (a.1 = b.1 ∧ a.2 = !b.2) at safe
    rw [ite_eq_right safe]

theorem signed_mul_free (a : S × Bool) (f : FreeGroup S) :
    signed J S a * free J S f = free J S (FreeGroup.mk (a :: f.toWord)) := by
  change free J S (FreeGroup.mk [a]) * free J S f = _
  rw [← map_mul]
  apply congrArg (free J S)
  calc
    FreeGroup.mk [a] * f = FreeGroup.mk [a] * FreeGroup.mk f.toWord := by rw [FreeGroup.mk_toWord]
    _ = _ := FreeGroup.mul_mk

theorem head_nontrivial (a : S × Bool) (f : FreeGroup S)
    (head : f.toWord.head? = some a) : f ≠ 1 := by
  intro eq
  simp [eq] at head

theorem relative_normal_form (a : S × Bool) (j : J) (rest : List ((S × Bool) × J))
    (reduced : Reduced J S ((a, j) :: rest)) :
    ∃ (f : FreeGroup S) (tail : Word (Factor J S)),
      f.toWord.head? = some a ∧ tail.fstIdx ≠ some true ∧
      eval J S ((a, j) :: rest) = free J S f * tail.prod := by
  classical
  induction rest generalizing a j with
  | nil =>
    refine ⟨FreeGroup.mk [a], oldWord J S j, rfl, oldWord_not_free J S j, ?_⟩
    rw [oldWord_prod]
    exact mul_one _
  | cons b rest ih =>
    rcases b with ⟨b, k⟩
    rcases ih b k reduced.2 with ⟨f, tail, first, tailHead, value⟩
    by_cases jone : j = 1
    · subst j
      have safe := reduced.1 rfl
      have prep := free_prepend S a b f first safe
      refine ⟨FreeGroup.mk (a :: f.toWord), tail, ?_, tailHead, ?_⟩
      · rw [prep]
        rfl
      · change signed J S a * old J S 1 * eval J S ((b, k) :: rest) = _
        rw [map_one, mul_one, value, ← mul_assoc, signed_mul_free]
    · let w := Word.cons (i := true) f tail tailHead (head_nontrivial S b f first)
      have wHead : w.fstIdx ≠ some false := by
        change (some true : Option Bool) ≠ some false
        decide
      let t := Word.cons (i := false) j w wHead jone
      refine ⟨FreeGroup.mk [a], t, rfl, ?_, ?_⟩
      · change (some false : Option Bool) ≠ some true
        decide
      · change signed J S a * old J S j * eval J S ((b, k) :: rest) =
          signed J S a * (old J S j * (free J S f * tail.prod))
        rw [value, mul_assoc]

theorem reduced_not_old (a : S × Bool) (j : J) (rest : List ((S × Bool) × J))
    (reduced : Reduced J S ((a, j) :: rest)) (k : J) :
    eval J S ((a, j) :: rest) ≠ old J S k := by
  classical
  rcases relative_normal_form J S a j rest reduced with ⟨f, tail, head, tailHead, value⟩
  let w := Word.cons (i := true) f tail tailHead (head_nontrivial S a f head)
  have prod : w.prod = eval J S ((a, j) :: rest) := by
    rw [value]
    exact Word.prod_cons true f tail _ _
  intro eq
  exact free_head_not_old J S w rfl k (prod.trans eq)

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_PrincipalBatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace CosetGeometry

universe u

variable (J S : Type u) [Group J]

def Same (x y : External J S) : Prop := ∃ j, x * old J S j = y

def cosetSetoid : Setoid (External J S) where
  r := Same J S
  iseqv := by
    constructor
    · intro x
      exact ⟨1, by rw [map_one, mul_one]⟩
    · rintro x y ⟨j, rfl⟩
      exact ⟨j⁻¹, by rw [map_inv, mul_inv_cancel_right]⟩
    · rintro x y z ⟨i, rfl⟩ ⟨j, rfl⟩
      exact ⟨i * j, by rw [map_mul, mul_assoc]⟩

def Vertex := Quotient (cosetSetoid J S)
def point (g : External J S) : Vertex J S := Quotient.mk (cosetSetoid J S) g

def root : Vertex J S := point J S 1

theorem point_eq (g h : External J S) : point J S g = point J S h ↔ ∃ j, g * old J S j = h :=
  ⟨fun eq => Quotient.exact eq, fun eq => Quotient.sound eq⟩

theorem root_eq_point (g : External J S) : root J S = point J S g ↔ ∃ j, old J S j = g := by
  rw [root, point_eq]
  simp only [one_mul]

def act (g : External J S) : Vertex J S → Vertex J S :=
  Quotient.map (fun x => g * x) (by
    rintro x y ⟨j, rfl⟩
    exact ⟨j, mul_assoc _ _ _⟩)

theorem act_point (g h : External J S) : act J S g (point J S h) = point J S (g * h) := rfl

theorem act_root (g : External J S) : act J S g (root J S) = point J S g := by
  change point J S (g * 1) = _
  rw [mul_one]

def Dart := (External J S × S) × Bool

def reverse (d : Dart J S) : Dart J S := (d.1, !d.2)

def startRep (d : Dart J S) : External J S :=
  if d.2 then d.1.1 else d.1.1 * generator J S d.1.2

def endRep (d : Dart J S) : External J S :=
  if d.2 then d.1.1 * generator J S d.1.2 else d.1.1

def letter (d : Dart J S) : S × Bool := (d.1.2, d.2)
def source (d : Dart J S) : Vertex J S := point J S (startRep J S d)
def target (d : Dart J S) : Vertex J S := point J S (endRep J S d)

theorem signed_false (s : S) : signed J S (s, false) = (generator J S s)⁻¹ := by
  rw [generator, ← map_inv]
  rfl

theorem end_eq (d : Dart J S) : startRep J S d * signed J S (letter J S d) = endRep J S d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b
  · change (w * generator J S s) * signed J S (s, false) = w
    rw [signed_false, mul_inv_cancel_right]
  · rfl

theorem target_reverse (d : Dart J S) : target J S (reverse J S d) = source J S d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b <;> rfl

theorem cancellation_reverses_edge (d e : Dart J S)
    (joined : startRep J S e = endRep J S d)
    (cancel : Cancel S (letter J S d) (letter J S e)) : e = reverse J S d := by
  rcases d with ⟨⟨w, s⟩, b⟩
  rcases e with ⟨⟨v, t⟩, c⟩
  cases b <;> cases c
  · simp [Cancel, letter] at cancel
  · have st : s = t := cancel.1
    subst t
    change v = w at joined
    subst v
    rfl
  · have st : s = t := cancel.1
    subst t
    change v * generator J S s = w * generator J S s at joined
    have vw := mul_right_cancel joined
    subst v
    rfl
  · simp [Cancel, letter] at cancel

def translate (g : External J S) (d : Dart J S) : Dart J S := ((g * d.1.1, d.1.2), d.2)

theorem source_translate (g : External J S) (d : Dart J S) :
    source J S (translate J S g d) = act J S g (source J S d) := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b
  · exact congrArg (point J S) (mul_assoc g w (generator J S s))
  · rfl

theorem target_translate (g : External J S) (d : Dart J S) :
    target J S (translate J S g d) = act J S g (target J S d) := by
  rcases d with ⟨⟨w, s⟩, b⟩
  cases b
  · rfl
  · exact congrArg (point J S) (mul_assoc g w (generator J S s))

inductive Follows : Vertex J S → List (Dart J S) → Vertex J S → Prop
  | nil (v) : Follows v [] v
  | cons (d : Dart J S) {L v} (tail : Follows (target J S d) L v) :
      Follows (source J S d) (d :: L) v

theorem follows_cons_source {v w : Vertex J S} {d : Dart J S} {L}
    (path : Follows J S v (d :: L) w) : v = source J S d := by
  cases path
  rfl

theorem follows_tail {v w : Vertex J S} {d : Dart J S} {L}
    (path : Follows J S v (d :: L) w) : Follows J S (target J S d) L w := by
  cases path with
  | cons _ tail => exact tail

theorem follows_append {v w z : Vertex J S} {L M}
    (first : Follows J S v L w) (second : Follows J S w M z) :
    Follows J S v (L ++ M) z := by
  induction first with
  | nil => exact second
  | cons d tail ih => exact Follows.cons d (ih second)

theorem follows_translate {v w : Vertex J S} {L} (path : Follows J S v L w)
    (g : External J S) :
    Follows J S (act J S g v) (L.map (translate J S g)) (act J S g w) := by
  induction path with
  | nil v => exact Follows.nil _
  | cons d tail ih =>
    rw [← source_translate, List.map_cons]
    apply Follows.cons
    rw [target_translate]
    exact ih







def NoBacktracking : List (Dart J S) → Prop
  | [] => True
  | [_] => True
  | d :: e :: rest => e ≠ reverse J S d ∧ NoBacktracking (e :: rest)

theorem follows_empty_eq {v w : Vertex J S} {L : List (Dart J S)}
    (path : Follows J S v L w) (empty : L = []) : v = w := by
  induction path with
  | nil => rfl
  | cons d tail ih => cases empty

theorem follows_singleton_target {v w : Vertex J S} {d : Dart J S}
    (path : Follows J S v [d] w) : w = target J S d := by
  have tail : Follows J S (target J S d) [] w := follows_tail J S path
  exact (follows_empty_eq J S tail rfl).symm

theorem path_word (d : Dart J S) (tail : List (Dart J S)) (finish : Vertex J S)
    (path : Follows J S (source J S d) (d :: tail) finish)
    (reduced : NoBacktracking J S (d :: tail)) :
    ∃ j rest, Reduced J S ((letter J S d, j) :: rest) ∧
      point J S (startRep J S d * eval J S ((letter J S d, j) :: rest)) = finish := by
  induction tail generalizing d finish with
  | nil =>
    refine ⟨1, [], True.intro, ?_⟩
    rw [follows_singleton_target J S path]
    change point J S (startRep J S d * (signed J S (letter J S d) * old J S 1 * 1)) = _
    rw [map_one, mul_one, mul_one, end_eq]
    rfl
  | cons e tail ih =>
    have ep := follows_tail J S path
    have join : target J S d = source J S e := follows_cons_source J S ep
    rw [join] at ep
    rcases ih e finish ep reduced.2 with ⟨k, rest, ereduced, endpoint⟩
    rcases (point_eq J S (endRep J S d) (startRep J S e)).mp join with ⟨j, coordinate⟩
    refine ⟨j, (letter J S e, k) :: rest, ⟨?_, ereduced⟩, ?_⟩
    · intro jone cancel
      change j = 1 at jone
      have joined : startRep J S e = endRep J S d := by
        rw [jone, map_one, mul_one] at coordinate
        exact coordinate.symm
      exact reduced.1 (cancellation_reverses_edge J S d e joined cancel)
    · have transition : startRep J S d * signed J S (letter J S d) * old J S j = startRep J S e :=
        (congrArg (fun x => x * old J S j) (end_eq J S d)).trans coordinate
      calc
        point J S (startRep J S d * eval J S ((letter J S d, j) :: (letter J S e, k) :: rest)) =
            point J S ((startRep J S d * signed J S (letter J S d) * old J S j) *
              eval J S ((letter J S e, k) :: rest)) := by simp only [eval, mul_assoc]
        _ = point J S (startRep J S e * eval J S ((letter J S e, k) :: rest)) := by rw [transition]
        _ = finish := endpoint

theorem no_closed_reduced_path (v : Vertex J S) (d : Dart J S) (tail : List (Dart J S))
    (path : Follows J S v (d :: tail) v) : ¬ NoBacktracking J S (d :: tail) := by
  classical
  intro reduced
  have start := follows_cons_source J S path
  rw [start] at path
  rcases path_word J S d tail (source J S d) path reduced with ⟨j, rest, normal, endpoint⟩
  let value := eval J S ((letter J S d, j) :: rest)
  rcases (point_eq J S (startRep J S d * value) (startRep J S d)).mp endpoint with ⟨k, eq⟩
  have cancelled : value * old J S k = 1 := by
    apply mul_left_cancel (a := startRep J S d)
    simpa only [mul_assoc, mul_one] using eq
  have value_eq : value = old J S k⁻¹ := by
    calc
      value = value * (old J S k * old J S k⁻¹) := by rw [map_inv, mul_inv_cancel, mul_one]
      _ = (value * old J S k) * old J S k⁻¹ := (mul_assoc _ _ _).symm
      _ = old J S k⁻¹ := by rw [cancelled, one_mul]
  exact reduced_not_old J S (letter J S d) j rest normal k⁻¹ value_eq

def Reachable (g : External J S) : Prop :=
  ∃ L, Follows J S (root J S) L (point J S g)

theorem reachable_one : Reachable J S 1 := ⟨[], Follows.nil _⟩

theorem reachable_old (j : J) : Reachable J S (old J S j) := by
  have eq := (root_eq_point J S (old J S j)).mpr ⟨j, rfl⟩
  refine ⟨[], ?_⟩
  rw [← eq]
  exact Follows.nil _

theorem reachable_mul {g h : External J S} (hg : Reachable J S g) (hh : Reachable J S h) :
    Reachable J S (g * h) := by
  rcases hg with ⟨L, first⟩
  rcases hh with ⟨M, second⟩
  have shifted := follows_translate J S second g
  rw [act_root, act_point] at shifted
  exact ⟨L ++ M.map (translate J S g), follows_append J S first shifted⟩

theorem reachable_generator (s : S) : Reachable J S (generator J S s) := by
  let d : Dart J S := ((1, s), true)
  have path := Follows.cons d (Follows.nil (target J S d))
  change Follows J S (root J S) [d] (point J S (1 * generator J S s)) at path
  rw [one_mul] at path
  exact ⟨[d], path⟩

theorem reachable_generator_inv (s : S) : Reachable J S (generator J S s)⁻¹ := by
  let d : Dart J S := (((generator J S s)⁻¹, s), false)
  have path := Follows.cons d (Follows.nil (target J S d))
  change Follows J S (point J S ((generator J S s)⁻¹ * generator J S s)) [d]
    (point J S (generator J S s)⁻¹) at path
  rw [inv_mul_cancel] at path
  exact ⟨[d], path⟩

theorem reachable_free (f : FreeGroup S) : Reachable J S (free J S f) := by
  induction f using OAI.freeGroupInductionOn with
  | one => rw [map_one]; exact reachable_one J S
  | of letter => exact reachable_generator J S letter
  | inv_of letter _ => rw [map_inv]; exact reachable_generator_inv J S letter
  | mul first second firstReachable secondReachable =>
    rw [map_mul]
    exact reachable_mul J S firstReachable secondReachable

theorem reachable_element (g : External J S) : Reachable J S g := by
  induction g using Monoid.CoprodI.induction_on with
  | one => exact reachable_one J S
  | of i x =>
    cases i
    · exact reachable_old J S x
    · exact reachable_free J S x
  | mul x y hx hy => exact reachable_mul J S hx hy

theorem connected (v : Vertex J S) : ∃ L, Follows J S (root J S) L v := by
  induction v using Quotient.ind with
  | _ g => exact reachable_element J S g

theorem reversal_of_not_reduced (L : List (Dart J S)) (h : ¬ NoBacktracking J S L) :
    ∃ pre d suffix, L = pre ++ d :: reverse J S d :: suffix := by
  classical
  induction L with
  | nil => exact False.elim (h True.intro)
  | cons d tail ih =>
    cases tail with
    | nil => exact False.elim (h True.intro)
    | cons e tail =>
      by_cases back : e = reverse J S d
      · exact ⟨[], d, tail, by rw [back]; rfl⟩
      · rcases ih (fun ht => h ⟨back, ht⟩) with ⟨pre, x, suffix, eq⟩
        exact ⟨d :: pre, x, suffix, congrArg (List.cons d) eq⟩

theorem closed_path_has_reversal (v : Vertex J S) (d : Dart J S) (tail : List (Dart J S))
    (path : Follows J S v (d :: tail) v) :
    ∃ pre e suffix, d :: tail = pre ++ e :: reverse J S e :: suffix :=
  reversal_of_not_reduced J S _ (no_closed_reduced_path J S v d tail path)

end CosetGeometry



section

namespace EdgeWords

universe u
variable {E : Type u}

def reverse (d : E × Bool) : E × Bool := (d.1, !d.2)

def NoBacktracking : List (E × Bool) → Prop
  | [] => True
  | [_] => True
  | d :: e :: rest => e ≠ reverse d ∧ NoBacktracking (e :: rest)

theorem mk_cons (d : E × Bool) (L : List (E × Bool)) :
    FreeGroup.mk (d :: L) = FreeGroup.mk [d] * FreeGroup.mk L :=
  (@FreeGroup.mul_mk E [d] L).symm

theorem mk_delete_reversal (pre : List (E × Bool)) (d : E × Bool) (suffix) :
    FreeGroup.mk (pre ++ d :: reverse d :: suffix) = FreeGroup.mk (pre ++ suffix) :=
  Quot.sound FreeGroup.Red.Step.not

theorem reduce_of_no_backtracking [DecidableEq E] (L : List (E × Bool))
    (h : NoBacktracking L) : FreeGroup.reduce L = L := by
  induction L with
  | nil => rfl
  | cons d tail ih =>
    cases tail with
    | nil => rfl
    | cons e rest =>
      rw [FreeGroup.reduce.cons, ih h.2]
      have safe : ¬ (d.1 = e.1 ∧ d.2 = !e.2) := by
        rintro ⟨edges, signs⟩
        apply h.1
        change e = (d.1, !d.2)
        refine Prod.ext edges.symm ?_
        have flipped := congrArg Bool.not signs
        simpa only [Bool.not_not] using flipped.symm
      change (if d.1 = e.1 ∧ d.2 = !e.2 then rest else d :: e :: rest) = _
      rw [ite_eq_right safe]

end EdgeWords

namespace CosetGeometry

universe u
variable (J S : Type u) [Group J]

theorem follows_delete_reversal (pre : List (Dart J S)) (d : Dart J S) (suffix)
    {v w : Vertex J S} (path : Follows J S v (pre ++ d :: reverse J S d :: suffix) w) :
    Follows J S v (pre ++ suffix) w := by
  induction pre generalizing v with
  | nil =>
    have start := follows_cons_source J S path
    have tail := follows_tail J S (follows_tail J S path)
    rw [target_reverse] at tail
    rw [start]
    exact tail
  | cons e pre ih =>
    have start := follows_cons_source J S path
    rw [start]
    exact Follows.cons e (ih (follows_tail J S path))

theorem closed_edge_word (v : Vertex J S) (L : List (Dart J S))
    (path : Follows J S v L v) : FreeGroup.mk L = 1 := by
  cases hL : L with
  | nil => rfl
  | cons d tail =>
    rw [hL] at path
    rcases closed_path_has_reversal J S v d tail path with ⟨pre, e, suffix, eq⟩
    have cut : Follows J S v (pre ++ suffix) v := by
      apply follows_delete_reversal J S pre e suffix
      rw [← eq]
      exact path
    calc
      FreeGroup.mk (d :: tail) = FreeGroup.mk (pre ++ suffix) := by
        erw [eq]
        exact EdgeWords.mk_delete_reversal pre e suffix
      _ = 1 := closed_edge_word v (pre ++ suffix) cut
termination_by L.length
decreasing_by
  rw [hL]
  have lengths := congrArg List.length eq
  simp only [List.length_cons, List.length_append] at lengths ⊢
  omega

end CosetGeometry
end



namespace CosetGeometry.TileStars

universe u
variable (J S R : Type u) [Group J]

abbrev Center := External J S × R
abbrev OldEdge := External J S × S
def Vertex := Sum (CosetGeometry.Vertex J S) (Center J S R)
def Edge := Sum (Center J S R) (OldEdge J S)
abbrev Dart := Edge J S R × Bool

def reverse (d : Dart J S R) : Dart J S R := EdgeWords.reverse d

variable (request : S → R)

def centerOf (e : OldEdge J S) : Center J S R := (e.1, request e.2)

def source (d : Dart J S R) : Vertex J S R :=
  match d.1, d.2 with
  | .inl c, true => .inl (point J S c.1)
  | .inl c, false => .inr c
  | .inr e, true => .inr (centerOf J S R request e)
  | .inr e, false => .inl (point J S (e.1 * generator J S e.2))

def target (d : Dart J S R) : Vertex J S R :=
  source J S R request (reverse J S R d)

theorem reverse_reverse (d : Dart J S R) : reverse J S R (reverse J S R d) = d := by
  rcases d with ⟨e, b⟩
  cases b <;> rfl

theorem source_reverse (d : Dart J S R) :
    source J S R request (reverse J S R d) = target J S R request d := rfl

theorem target_reverse (d : Dart J S R) :
    target J S R request (reverse J S R d) = source J S R request d := by
  exact congrArg (source J S R request) (reverse_reverse J S R d)

def root : Vertex J S R := .inl (CosetGeometry.root J S)

inductive Follows : Vertex J S R → List (Dart J S R) → Vertex J S R → Prop
  | nil (v) : Follows v [] v
  | cons (d : Dart J S R) {L v}
      (tail : Follows (target J S R request d) L v) :
      Follows (source J S R request d) (d :: L) v

theorem follows_append {v w z : Vertex J S R} {L M}
    (first : Follows J S R request v L w) (second : Follows J S R request w M z) :
    Follows J S R request v (L ++ M) z := by
  induction first with
  | nil => exact second
  | cons d tail ih => exact Follows.cons d (ih second)

def contract : Vertex J S R → CosetGeometry.Vertex J S
  | .inl v => v
  | .inr c => point J S c.1

def projectDart (d : Dart J S R) : List (CosetGeometry.Dart J S) :=
  match d.1 with
  | .inl _ => []
  | .inr e => [(e, d.2)]

def project (L : List (Dart J S R)) : List (CosetGeometry.Dart J S) :=
  L.flatMap (projectDart J S R)

theorem contract_edge (d : Dart J S R) :
    CosetGeometry.Follows J S (contract J S R (source J S R request d))
      (projectDart J S R d) (contract J S R (target J S R request d)) := by
  rcases d with ⟨c | e, b⟩ <;> cases b
  · exact CosetGeometry.Follows.nil _
  · exact CosetGeometry.Follows.nil _
  · exact CosetGeometry.Follows.cons (e, false) (CosetGeometry.Follows.nil _)
  · exact CosetGeometry.Follows.cons (e, true) (CosetGeometry.Follows.nil _)

theorem follows_project {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) :
    CosetGeometry.Follows J S (contract J S R v) (project J S R L) (contract J S R w) := by
  induction path with
  | nil v => exact CosetGeometry.Follows.nil _
  | cons d tail ih =>
    exact CosetGeometry.follows_append J S (contract_edge J S R request d) ih

def expandDart (d : CosetGeometry.Dart J S) : List (Dart J S R) :=
  if d.2 then
    [(.inl (centerOf J S R request d.1), true), (.inr d.1, true)]
  else
    [(.inr d.1, false), (.inl (centerOf J S R request d.1), false)]

theorem expand_edge (d : CosetGeometry.Dart J S) :
    Follows J S R request (.inl (CosetGeometry.source J S d))
      (expandDart J S R request d) (.inl (CosetGeometry.target J S d)) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact Follows.cons (.inr e, false)
      (Follows.cons (.inl (centerOf J S R request e), false) (Follows.nil _))
  · exact Follows.cons (.inl (centerOf J S R request e), true)
      (Follows.cons (.inr e, true) (Follows.nil _))

theorem follows_expand {v w : CosetGeometry.Vertex J S} {L}
    (path : CosetGeometry.Follows J S v L w) :
    Follows J S R request (.inl v) (L.flatMap (expandDart J S R request)) (.inl w) := by
  induction path with
  | nil v => exact Follows.nil _
  | cons d tail ih => exact follows_append J S R request (expand_edge J S R request d) ih

theorem connected (v : Vertex J S R) :
    ∃ L, Follows J S R request (root J S R) L v := by
  cases v with
  | inl v =>
    rcases CosetGeometry.connected J S v with ⟨L, path⟩
    exact ⟨L.flatMap (expandDart J S R request), follows_expand J S R request path⟩
  | inr c =>
    rcases CosetGeometry.connected J S (point J S c.1) with ⟨L, path⟩
    have lifted := follows_expand J S R request path
    have stem := Follows.cons (J := J) (S := S) (R := R) (request := request)
      (.inl c, true) (Follows.nil _)
    exact ⟨_, follows_append J S R request lifted stem⟩

end CosetGeometry.TileStars



namespace CosetGeometry.TileStars

universe u
variable (J S R : Type u) [Group J] (request : S → R)

def potential : Vertex J S R → FreeGroup (Edge J S R)
  | .inl _ => 1
  | .inr c => FreeGroup.of (.inl c)

def expandHom : FreeGroup (OldEdge J S) →* FreeGroup (Edge J S R) :=
  FreeGroup.lift (fun e =>
    FreeGroup.of (.inl (centerOf J S R request e)) * FreeGroup.of (.inr e))

theorem edge_word (d : Dart J S R) :
    FreeGroup.mk [d] =
      (potential J S R (source J S R request d))⁻¹ *
        expandHom J S R request (FreeGroup.mk (projectDart J S R d)) *
          potential J S R (target J S R request d) := by
  rcases d with ⟨c | e, b⟩ <;> cases b
  · change (FreeGroup.of (.inl c : Edge J S R))⁻¹ =
      (FreeGroup.of (.inl c))⁻¹ * expandHom J S R request 1 * 1
    erw [map_one, mul_one, mul_one]
    rfl
  · change FreeGroup.of (.inl c : Edge J S R) =
      (1 : FreeGroup (Edge J S R))⁻¹ * expandHom J S R request 1 * FreeGroup.of (.inl c)
    erw [map_one, inv_one, one_mul]
    rfl
  · change (FreeGroup.of (.inr e : Edge J S R))⁻¹ =
      (1 : FreeGroup (Edge J S R))⁻¹ * expandHom J S R request (FreeGroup.of e)⁻¹ *
        FreeGroup.of (.inl (centerOf J S R request e))
    rw [inv_one, one_mul, map_inv]
    rw [expandHom, FreeGroup.lift_apply_of]
    change (FreeGroup.of (.inr e : Edge J S R))⁻¹ =
      (FreeGroup.of (.inl (centerOf J S R request e)) * FreeGroup.of (.inr e))⁻¹ *
        FreeGroup.of (.inl (centerOf J S R request e))
    rw [mul_inv_rev, inv_mul_cancel_right]
  · change FreeGroup.of (.inr e : Edge J S R) =
      (FreeGroup.of (.inl (centerOf J S R request e)))⁻¹ *
        expandHom J S R request (FreeGroup.of e) * 1
    rw [expandHom, FreeGroup.lift_apply_of]
    change FreeGroup.of (.inr e : Edge J S R) =
      (FreeGroup.of (.inl (centerOf J S R request e)))⁻¹ *
        (FreeGroup.of (.inl (centerOf J S R request e)) * FreeGroup.of (.inr e)) * 1
    rw [inv_mul_cancel_left, mul_one]

theorem path_word {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) :
    FreeGroup.mk L = (potential J S R v)⁻¹ *
      expandHom J S R request (FreeGroup.mk (project J S R L)) * potential J S R w := by
  induction path with
  | nil v =>
    change 1 = (potential J S R v)⁻¹ * expandHom J S R request 1 * potential J S R v
    rw [map_one, mul_one, inv_mul_cancel]
  | @cons d L w tail ih =>
    rw [EdgeWords.mk_cons, edge_word, ih]
    change (_ * expandHom J S R request (FreeGroup.mk (projectDart J S R d)) * _) *
      (_ * expandHom J S R request (FreeGroup.mk (project J S R L)) * _) =
      _ * expandHom J S R request (FreeGroup.mk (projectDart J S R d ++ project J S R L)) * _
    erw [← FreeGroup.mul_mk, map_mul]
    simp only [mul_assoc, mul_inv_cancel_left]

theorem closed_edge_word (v : Vertex J S R) (L : List (Dart J S R))
    (path : Follows J S R request v L v) : FreeGroup.mk L = 1 := by
  have equation := path_word J S R request path
  have contracted := CosetGeometry.closed_edge_word J S (contract J S R v)
    (project J S R L) (follows_project J S R request path)
  rw [contracted, map_one, mul_one, inv_mul_cancel] at equation
  exact equation

theorem reversal_of_not_reduced (L : List (Dart J S R)) (h : ¬ EdgeWords.NoBacktracking L) :
    ∃ pre d suffix, L = pre ++ d :: reverse J S R d :: suffix := by
  classical
  induction L with
  | nil => exact False.elim (h True.intro)
  | cons d tail ih =>
    cases tail with
    | nil => exact False.elim (h True.intro)
    | cons e tail =>
      by_cases back : e = reverse J S R d
      · exact ⟨[], d, tail, by rw [back]; rfl⟩
      · rcases ih (fun ht => h ⟨back, ht⟩) with ⟨pre, x, suffix, eq⟩
        exact ⟨d :: pre, x, suffix, congrArg (List.cons d) eq⟩

end CosetGeometry.TileStars



section

namespace EdgeWords

universe u
variable {E : Type u}

theorem reduced_words_injective {L M : List (E × Bool)}
    (hL : NoBacktracking L) (hM : NoBacktracking M)
    (eq : FreeGroup.mk L = FreeGroup.mk M) : L = M := by
  classical
  have words := congrArg FreeGroup.toWord eq
  simpa only [FreeGroup.toWord_mk, reduce_of_no_backtracking L hL,
    reduce_of_no_backtracking M hM] using words

theorem no_backtracking_append_left (L M : List (E × Bool))
    (h : NoBacktracking (L ++ M)) : NoBacktracking L := by
  induction L with
  | nil => exact True.intro
  | cons d tail ih =>
    cases tail with
    | nil => exact True.intro
    | cons e tail => exact ⟨h.1, ih h.2⟩

end EdgeWords

namespace CosetGeometry.TileStars

universe u
variable (J S R : Type u) [Group J] (request : S → R)

theorem follows_cons_source {v w : Vertex J S R} {d : Dart J S R} {L}
    (path : Follows J S R request v (d :: L) w) : v = source J S R request d := by
  cases path
  rfl

theorem follows_tail {v w : Vertex J S R} {d : Dart J S R} {L}
    (path : Follows J S R request v (d :: L) w) :
    Follows J S R request (target J S R request d) L w := by
  cases path with
  | cons _ tail => exact tail

theorem follows_delete_reversal (pre : List (Dart J S R)) (d : Dart J S R) (suffix)
    {v w : Vertex J S R}
    (path : Follows J S R request v (pre ++ d :: reverse J S R d :: suffix) w) :
    Follows J S R request v (pre ++ suffix) w := by
  induction pre generalizing v with
  | nil =>
    have start := follows_cons_source J S R request path
    have tail := follows_tail J S R request (follows_tail J S R request path)
    rw [target_reverse] at tail
    rw [start]
    exact tail
  | cons e pre ih =>
    have start := follows_cons_source J S R request path
    rw [start]
    exact Follows.cons e (ih (follows_tail J S R request path))

theorem reduced_path {v w : Vertex J S R} (L : List (Dart J S R))
    (path : Follows J S R request v L w) :
    ∃ M, Follows J S R request v M w ∧ EdgeWords.NoBacktracking M ∧ M.length ≤ L.length := by
  classical
  by_cases reduced : EdgeWords.NoBacktracking L
  · exact ⟨L, path, reduced, le_refl _⟩
  · rcases reversal_of_not_reduced J S R L reduced with ⟨pre, d, suffix, eq⟩
    have cut : Follows J S R request v (pre ++ suffix) w := by
      apply follows_delete_reversal J S R request pre d suffix
      rw [← eq]
      exact path
    rcases reduced_path (pre ++ suffix) cut with ⟨M, mp, mr, bound⟩
    refine ⟨M, mp, mr, le_trans bound ?_⟩
    rw [eq]
    simp only [List.length_append, List.length_cons]
    omega
termination_by L.length
decreasing_by
  rw [eq]
  simp only [List.length_append, List.length_cons]
  omega

theorem follows_reverse {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) :
    Follows J S R request w (FreeGroup.invRev L) v := by
  induction path with
  | nil v => exact Follows.nil _
  | @cons d L w tail ih =>
    rw [FreeGroup.invRev_cons]
    apply follows_append J S R request ih
    have last := Follows.cons (J := J) (S := S) (R := R) (request := request)
      (reverse J S R d) (Follows.nil _)
    rw [source_reverse, target_reverse] at last
    exact last

theorem path_words_equal {v w : Vertex J S R} {L M}
    (first : Follows J S R request v L w) (second : Follows J S R request v M w) :
    FreeGroup.mk L = FreeGroup.mk M := by
  have loop := follows_append J S R request first (follows_reverse J S R request second)
  have equation := closed_edge_word J S R request v (L ++ FreeGroup.invRev M) loop
  rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk] at equation
  exact mul_inv_eq_one.mp equation

theorem reduced_path_unique {v w : Vertex J S R} {L M}
    (first : Follows J S R request v L w) (second : Follows J S R request v M w)
    (hL : EdgeWords.NoBacktracking L) (hM : EdgeWords.NoBacktracking M) : L = M :=
  EdgeWords.reduced_words_injective hL hM (path_words_equal J S R request first second)

theorem unique_root_path (v : Vertex J S R) :
    ∃! L, Follows J S R request (root J S R) L v ∧ EdgeWords.NoBacktracking L := by
  rcases connected J S R request v with ⟨L, path⟩
  rcases reduced_path J S R request L path with ⟨M, mp, mr, _⟩
  exact ⟨M, ⟨mp, mr⟩, fun N hN => reduced_path_unique J S R request hN.1 mp hN.2 mr⟩

noncomputable def rootPath (v : Vertex J S R) : List (Dart J S R) :=
  Classical.choose (unique_root_path J S R request v).exists

theorem rootPath_follows (v : Vertex J S R) :
    Follows J S R request (root J S R) (rootPath J S R request v) v :=
  (Classical.choose_spec (unique_root_path J S R request v).exists).1

theorem rootPath_reduced (v : Vertex J S R) :
    EdgeWords.NoBacktracking (rootPath J S R request v) :=
  (Classical.choose_spec (unique_root_path J S R request v).exists).2

theorem rootPath_eq {v : Vertex J S R} {L}
    (path : Follows J S R request (root J S R) L v) (reduced : EdgeWords.NoBacktracking L) :
    rootPath J S R request v = L :=
  reduced_path_unique J S R request (rootPath_follows J S R request v) path
    (rootPath_reduced J S R request v) reduced

theorem rootPath_root : rootPath J S R request (root J S R) = [] :=
  rootPath_eq J S R request (Follows.nil _) True.intro

noncomputable def depth (v : Vertex J S R) : Nat := (rootPath J S R request v).length

theorem rootPath_shortest {v : Vertex J S R} {L}
    (path : Follows J S R request (root J S R) L v) : depth J S R request v ≤ L.length := by
  rcases reduced_path J S R request L path with ⟨M, mp, mr, bound⟩
  have eq := rootPath_eq J S R request mp mr
  exact (congrArg List.length eq).le.trans bound

theorem follows_empty_eq {v w : Vertex J S R} {L}
    (path : Follows J S R request v L w) (empty : L = []) : v = w := by
  induction path with
  | nil => rfl
  | cons d tail ih => cases empty

theorem rootPath_empty_iff (v : Vertex J S R) :
    rootPath J S R request v = [] ↔ v = root J S R := by
  constructor
  · intro empty
    exact (follows_empty_eq J S R request (rootPath_follows J S R request v) empty).symm
  · rintro rfl
    exact rootPath_root J S R request

theorem follows_last (pre : List (Dart J S R)) (d : Dart J S R) {v w : Vertex J S R}
    (path : Follows J S R request v (pre ++ [d]) w) :
    Follows J S R request v pre (source J S R request d) ∧ target J S R request d = w := by
  induction pre generalizing v with
  | nil =>
    have start := follows_cons_source J S R request path
    have finish := follows_empty_eq J S R request (follows_tail J S R request path) rfl
    rw [start]
    exact ⟨Follows.nil _, finish⟩
  | cons e pre ih =>
    rcases ih (follows_tail J S R request path) with ⟨first, finish⟩
    refine ⟨?_, finish⟩
    rw [follows_cons_source J S R request path]
    exact Follows.cons e first

theorem exists_parent_edge (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    ∃ d : Dart J S R, target J S R request d = v ∧
      rootPath J S R request v = rootPath J S R request (source J S R request d) ++ [d] ∧
      depth J S R request v = depth J S R request (source J S R request d) + 1 := by
  rcases List.eq_nil_or_concat' (rootPath J S R request v) with empty | ⟨pre, d, eq⟩
  · exact False.elim (nonroot ((rootPath_empty_iff J S R request v).mp empty))
  · have path := rootPath_follows J S R request v
    have reduced := rootPath_reduced J S R request v
    rw [eq] at path reduced
    rcases follows_last J S R request pre d path with ⟨first, finish⟩
    have shorter := rootPath_eq J S R request first
      (EdgeWords.no_backtracking_append_left pre [d] reduced)
    refine ⟨d, finish, ?_, ?_⟩
    · rw [eq, shorter]
    · change (rootPath J S R request v).length =
        (rootPath J S R request (source J S R request d)).length + 1
      rw [eq, shorter, List.length_append]
      rfl

end CosetGeometry.TileStars




open Attachment
universe u v w

structure IdealEmbedding {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B)
    extends MeetEmbedding P Q where
  ideal : ∀ a x, Q.le x (toFun a) → ∃ b, toFun b = x

namespace IdealEmbedding

variable {A : Type u} {B : Type v} {C : Type w}
    {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}

def identity (P : MeetOrder A) : IdealEmbedding P P where
  toMeetEmbedding := (identityIso P).toMeetEmbedding
  ideal _ x _ := ⟨x, rfl⟩

def comp (f : IdealEmbedding P Q) (g : IdealEmbedding Q R) : IdealEmbedding P R where
  toMeetEmbedding := compose f.toMeetEmbedding g.toMeetEmbedding
  ideal a x hx := by
    rcases g.ideal (f.toFun a) x hx with ⟨b, rfl⟩
    rcases f.ideal a b ((g.le_iff _ _).mp hx) with ⟨c, rfl⟩
    exact ⟨c, rfl⟩

def ofOrderMap (f : A → B) (le_iff : ∀ a b, Q.le (f a) (f b) ↔ P.le a b)
    (ideal : ∀ a x, Q.le x (f a) → ∃ b, f b = x) : IdealEmbedding P Q where
  toFun := f
  le_iff := le_iff
  ideal := ideal
  map_meet a b := by
    apply Q.antisymm
    · exact Q.le_meet ((le_iff _ _).mpr (P.meet_le_left a b))
        ((le_iff _ _).mpr (P.meet_le_right a b))
    · rcases ideal a (Q.meet (f a) (f b)) (Q.meet_le_left _ _) with ⟨c, eq⟩
      rw [← eq]
      apply (le_iff _ _).mpr
      apply P.le_meet
      · apply (le_iff _ _).mp
        rw [eq]
        exact Q.meet_le_left _ _
      · apply (le_iff _ _).mp
        rw [eq]
        exact Q.meet_le_right _ _

theorem principal_surjective (f : IdealEmbedding P Q) (a : A)
    (x : {x : B // Q.le x (f.toFun a)}) :
    ∃ y : {y : A // P.le y a}, f.toFun y.val = x.val := by
  rcases f.ideal a x.val x.property with ⟨y, eq⟩
  exact ⟨⟨y, (f.le_iff _ _).mp (eq ▸ x.property)⟩, eq⟩

noncomputable def principalIso (f : IdealEmbedding P Q) (a : A) :
    MeetIso (idealOrder P a) (idealOrder Q (f.toFun a)) where
  toFun x := ⟨f.toFun x.val, (f.le_iff _ _).mpr x.property⟩
  le_iff x y := f.le_iff x.val y.val
  map_meet x y := Subtype.ext (f.map_meet x.val y.val)
  inverse x := Classical.choose (f.principal_surjective a x)
  right_inverse x := Subtype.ext (Classical.choose_spec (f.principal_surjective a x))
  left_inverse x := by
    apply Subtype.ext
    apply embedding_injective f.toMeetEmbedding
    exact Classical.choose_spec (f.principal_surjective a _)

noncomputable def projection (f : IdealEmbedding P Q) (top : A) (x : B) : A :=
  Classical.choose (f.ideal top (Q.meet x (f.toFun top)) (Q.meet_le_right _ _))

theorem projection_spec (f : IdealEmbedding P Q) (top : A) (x : B) :
    f.toFun (f.projection top x) = Q.meet x (f.toFun top) :=
  Classical.choose_spec (f.ideal top (Q.meet x (f.toFun top)) (Q.meet_le_right _ _))

end IdealEmbedding
end



namespace PrincipalBatch

open Attachment
universe u

structure Family {A : Type u} (P : MeetOrder A) (I : Type u) where
  Space : I → Type u
  order : ∀ i, MeetOrder (Space i)
  glue : ∀ i, PrincipalAmalgamation.Input P (order i)

namespace Family

variable {A I : Type u} {P : MeetOrder A} (b : Family P I)

def Fresh := (i : I) × (b.glue i).Fresh
def Node := A ⊕ b.Fresh

def Inside (x y : b.Fresh) : Prop :=
  ∃ h : x.1 = y.1, (b.order x.1).le x.2.val (h.symm ▸ y.2.val)

def data : Data P b.Fresh I where
  component := Sigma.fst
  base i := (b.glue i).leftAnchor
  upper _ _ := False
  upper_up := by intro _ _ _ h _; exact h
  upper_meet := by intro _ _ _ h _; exact h
  base_le_upper := by intro _ _ h; exact False.elim h
  base_not_upper := by intro _ h; exact h
  shadow x := (b.glue x.1).shadow x.2.val
  shadow_le_base x := (b.glue x.1).shadow_le_anchor x.2.val
  inside := b.Inside
  inside_refl x := ⟨rfl, (b.order x.1).refl x.2.val⟩
  inside_trans := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ ⟨hij, hxy⟩ ⟨hjk, hyz⟩
    cases hij
    cases hjk
    exact ⟨rfl, (b.order i).trans hxy hyz⟩
  inside_antisymm := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hij, hxy⟩ ⟨hji, hyx⟩
    cases hij
    cases hji
    exact congrArg (Sigma.mk i) (Subtype.ext ((b.order i).antisymm hxy hyx))
  inside_component h := h.choose
  inside_shadow := by
    rintro ⟨i, x⟩ ⟨j, y⟩ ⟨hij, hxy⟩
    cases hij
    exact (b.glue i).shadow_mono hxy

theorem component_meets : ComponentMeets b.data := by
  classical
  rintro ⟨i, x⟩ ⟨j, z⟩ same
  change i = j at same
  cases same
  by_cases old : (b.order i).le ((b.order i).meet x.val z.val) (b.glue i).rightAnchor
  · apply Or.inr
    rintro ⟨k, y⟩ ⟨hki, hyx⟩ ⟨hki', hyz⟩
    cases hki
    cases hki'
    exact y.property ((b.order i).trans ((b.order i).le_meet hyx hyz) old)
  · refine Or.inl ⟨⟨i, ⟨(b.order i).meet x.val z.val, old⟩⟩,
      ⟨rfl, (b.order i).meet_le_left _ _⟩, ⟨rfl, (b.order i).meet_le_right _ _⟩, ?_, ?_⟩
    · rintro ⟨k, y⟩ ⟨hki, hyx⟩ ⟨hki', hyz⟩
      cases hki
      cases hki'
      exact ⟨rfl, (b.order i).le_meet hyx hyz⟩
    · exact (b.glue i).shadow_meet x.val z.val

noncomputable def extension : MeetOrder b.Node := meetOrder b.data b.component_meets

noncomputable def old : IdealEmbedding P b.extension where
  toMeetEmbedding := oldEmbedding b.data b.component_meets
  ideal a x hx := by
    cases x with
    | inl x => exact ⟨x, rfl⟩
    | inr x => exact False.elim hx

def componentMap (i : I) : (b.glue i).Node → b.Node
  | .inl a => .inl a
  | .inr x => .inr ⟨i, x⟩

theorem componentMap_le (i : I) (x y : (b.glue i).Node) :
    b.extension.le (b.componentMap i x) (b.componentMap i y) ↔ (b.glue i).order.le x y := by
  cases x with
  | inl a => cases y <;> exact Iff.rfl
  | inr x =>
    cases y with
    | inl a => exact Iff.rfl
    | inr y =>
      change (b.Inside ⟨i, x⟩ ⟨i, y⟩ ∨ False) ↔ ((b.order i).le x.val y.val ∨ False)
      constructor
      · rintro (⟨h, lower⟩ | impossible)
        · cases h
          exact Or.inl lower
        · exact False.elim impossible
      · rintro (lower | impossible)
        · exact Or.inl ⟨rfl, lower⟩
        · exact False.elim impossible

theorem componentMap_ideal (i : I) (a : (b.glue i).Node) (x : b.Node)
    (lower : b.extension.le x (b.componentMap i a)) :
    ∃ y, b.componentMap i y = x := by
  cases x with
  | inl x => exact ⟨.inl x, rfl⟩
  | inr x =>
    cases a with
    | inl a => exact False.elim lower
    | inr a =>
      rcases lower with h | impossible
      · rcases x with ⟨j, x⟩
        rcases h with ⟨eq, _⟩
        cases eq
        exact ⟨.inr x, rfl⟩
      · exact False.elim impossible

noncomputable def component (i : I) : IdealEmbedding (b.glue i).order b.extension :=
  IdealEmbedding.ofOrderMap (b.componentMap i) (b.componentMap_le i) (b.componentMap_ideal i)

noncomputable def tile (i : I) : IdealEmbedding (b.order i) b.extension :=
  IdealEmbedding.comp
    { toMeetEmbedding := (b.glue i).right, ideal := (b.glue i).right_ideal }
    (b.component i)

theorem tile_old_overlap (i : I) (x : b.Space i) (a : A) :
    (b.tile i).toFun x = b.old.toFun a ↔
      ∃ h : (b.order i).le x (b.glue i).rightAnchor,
        ((b.glue i).overlap.toFun ⟨x, h⟩).val = a := by
  change b.componentMap i ((b.glue i).right.toFun x) = b.componentMap i (.inl a) ↔ _
  exact (Iff.intro (fun h => embedding_injective (b.component i).toMeetEmbedding h)
    (congrArg (b.componentMap i))).trans ((b.glue i).overlap_exact a x)

theorem cover (x : b.Node) :
    (∃ a, b.old.toFun a = x) ∨ ∃ i y, (b.tile i).toFun y = x := by
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr x =>
    refine Or.inr ⟨x.1, x.2.val, ?_⟩
    exact congrArg (b.componentMap x.1) ((b.glue x.1).represent_new x.2.val x.2.property)

end Family
end PrincipalBatch

end PartitionPilot.Compression.RecursiveMaps

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IdealChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u

structure IdealChain where
  Point : Nat → Type u
  order : ∀ n, MeetOrder (Point n)
  next : ∀ n, IdealEmbedding (order n) (order (n + 1))

namespace IdealChain
variable (c : IdealChain.{u})

noncomputable def up {n m : Nat} (h : n ≤ m) (x : c.Point n) : c.Point m :=
  Nat.leRecOn h (fun {k} x => (c.next k).toFun x) x

theorem up_self (n : Nat) (x : c.Point n) : c.up (Nat.le_refl n) x = x :=
  Nat.leRecOn_self x

theorem up_succ {n m : Nat} (h : n ≤ m) (x : c.Point n) :
    c.up (Nat.le_succ_of_le h) x = (c.next m).toFun (c.up h x) :=
  Nat.leRecOn_succ h x

theorem up_comp {n m k : Nat} (hnm : n ≤ m) (hmk : m ≤ k) (x : c.Point n) :
    c.up (Nat.le_trans hnm hmk) x = c.up hmk (c.up hnm x) :=
  Nat.leRecOn_trans hnm hmk x

theorem up_le {n m : Nat} (h : n ≤ m) (x y : c.Point n) :
    (c.order m).le (c.up h x) (c.up h y) ↔ (c.order n).le x y := by
  induction h with
  | refl => rw [c.up_self, c.up_self]
  | @step m h ih => rw [c.up_succ h, c.up_succ h, (c.next m).le_iff, ih]

theorem up_ideal {n m : Nat} (h : n ≤ m) (a : c.Point n) (x : c.Point m)
    (lower : (c.order m).le x (c.up h a)) : ∃ b, c.up h b = x := by
  induction h with
  | refl => exact ⟨x, c.up_self _ _⟩
  | @step m h ih =>
    rw [c.up_succ h] at lower
    rcases (c.next m).ideal (c.up h a) x lower with ⟨y, rfl⟩
    rcases ih y (((c.next m).le_iff _ _).mp lower) with ⟨b, eq⟩
    exact ⟨b, by rw [c.up_succ h, eq]⟩

noncomputable def raise {n m : Nat} (h : n ≤ m) : IdealEmbedding (c.order n) (c.order m) :=
  IdealEmbedding.ofOrderMap (c.up h) (c.up_le h) (c.up_ideal h)

def Label := (n : Nat) × c.Point n

def Related (x y : c.Label) : Prop :=
  ∃ (k : Nat) (hx : x.1 ≤ k) (hy : y.1 ≤ k), c.up hx x.2 = c.up hy y.2

theorem related_refl (x : c.Label) : c.Related x x := ⟨x.1, _root_.le_refl _, _root_.le_refl _, rfl⟩

theorem related_symm {x y : c.Label} (h : c.Related x y) : c.Related y x := by
  rcases h with ⟨k, hx, hy, eq⟩
  exact ⟨k, hy, hx, eq.symm⟩

theorem related_trans {x y z : c.Label} (hxy : c.Related x y) (hyz : c.Related y z) :
    c.Related x z := by
  rcases hxy with ⟨k, hx, hy, eq1⟩
  rcases hyz with ⟨l, hy', hz, eq2⟩
  refine ⟨max k l, _root_.le_trans hx (Nat.le_max_left _ _), _root_.le_trans hz (Nat.le_max_right _ _), ?_⟩
  calc
    c.up _ x.2 = c.up (Nat.le_max_left k l) (c.up hx x.2) := c.up_comp _ _ _
    _ = c.up (Nat.le_max_left k l) (c.up hy y.2) := congrArg _ eq1
    _ = c.up (Nat.le_max_right k l) (c.up hy' y.2) :=
      (c.up_comp _ _ _).symm.trans (c.up_comp _ _ _)
    _ = c.up (Nat.le_max_right k l) (c.up hz z.2) := congrArg _ eq2
    _ = c.up _ z.2 := (c.up_comp _ _ _).symm

def setoid : Setoid c.Label := ⟨c.Related, c.related_refl, c.related_symm, c.related_trans⟩
def Union := Quotient c.setoid
def point (n : Nat) (x : c.Point n) : c.Union := Quotient.mk c.setoid ⟨n, x⟩

theorem include_up {n m : Nat} (h : n ≤ m) (x : c.Point n) :
    c.point m (c.up h x) = c.point n x := by
  apply Quotient.sound
  exact ⟨m, _root_.le_refl _, h, c.up_self _ _⟩

theorem include_injective (n : Nat) : Function.Injective (c.point n) := by
  intro x y eq
  rcases Quotient.exact eq with ⟨k, hx, hy, same⟩
  exact embedding_injective (c.raise hx).toMeetEmbedding same

theorem cover (x : c.Union) : ∃ n a, c.point n a = x := by
  induction x using Quotient.ind with
  | _ x => exact ⟨x.1, x.2, rfl⟩

theorem pair_cover (x y : c.Union) :
    ∃ n a b, c.point n a = x ∧ c.point n b = y := by
  rcases c.cover x with ⟨n, a, rfl⟩
  rcases c.cover y with ⟨m, b, rfl⟩
  exact ⟨max n m, c.up (Nat.le_max_left _ _) a, c.up (Nat.le_max_right _ _) b,
    c.include_up _ _, c.include_up _ _⟩

def Le (x y : c.Union) : Prop :=
  ∃ n a b, c.point n a = x ∧ c.point n b = y ∧ (c.order n).le a b

theorem le_stage (n : Nat) (a b : c.Point n) :
    c.Le (c.point n a) (c.point n b) ↔ (c.order n).le a b := by
  constructor
  · rintro ⟨m, x, y, hx, hy, lower⟩
    let k := max n m
    have ex : c.up (Nat.le_max_right n m) x = c.up (Nat.le_max_left n m) a := by
      apply c.include_injective k
      rw [c.include_up, c.include_up]
      exact hx
    have ey : c.up (Nat.le_max_right n m) y = c.up (Nat.le_max_left n m) b := by
      apply c.include_injective k
      rw [c.include_up, c.include_up]
      exact hy
    have lifted := (c.up_le (Nat.le_max_right n m) x y).mpr lower
    rw [ex, ey] at lifted
    exact (c.up_le (Nat.le_max_left n m) a b).mp lifted
  · intro h
    exact ⟨n, a, b, rfl, rfl, h⟩

theorem le_refl (x : c.Union) : c.Le x x := by
  rcases c.cover x with ⟨n, a, rfl⟩
  exact (c.le_stage n a a).mpr ((c.order n).refl a)

theorem le_trans {x y z : c.Union} (hxy : c.Le x y) (hyz : c.Le y z) : c.Le x z := by
  rcases hxy with ⟨n, a, b, ha, hb, lower1⟩
  rcases hyz with ⟨m, d, e, hd, he, lower2⟩
  have middle : c.up (Nat.le_max_left n m) b = c.up (Nat.le_max_right n m) d := by
    apply c.include_injective (max n m)
    rw [c.include_up, c.include_up]
    exact hb.trans hd.symm
  have left := (c.up_le (Nat.le_max_left n m) a b).mpr lower1
  rw [middle] at left
  exact ⟨max n m, _, _, (c.include_up _ _).trans ha, (c.include_up _ _).trans he,
    (c.order _).trans left ((c.up_le (Nat.le_max_right n m) d e).mpr lower2)⟩

theorem le_antisymm {x y : c.Union} (hxy : c.Le x y) (hyx : c.Le y x) : x = y := by
  rcases c.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  exact congrArg (c.point n) ((c.order n).antisymm
    ((c.le_stage _ _ _).mp hxy) ((c.le_stage _ _ _).mp hyx))

theorem include_ideal (n : Nat) (a : c.Point n) (x : c.Union) (lower : c.Le x (c.point n a)) :
    ∃ b, c.point n b = x := by
  rcases c.cover x with ⟨m, b, rfl⟩
  have lifted : c.Le (c.point (max n m) (c.up (Nat.le_max_right n m) b))
      (c.point (max n m) (c.up (Nat.le_max_left n m) a)) := by
    rw [c.include_up, c.include_up]
    exact lower
  rcases c.up_ideal (Nat.le_max_left n m) a _ ((c.le_stage _ _ _).mp lifted) with ⟨d, eq⟩
  refine ⟨d, ?_⟩
  rw [← c.include_up (Nat.le_max_left n m) d, eq, c.include_up]

theorem stage_meet_spec (n : Nat) (a b : c.Point n) :
    c.Le (c.point n ((c.order n).meet a b)) (c.point n a) ∧
    c.Le (c.point n ((c.order n).meet a b)) (c.point n b) ∧
    ∀ z, c.Le z (c.point n a) → c.Le z (c.point n b) →
      c.Le z (c.point n ((c.order n).meet a b)) := by
  refine ⟨(c.le_stage _ _ _).mpr ((c.order n).meet_le_left a b),
    (c.le_stage _ _ _).mpr ((c.order n).meet_le_right a b), ?_⟩
  intro z hza hzb
  rcases c.include_ideal n a z hza with ⟨d, rfl⟩
  exact (c.le_stage _ _ _).mpr ((c.order n).le_meet
    ((c.le_stage _ _ _).mp hza) ((c.le_stage _ _ _).mp hzb))

theorem meets_exist (x y : c.Union) :
    ∃ m, c.Le m x ∧ c.Le m y ∧ ∀ z, c.Le z x → c.Le z y → c.Le z m := by
  rcases c.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
  exact ⟨c.point n ((c.order n).meet a b), c.stage_meet_spec n a b⟩

noncomputable def unionOrder : MeetOrder c.Union where
  le := c.Le
  meet x y := Classical.choose (c.meets_exist x y)
  refl := c.le_refl
  trans := c.le_trans
  antisymm := c.le_antisymm
  meet_le_left x y := (Classical.choose_spec (c.meets_exist x y)).1
  meet_le_right x y := (Classical.choose_spec (c.meets_exist x y)).2.1
  le_meet {z x y} := (Classical.choose_spec (c.meets_exist x y)).2.2 z

noncomputable def inclusion (n : Nat) : IdealEmbedding (c.order n) c.unionOrder :=
  IdealEmbedding.ofOrderMap (c.point n) (c.le_stage n) (c.include_ideal n)

end IdealChain
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TileTreeGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace RootedGluing

open Attachment
universe u

def chainIso {A B C : Type u} {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}
    (f : MeetIso P Q) (g : MeetIso Q R) : MeetIso P R where
  toMeetEmbedding := compose f.toMeetEmbedding g.toMeetEmbedding
  inverse x := f.inverse (g.inverse x)
  left_inverse x := by
    change f.inverse (g.inverse (g.toFun (f.toFun x))) = x
    rw [g.left_inverse, f.left_inverse]
  right_inverse x := by
    change g.toFun (f.toFun (f.inverse (g.inverse x))) = x
    rw [f.right_inverse, g.right_inverse]

structure Scheme (V : Type u) where
  root : V
  depth : V → Nat
  depth_root : depth root = 0
  zero_eq_root : ∀ v, depth v = 0 → v = root
  parent : V → V
  parent_depth : ∀ v, depth v ≠ 0 → depth (parent v) + 1 = depth v
  Space : V → Type u
  order : ∀ v, MeetOrder (Space v)
  childAnchor : ∀ v, depth v ≠ 0 → Space v
  parentAnchor : ∀ v, depth v ≠ 0 → Space (parent v)
  link : ∀ v h, MeetIso (idealOrder (order v) (childAnchor v h))
    (idealOrder (order (parent v)) (parentAnchor v h))

namespace Scheme
variable {V : Type u} (d : Scheme V)

structure Stage (n : Nat) where
  Point : Type u
  order : MeetOrder Point
  vertex : ∀ v, d.depth v ≤ n → IdealEmbedding (d.order v) order

noncomputable def initial : d.Stage 0 where
  Point := d.Space d.root
  order := d.order d.root
  vertex v hv := by
    have eq := d.zero_eq_root v (Nat.eq_zero_of_le_zero hv)
    subst v
    exact IdealEmbedding.identity _

namespace Stage
variable {d} {n : Nat} (s : d.Stage n)

def Layer (_s : d.Stage n) := {v : V // d.depth v = n + 1}

theorem layer_nonzero (v : s.Layer) : d.depth v.val ≠ 0 := by
  rw [v.property]
  exact Nat.succ_ne_zero n

theorem parent_present (v : s.Layer) : d.depth (d.parent v.val) ≤ n := by
  have h := d.parent_depth v.val (s.layer_nonzero v)
  rw [v.property] at h
  omega

noncomputable def batch : PrincipalBatch.Family s.order s.Layer where
  Space v := d.Space v.val
  order v := d.order v.val
  glue v := {
    leftAnchor := (s.vertex (d.parent v.val) (s.parent_present v)).toFun
      (d.parentAnchor v.val (s.layer_nonzero v))
    rightAnchor := d.childAnchor v.val (s.layer_nonzero v)
    overlap := chainIso (d.link v.val (s.layer_nonzero v))
      ((s.vertex (d.parent v.val) (s.parent_present v)).principalIso
        (d.parentAnchor v.val (s.layer_nonzero v))) }

noncomputable def successor : d.Stage (n + 1) := by
  classical
  exact {
    Point := s.batch.Node
    order := s.batch.extension
    vertex := fun v hv =>
      if old : d.depth v ≤ n then (s.vertex v old).comp s.batch.old
      else s.batch.tile ⟨v, by omega⟩ }

theorem successor_old (v : V) (hv : d.depth v ≤ n) (x : d.Space v) :
    (s.successor.vertex v (Nat.le_succ_of_le hv)).toFun x =
      s.batch.old.toFun ((s.vertex v hv).toFun x) := by
  dsimp only [successor]
  erw [dite_eq_left hv]
  rfl

theorem successor_new (v : s.Layer) (x : d.Space v.val) :
    (s.successor.vertex v.val v.property.le).toFun x = (s.batch.tile v).toFun x := by
  have fresh : ¬ d.depth v.val ≤ n := by rw [v.property]; omega
  dsimp only [successor]
  erw [dite_eq_right fresh]
  rfl

end Stage

noncomputable def stages : (n : Nat) → d.Stage n
  | 0 => d.initial
  | n + 1 => (stages n).successor

noncomputable def chain : IdealChain where
  Point n := (d.stages n).Point
  order n := (d.stages n).order
  next n := (d.stages n).batch.old

theorem vertex_coherent {n m : Nat} (hnm : n ≤ m) (v : V) (hv : d.depth v ≤ n) (x : d.Space v) :
    d.chain.up hnm ((d.stages n).vertex v hv |>.toFun x) =
      ((d.stages m).vertex v (Nat.le_trans hv hnm)).toFun x := by
  induction hnm with
  | refl => exact d.chain.up_self _ _
  | @step m h ih =>
    erw [d.chain.up_succ h, ih]
    exact ((d.stages m).successor_old v (le_trans hv h) x).symm

def Node := d.chain.Union
noncomputable def gluedOrder : MeetOrder d.Node := d.chain.unionOrder

noncomputable def vertex (v : V) : IdealEmbedding (d.order v) d.gluedOrder :=
  ((d.stages (d.depth v)).vertex v (le_refl _)).comp (d.chain.inclusion (d.depth v))

theorem vertex_at (v : V) (n : Nat) (hv : d.depth v ≤ n) (x : d.Space v) :
    (d.vertex v).toFun x = d.chain.point n (((d.stages n).vertex v hv).toFun x) := by
  change d.chain.point (d.depth v) (((d.stages (d.depth v)).vertex v (le_refl _)).toFun x) = _
  erw [← d.chain.include_up hv, d.vertex_coherent hv]

end Scheme
end RootedGluing



namespace RootedGluing.Scheme

open Attachment
universe u
variable {V : Type u} (d : Scheme V)

theorem stage_cover (n : Nat) (x : (d.stages n).Point) :
    ∃ (v : V) (hv : d.depth v ≤ n) (a : d.Space v), ((d.stages n).vertex v hv).toFun a = x := by
  induction n with
  | zero => exact ⟨d.root, d.depth_root.le, x, rfl⟩
  | succ n ih =>
    rcases (d.stages n).batch.cover x with ⟨a, rfl⟩ | ⟨v, a, rfl⟩
    · rcases ih a with ⟨v, hv, b, eq⟩
      refine ⟨v, Nat.le_succ_of_le hv, b, ?_⟩
      exact ((d.stages n).successor_old v hv b).trans (congrArg _ eq)
    · exact ⟨v.val, v.property.le, a, (d.stages n).successor_new v a⟩

theorem cover (x : d.Node) : ∃ v a, (d.vertex v).toFun a = x := by
  rcases d.chain.cover x with ⟨n, a, rfl⟩
  rcases d.stage_cover n a with ⟨v, hv, b, eq⟩
  exact ⟨v, b, (d.vertex_at v n hv b).trans (congrArg _ eq)⟩

theorem point_next (n : Nat) (x : (d.stages n).Point) :
    d.chain.point (n + 1) ((d.stages n).batch.old.toFun x) = d.chain.point n x := by
  have eq := d.chain.include_up (Nat.le_succ n) x
  erw [d.chain.up_succ (Nat.le_refl n), d.chain.up_self] at eq
  exact eq

theorem parent_identification (v : V) (h : d.depth v ≠ 0)
    (x : {x : d.Space v // (d.order v).le x (d.childAnchor v h)}) :
    (d.vertex v).toFun x.val = (d.vertex (d.parent v)).toFun ((d.link v h).toFun x).val := by
  let n := d.depth (d.parent v)
  let s := d.stages n
  let i : s.Layer := ⟨v, (d.parent_depth v h).symm⟩
  have base : (s.batch.tile i).toFun x.val =
      s.batch.old.toFun ((s.vertex (d.parent v) (s.parent_present i)).toFun ((d.link v h).toFun x).val) := by
    apply (s.batch.tile_old_overlap i x.val _).mpr
    exact ⟨x.property, rfl⟩
  exact (d.vertex_at v (n + 1) i.property.le x.val).trans
    ((congrArg (d.chain.point (n + 1)) (s.successor_new i x.val)).trans
      ((congrArg (d.chain.point (n + 1)) base).trans
        ((d.point_next n _).trans (d.vertex_at (d.parent v) n (s.parent_present i) _).symm)))

end RootedGluing.Scheme



section

namespace EdgeWords
universe u
variable {E : Type u}

theorem append_reduced_or_cancelled (L : List (E × Bool)) (d : E × Bool)
    (h : NoBacktracking L) :
    NoBacktracking (L ++ [d]) ∨ ∃ pre, L = pre ++ [reverse d] := by
  classical
  induction L with
  | nil => exact Or.inl True.intro
  | cons a tail ih =>
    cases tail with
    | nil =>
      by_cases back : d = reverse a
      · refine Or.inr ⟨[], ?_⟩
        have twice : reverse (reverse a) = a := by
          rcases a with ⟨e, b⟩
          cases b <;> rfl
        rw [back, twice]
        rfl
      · exact Or.inl ⟨back, True.intro⟩
    | cons b tail =>
      rcases ih h.2 with reduced | ⟨pre, eq⟩
      · exact Or.inl ⟨h.1, reduced⟩
      · exact Or.inr ⟨a :: pre, congrArg (List.cons a) eq⟩

end EdgeWords

namespace CosetGeometry.TileStars
universe u
variable (J S R : Type u) [Group J] (request : S → R)

theorem depth_zero_iff (v : Vertex J S R) : depth J S R request v = 0 ↔ v = root J S R := by
  simp only [depth, List.length_eq_zero_iff, rootPath_empty_iff]

theorem edge_root_paths (d : Dart J S R) :
    rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d] ∨
    rootPath J S R request (source J S R request d) =
      rootPath J S R request (target J S R request d) ++ [reverse J S R d] := by
  have first := rootPath_follows J S R request (source J S R request d)
  have reduced := rootPath_reduced J S R request (source J S R request d)
  rcases EdgeWords.append_reduced_or_cancelled _ d reduced with forward | ⟨pre, eq⟩
  · apply Or.inl
    exact rootPath_eq J S R request
      (follows_append J S R request first (Follows.cons d (Follows.nil _))) forward
  · rw [eq] at first reduced
    have prefixPath := (follows_last J S R request pre (reverse J S R d) first).1
    rw [source_reverse] at prefixPath
    have canonical := rootPath_eq J S R request prefixPath
      (EdgeWords.no_backtracking_append_left pre _ reduced)
    exact Or.inr (eq.trans (congrArg (fun L => L ++ [reverse J S R d]) canonical.symm))

noncomputable def incoming (v : Vertex J S R) (nonroot : v ≠ root J S R) : Dart J S R :=
  Classical.choose (exists_parent_edge J S R request v nonroot)

theorem incoming_target (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    target J S R request (incoming J S R request v nonroot) = v :=
  (Classical.choose_spec (exists_parent_edge J S R request v nonroot)).1

theorem incoming_path (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    rootPath J S R request v =
      rootPath J S R request (source J S R request (incoming J S R request v nonroot)) ++
        [incoming J S R request v nonroot] :=
  (Classical.choose_spec (exists_parent_edge J S R request v nonroot)).2.1

noncomputable def parent (v : Vertex J S R) : Vertex J S R := by
  classical
  exact if h : v = root J S R then root J S R else
    source J S R request (incoming J S R request v h)

theorem parent_eq (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    parent J S R request v = source J S R request (incoming J S R request v nonroot) := by
  simp only [parent, dite_eq_right nonroot]

theorem parent_depth (v : Vertex J S R) (nonzero : depth J S R request v ≠ 0) :
    depth J S R request (parent J S R request v) + 1 = depth J S R request v := by
  have nonroot : v ≠ root J S R := fun h => nonzero ((depth_zero_iff J S R request v).mpr h)
  rw [parent_eq J S R request v nonroot]
  exact (Classical.choose_spec (exists_parent_edge J S R request v nonroot)).2.2.symm

theorem extension_nonroot (d : Dart J S R)
    (eq : rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d]) :
    target J S R request d ≠ root J S R := by
  intro h
  rw [h, rootPath_root] at eq
  have lengths := congrArg List.length eq
  simp only [List.length_nil, List.length_append, List.length_cons] at lengths
  omega

theorem incoming_of_extension (d : Dart J S R)
    (eq : rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d]) :
    incoming J S R request (target J S R request d)
      (extension_nonroot J S R request d eq) = d := by
  have other := incoming_path J S R request (target J S R request d)
    (extension_nonroot J S R request d eq)
  have lasts := congrArg List.getLast? (other.symm.trans eq)
  simpa only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.some.injEq] using lasts

end CosetGeometry.TileStars
end



namespace CosetGeometry.TileStars

open Attachment
universe u
variable (J S R : Type u) [Group J] (request : S → R)

structure Spaces where
  Space : Vertex J S R → Type u
  order : ∀ v, MeetOrder (Space v)
  leftAnchor : ∀ e : Edge J S R, Space (source J S R request (e, true))
  rightAnchor : ∀ e : Edge J S R, Space (target J S R request (e, true))
  overlap : ∀ e, MeetIso
    (idealOrder (order (source J S R request (e, true))) (leftAnchor e))
    (idealOrder (order (target J S R request (e, true))) (rightAnchor e))

namespace Spaces
variable {J S R request} (g : Spaces J S R request)

def anchor (d : Dart J S R) : g.Space (source J S R request d) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact g.rightAnchor e
  · exact g.leftAnchor e

def arrow (d : Dart J S R) : MeetIso
    (idealOrder (g.order (source J S R request d)) (g.anchor d))
    (idealOrder (g.order (target J S R request d)) (g.anchor (reverse J S R d))) := by
  rcases d with ⟨e, b⟩
  cases b
  · exact inverseIso (g.overlap e)
  · exact g.overlap e

def edgeInput (d : Dart J S R) : PrincipalAmalgamation.Input
    (g.order (source J S R request d)) (g.order (target J S R request d)) where
  leftAnchor := g.anchor d
  rightAnchor := g.anchor (reverse J S R d)
  overlap := inverseIso (g.arrow d)

def reindexInput {v w v' w' : Vertex J S R} (hv : v = v') (hw : w = w')
    (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) :
    PrincipalAmalgamation.Input (g.order v') (g.order w') := hv ▸ hw ▸ i

noncomputable def localGlue (v : Vertex J S R) (nonzero : depth J S R request v ≠ 0) :
    PrincipalAmalgamation.Input (g.order (parent J S R request v)) (g.order v) := by
  have nonroot : v ≠ root J S R := fun h => nonzero ((depth_zero_iff J S R request v).mpr h)
  exact g.reindexInput (parent_eq J S R request v nonroot).symm
    (incoming_target J S R request v nonroot) (g.edgeInput (incoming J S R request v nonroot))

noncomputable def scheme : RootedGluing.Scheme (Vertex J S R) where
  root := root J S R
  depth := depth J S R request
  depth_root := (depth_zero_iff J S R request _).mpr rfl
  zero_eq_root v := (depth_zero_iff J S R request v).mp
  parent := parent J S R request
  parent_depth := parent_depth J S R request
  Space := g.Space
  order := g.order
  childAnchor v h := (g.localGlue v h).rightAnchor
  parentAnchor v h := (g.localGlue v h).leftAnchor
  link v h := (g.localGlue v h).overlap

def Node := g.scheme.Node
noncomputable def gluedOrder : MeetOrder g.Node := g.scheme.gluedOrder
noncomputable def vertex (v : Vertex J S R) : IdealEmbedding (g.order v) g.gluedOrder :=
  g.scheme.vertex v

theorem parent_identification (v : Vertex J S R) (h : depth J S R request v ≠ 0)
    (x : {x : g.Space v // (g.order v).le x (g.localGlue v h).rightAnchor}) :
    (g.vertex v).toFun x.val =
      (g.vertex (parent J S R request v)).toFun ((g.localGlue v h).overlap.toFun x).val :=
  g.scheme.parent_identification v h x

theorem cover (z : g.Node) : ∃ v x, (g.vertex v).toFun x = z := g.scheme.cover z

end Spaces
end CosetGeometry.TileStars

end PartitionPilot.Compression.RecursiveMaps

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_RootedGluingQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

universe u
variable {V : Type u} (d : Scheme V)

def Label := (v : V) × d.Space v

inductive Related : d.Label → d.Label → Prop
  | parent (v : V) (h : d.depth v ≠ 0)
      (x : {x : d.Space v // (d.order v).le x (d.childAnchor v h)}) :
      Related ⟨v, x.val⟩ ⟨d.parent v, ((d.link v h).toFun x).val⟩
  | refl (x) : Related x x
  | symm {x y} : Related x y → Related y x
  | trans {x y z} : Related x y → Related y z → Related x z

def labelSetoid : Setoid d.Label := ⟨d.Related, Related.refl, Related.symm, Related.trans⟩
def Generated := Quotient d.labelSetoid
def labelClass (v : V) (x : d.Space v) : d.Generated := Quotient.mk d.labelSetoid ⟨v, x⟩

theorem label_parent (v : V) (h : d.depth v ≠ 0)
    (x : {x : d.Space v // (d.order v).le x (d.childAnchor v h)}) :
    d.labelClass v x.val = d.labelClass (d.parent v) ((d.link v h).toFun x).val :=
  Quotient.sound (Related.parent v h x)

noncomputable def stageClass : (n : Nat) → (d.stages n).Point → d.Generated
  | 0, x => d.labelClass d.root x
  | n + 1, .inl x => stageClass n x
  | _ + 1, .inr x => d.labelClass x.1.val x.2.val

theorem stageClass_old (n : Nat) (x : (d.stages n).Point) :
    d.stageClass (n + 1) ((d.stages n).batch.old.toFun x) = d.stageClass n x := rfl

theorem stageClass_vertex (n : Nat) (v : V) (hv : d.depth v ≤ n) (x : d.Space v) :
    d.stageClass n (((d.stages n).vertex v hv).toFun x) = d.labelClass v x := by
  classical
  induction n generalizing v with
  | zero =>
    have eq := d.zero_eq_root v (Nat.eq_zero_of_le_zero hv)
    subst v
    rfl
  | succ n ih =>
    change d.stageClass (n + 1) (((d.stages n).successor.vertex v hv).toFun x) = _
    by_cases older : d.depth v ≤ n
    · rw [(d.stages n).successor_old v older x, d.stageClass_old]
      exact ih v older x
    · let s := d.stages n
      let i : s.Layer := ⟨v, by omega⟩
      rw [s.successor_new i x]
      by_cases base : (d.order v).le x (d.childAnchor v (s.layer_nonzero i))
      · have eq : (s.batch.tile i).toFun x =
            s.batch.old.toFun ((s.vertex (d.parent v) (s.parent_present i)).toFun
              ((d.link v (s.layer_nonzero i)).toFun ⟨x, base⟩).val) :=
          (s.batch.tile_old_overlap i x _).mpr ⟨base, rfl⟩
        rw [eq, d.stageClass_old]
        exact (ih (d.parent v) (s.parent_present i) _).trans
          (d.label_parent v (s.layer_nonzero i) ⟨x, base⟩).symm
      · have represented := (s.batch.glue i).represent_new x base
        change d.stageClass (n + 1) (s.batch.componentMap i ((s.batch.glue i).represent x)) = _
        rw [represented]
        rfl

theorem stageClass_up {n m : Nat} (h : n ≤ m) (x : (d.stages n).Point) :
    d.stageClass m (d.chain.up h x) = d.stageClass n x := by
  induction h with
  | refl => erw [d.chain.up_self]
  | @step m h ih =>
    erw [d.chain.up_succ h]
    exact (d.stageClass_old m _).trans ih

noncomputable def toGenerated : d.Node → d.Generated :=
  Quotient.lift (fun x => d.stageClass x.1 x.2) (by
    rintro x y ⟨k, hx, hy, eq⟩
    exact (d.stageClass_up hx x.2).symm.trans
      ((congrArg (d.stageClass k) eq).trans (d.stageClass_up hy y.2)))

theorem toGenerated_vertex (v : V) (x : d.Space v) :
    d.toGenerated ((d.vertex v).toFun x) = d.labelClass v x :=
  d.stageClass_vertex (d.depth v) v (le_refl _) x

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GluingHeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot

namespace Compression.RecursiveMaps.CosetGeometry

universe u
variable (J S : Type u) [Group J]

theorem representative_exists (v : Vertex J S) : ∃ w, point J S w = v := by
  induction v using Quotient.ind with
  | _ w => exact ⟨w, rfl⟩

noncomputable def representative (v : Vertex J S) : External J S := by
  classical
  exact if v = root J S then 1 else Classical.choose (representative_exists J S v)

theorem representative_spec (v : Vertex J S) : point J S (representative J S v) = v := by
  classical
  by_cases h : v = root J S
  · subst v
    simp only [representative]
    rfl
  · simp only [representative, ite_eq_right h]
    exact Classical.choose_spec (representative_exists J S v)

theorem representative_root : representative J S (root J S) = 1 := by
  simp [representative]

theorem coordinate_exists (w : External J S) :
    ∃ j, representative J S (point J S w) * old J S j = w :=
  (point_eq J S _ w).mp (representative_spec J S (point J S w))

noncomputable def coordinate (w : External J S) : J := Classical.choose (coordinate_exists J S w)

theorem coordinate_spec (w : External J S) :
    representative J S (point J S w) * old J S (coordinate J S w) = w :=
  Classical.choose_spec (coordinate_exists J S w)

theorem coordinate_unique (w : External J S) (j : J)
    (eq : representative J S (point J S w) * old J S j = w) : coordinate J S w = j :=
  old_injective J S (mul_left_cancel ((coordinate_spec J S w).trans eq.symm))

theorem point_mul_old (w : External J S) (j : J) : point J S (w * old J S j) = point J S w :=
  ((point_eq J S w (w * old J S j)).mpr ⟨j, rfl⟩).symm

theorem coordinate_mul_old (w : External J S) (j : J) :
    coordinate J S (w * old J S j) = coordinate J S w * j := by
  apply coordinate_unique J S
  rw [point_mul_old, map_mul, ← mul_assoc, coordinate_spec]

theorem coordinate_one : coordinate J S 1 = 1 := by
  apply coordinate_unique J S
  change representative J S (root J S) * old J S 1 = 1
  rw [representative_root, map_one, mul_one]

structure OrderAction {A : Type u} (P : MeetOrder A) where
  iso : J → MeetIso P P
  one : ∀ x, (iso 1).toFun x = x
  mul : ∀ g h x, (iso (g * h)).toFun x = (iso g).toFun ((iso h).toFun x)

namespace OrderAction
variable {J S} {A : Type u} {P : MeetOrder A} (a : OrderAction J P)

noncomputable def chart (w : External J S) : MeetIso P P := a.iso (coordinate J S w)

theorem chart_one (x : A) : (a.chart (S := S) 1).toFun x = x := by
  change (a.iso (coordinate J S 1)).toFun x = x
  rw [coordinate_one, a.one]

theorem chart_mul_old (w : External J S) (j : J) (x : A) :
    (a.chart (w * old J S j)).toFun x = (a.chart w).toFun ((a.iso j).toFun x) := by
  change (a.iso (coordinate J S (w * old J S j))).toFun x = _
  rw [coordinate_mul_old, a.mul]
  rfl

def ideal (j : J) : IdealEmbedding P P where
  toMeetEmbedding := (a.iso j).toMeetEmbedding
  ideal _ x _ := ⟨(a.iso j).inverse x, (a.iso j).right_inverse x⟩

end OrderAction

end Compression.RecursiveMaps.CosetGeometry



namespace Compression.RecursiveMaps.TileRequests

open Attachment
universe u
variable {A : Type u} (P : MeetOrder A)

structure Tile (Child : Type u) where
  Space : Type u
  order : MeetOrder Space
  root : IdealEmbedding P order
  child : Child → IdealEmbedding P order
  cover : ∀ z, (∃ x, root.toFun x = z) ∨ ∃ j x, (child j).toFun x = z

namespace Tile
variable {P}

noncomputable def binary (g : PrincipalAmalgamation.Input P P) : Tile P (ULift.{u} Unit) where
  Space := g.Node
  order := g.order
  root := { toMeetEmbedding := g.left, ideal := g.left_ideal }
  child _ := { toMeetEmbedding := g.right, ideal := g.right_ideal }
  cover z := by
    rcases g.cover z with ⟨x, eq⟩ | ⟨x, eq⟩
    · exact Or.inl ⟨x, eq⟩
    · exact Or.inr ⟨⟨()⟩, x, eq⟩

noncomputable def rectangle (r : Rectangle.Input P) : Tile P (ULift.{u} Bool) where
  Space := r.copies.Node
  order := r.copies.order
  root := { toMeetEmbedding := r.root, ideal := r.copies.vertex_ideal .root }
  child j := match j.down with
    | false => { toMeetEmbedding := r.first, ideal := r.copies.vertex_ideal .one }
    | true => { toMeetEmbedding := r.second, ideal := r.copies.vertex_ideal .two }
  cover z := by
    rcases r.three_vertex_cover z with ⟨i, x, eq⟩
    cases i with
    | root => exact Or.inl ⟨x, eq⟩
    | one => exact Or.inr ⟨⟨false⟩, x, eq⟩
    | two => exact Or.inr ⟨⟨true⟩, x, eq⟩

end Tile

inductive Request where
  | separation (W : A)
  | compression (K : A) (copy : MeetIso P (idealOrder P K))
  | rectangle (data : Rectangle.Input P)

namespace Request
variable {P}

def Child : Request P → Type u
  | .separation _ => ULift.{u} Unit
  | .compression _ _ => ULift.{u} Unit
  | .rectangle _ => ULift.{u} Bool

noncomputable def tile (T : A) (greatest : ∀ x, P.le x T) : (r : Request P) → Tile P r.Child
  | .separation W => Tile.binary (BinaryTiles.separation P W)
  | .compression K copy => Tile.binary (BinaryTiles.compression P T K greatest copy)
  | .rectangle r => Tile.rectangle r

end Request

structure Family (R : Type u) where
  top : A
  greatest : ∀ x, P.le x top
  request : R → Request P

namespace Family
variable {P} {R : Type u} (f : Family P R)

def Child (r : R) := (f.request r).Child
def Letters := Sigma f.Child
noncomputable def tile (r : R) : Tile P (f.Child r) := (f.request r).tile f.top f.greatest

end Family

end Compression.RecursiveMaps.TileRequests



namespace Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

open Attachment
universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)
variable {B : Type u} (value : ∀ v, g.Space v → B)

def Realizes (v w : Vertex J S R) (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) : Prop :=
  ∀ x : {x : g.Space w // (g.order w).le x i.rightAnchor},
    value w x.val = value v (i.overlap.toFun x).val

theorem realizes_reindex {v w v' w' : Vertex J S R} (hv : v = v') (hw : w = w')
    (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) :
    g.Realizes value v' w' (g.reindexInput hv hw i) ↔ g.Realizes value v w i := by
  cases hv
  cases hw
  rfl

def Equation (d : Dart J S R) : Prop :=
  ∀ x : {x : g.Space (source J S R request d) //
      (g.order (source J S R request d)).le x (g.anchor d)},
    value (source J S R request d) x.val =
      value (target J S R request d) ((g.arrow d).toFun x).val

theorem equation_of_reverse (d : Dart J S R) (h : g.Equation value (reverse J S R d)) :
    g.Equation value d := by
  rcases d with ⟨e, b⟩
  cases b
  · intro y
    have eq := h ((g.overlap e).inverse y)
    change value (source J S R request (e, true)) ((g.overlap e).inverse y).val =
      value (target J S R request (e, true)) ((g.overlap e).toFun ((g.overlap e).inverse y)).val at eq
    erw [(g.overlap e).right_inverse] at eq
    exact eq.symm
  · intro x
    have eq := h ((g.overlap e).toFun x)
    change value (target J S R request (e, true)) ((g.overlap e).toFun x).val =
      value (source J S R request (e, true)) ((g.overlap e).inverse ((g.overlap e).toFun x)).val at eq
    erw [(g.overlap e).left_inverse] at eq
    exact eq.symm

section
variable (parents : ∀ v (h : depth J S R request v ≠ 0),
  g.Realizes value (parent J S R request v) v (g.localGlue v h))
include parents

theorem incoming_realizes (v : Vertex J S R) (nonroot : v ≠ root J S R) :
    g.Realizes value (source J S R request (incoming J S R request v nonroot))
      (target J S R request (incoming J S R request v nonroot))
      (g.edgeInput (incoming J S R request v nonroot)) := by
  have nonzero : depth J S R request v ≠ 0 := fun h => nonroot ((depth_zero_iff J S R request v).mp h)
  exact (g.realizes_reindex value (parent_eq J S R request v nonroot).symm
    (incoming_target J S R request v nonroot) _).mp (parents v nonzero)

theorem equation_of_extension (d : Dart J S R)
    (eq : rootPath J S R request (target J S R request d) =
      rootPath J S R request (source J S R request d) ++ [d]) : g.Equation value d := by
  have realized := g.incoming_realizes value parents (target J S R request d)
    (extension_nonroot J S R request d eq)
  rw [incoming_of_extension J S R request d eq] at realized
  intro x
  have same := realized ((g.arrow d).toFun x)
  change value (target J S R request d) ((g.arrow d).toFun x).val =
    value (source J S R request d) ((g.arrow d).inverse ((g.arrow d).toFun x)).val at same
  rw [(g.arrow d).left_inverse] at same
  exact same.symm

theorem equations_of_parents (d : Dart J S R) : g.Equation value d := by
  rcases edge_root_paths J S R request d with forward | backward
  · exact g.equation_of_extension value parents d forward
  · apply g.equation_of_reverse value d
    apply g.equation_of_extension value parents (reverse J S R d)
    simpa only [source_reverse, target_reverse] using backward

end

theorem edge_identification (d : Dart J S R)
    (x : {x : g.Space (source J S R request d) //
      (g.order (source J S R request d)).le x (g.anchor d)}) :
    (g.vertex (source J S R request d)).toFun x.val =
      (g.vertex (target J S R request d)).toFun ((g.arrow d).toFun x).val :=
  g.equations_of_parents (fun v => (g.vertex v).toFun)
    (fun v h => g.parent_identification v h) d x

end Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces



namespace Compression.RecursiveMaps

open RationalHeights
universe u v w

namespace IdealEmbedding
variable {A : Type u} {B : Type v} {H : Type w}
    {P : MeetOrder A} {Q : MeetOrder B}

theorem projection_mono (f : IdealEmbedding P Q) (top : A) {x y : B}
    (lower : Q.le x y) : P.le (f.projection top x) (f.projection top y) := by
  apply (f.le_iff _ _).mp
  rw [f.projection_spec, f.projection_spec]
  exact Q.le_meet (Q.trans (Q.meet_le_left _ _) lower) (Q.meet_le_right _ _)

theorem projection_image (f : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) (a : A) : f.projection top (f.toFun a) = a := by
  apply embedding_injective f.toMeetEmbedding
  rw [f.projection_spec]
  exact Q.antisymm (Q.meet_le_left _ _)
    (Q.le_meet (Q.refl _) ((f.le_iff _ _).mpr (greatest a)))

theorem projected_strict (f : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) {R : HeightOrder H} (height : StrictHeight P R)
    (x y : B) (lower : Q.le x y) (different : x ≠ y) (in_copy : ∃ a, f.toFun a = y) :
    R.lt (height.value (f.projection top x)) (height.value (f.projection top y)) := by
  rcases in_copy with ⟨b, rfl⟩
  rcases f.ideal b x lower with ⟨a, rfl⟩
  rw [f.projection_image top greatest, f.projection_image top greatest]
  exact height.strict a b ((f.le_iff _ _).mp lower)
    (fun eq => different (congrArg f.toFun eq))

end IdealEmbedding

namespace LinearHeightOrder
variable {H : Type u} {K : Type v}

theorem lex_strict (R : LinearHeightOrder H) (S : LinearHeightOrder K) {x y : H × K}
    (first : R.Weak x.1 y.1)
    (strict : R.lt x.1 y.1 ∨ S.lt x.2 y.2) : (R.lex S).lt x y := by
  rcases first with eq | lower
  · rcases strict with lower | lower
    · exact False.elim (R.irrefl _ (eq ▸ lower))
    · exact Or.inr ⟨eq, lower⟩
  · exact Or.inl lower

end LinearHeightOrder

namespace TileRequests.Tile
variable {A : Type u} {H : Type v} {P : MeetOrder A}
    (top : A) (greatest : ∀ a, P.le a top)
    (R : LinearHeightOrder H) (seed : StrictHeight P R.toHeightOrder)

noncomputable def binaryTuple (t : Tile P (ULift.{u} Unit)) :
    StrictHeight t.order (R.lex R).toHeightOrder where
  value x := (seed.value (t.root.projection top x),
    seed.value ((t.child ⟨()⟩).projection top x))
  strict x y lower different := by
    apply R.lex_strict R (seed.mono (t.root.projection_mono top lower))
    rcases t.cover y with root | ⟨j, a, eq⟩
    · exact Or.inl (t.root.projected_strict top greatest seed x y lower different root)
    · rcases j with ⟨⟨⟩⟩
      exact Or.inr ((t.child ⟨()⟩).projected_strict top greatest seed x y lower different ⟨a, eq⟩)

noncomputable def rectangleTuple (t : Tile P (ULift.{u} Bool)) :
    StrictHeight t.order (R.lex (R.lex R)).toHeightOrder where
  value x := (seed.value (t.root.projection top x),
    seed.value ((t.child ⟨false⟩).projection top x),
    seed.value ((t.child ⟨true⟩).projection top x))
  strict x y lower different := by
    apply R.lex_strict (R.lex R) (seed.mono (t.root.projection_mono top lower))
    rcases t.cover y with root | ⟨j, a, eq⟩
    · exact Or.inl (t.root.projected_strict top greatest seed x y lower different root)
    · apply Or.inr
      apply R.lex_strict R (seed.mono ((t.child ⟨false⟩).projection_mono top lower))
      rcases j with ⟨j⟩
      cases j with
      | false => exact Or.inl ((t.child ⟨false⟩).projected_strict top greatest seed
          x y lower different ⟨a, eq⟩)
      | true => exact Or.inr ((t.child ⟨true⟩).projected_strict top greatest seed
          x y lower different ⟨a, eq⟩)

end TileRequests.Tile

end Compression.RecursiveMaps



end PartitionPilot

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_IncidenceQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)
variable {B : Type u} (value : ∀ v, g.Space v → B)

theorem realizes_of_equation (d : Dart J S R) (h : g.Equation value d) :
    g.Realizes value (source J S R request d) (target J S R request d) (g.edgeInput d) := by
  intro x
  have eq := h ((g.arrow d).inverse x)
  erw [(g.arrow d).right_inverse] at eq
  exact eq.symm

theorem parents_of_equations (edges : ∀ d, g.Equation value d)
    (v : Vertex J S R) (h : depth J S R request v ≠ 0) :
    g.Realizes value (parent J S R request v) v (g.localGlue v h) := by
  have nonroot : v ≠ root J S R := fun eq => h ((depth_zero_iff J S R request v).mpr eq)
  exact (g.realizes_reindex value (parent_eq J S R request v nonroot).symm
    (incoming_target J S R request v nonroot) _).mpr
      (g.realizes_of_equation value _ (edges _))

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_ExternalTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps

namespace TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

def fullIdeal : MeetIso (idealOrder P f.top) P where
  toFun := Subtype.val
  le_iff _ _ := Iff.rfl
  map_meet _ _ := rfl
  inverse x := ⟨x, f.greatest x⟩
  left_inverse _ := rfl
  right_inverse _ := rfl

noncomputable def vertexIdealIso {B : Type u} {Q : MeetOrder B} (i : IdealEmbedding P Q) :
    MeetIso P (idealOrder Q (i.toFun f.top)) :=
  RootedGluing.chainIso (inverseIso f.fullIdeal) (i.principalIso f.top)

def Space : TileStars.Vertex J f.Letters R → Type u
  | .inl _ => A
  | .inr c => (f.tile c.2).Space

noncomputable def localOrder : (v : TileStars.Vertex J f.Letters R) → MeetOrder (f.Space v)
  | .inl _ => P
  | .inr c => (f.tile c.2).order

noncomputable def leftAnchor (e : TileStars.Edge J f.Letters R) :
    f.Space (TileStars.source J f.Letters R Sigma.fst (e, true)) := by
  cases e with
  | inl c => exact f.top
  | inr e => exact ((f.tile e.2.1).child e.2.2).toFun f.top

noncomputable def rightAnchor (e : TileStars.Edge J f.Letters R) :
    f.Space (TileStars.target J f.Letters R Sigma.fst (e, true)) := by
  cases e with
  | inl c => exact (f.tile c.2).root.toFun f.top
  | inr e => exact f.top

noncomputable def edgeOverlap (e : TileStars.Edge J f.Letters R) : MeetIso
    (idealOrder (f.localOrder (TileStars.source J f.Letters R Sigma.fst (e, true))) (f.leftAnchor e))
    (idealOrder (f.localOrder (TileStars.target J f.Letters R Sigma.fst (e, true))) (f.rightAnchor e)) := by
  cases e with
  | inl c =>
    exact RootedGluing.chainIso f.fullIdeal (RootedGluing.chainIso
      (inverseIso (a.chart c.1)) (f.vertexIdealIso (f.tile c.2).root))
  | inr e =>
    exact RootedGluing.chainIso (inverseIso (f.vertexIdealIso ((f.tile e.2.1).child e.2.2)))
      (RootedGluing.chainIso (a.chart (e.1 * generator J f.Letters e.2)) (inverseIso f.fullIdeal))

noncomputable def diagram : TileStars.Spaces J f.Letters R Sigma.fst where
  Space := f.Space
  order := f.localOrder
  leftAnchor := f.leftAnchor
  rightAnchor := f.rightAnchor
  overlap := f.edgeOverlap a

def Node := (f.diagram a).Node
noncomputable def gluedOrder : MeetOrder (f.Node a) := (f.diagram a).gluedOrder

noncomputable def copy (w : External J f.Letters) : IdealEmbedding P (f.gluedOrder a) :=
  (a.ideal (coordinate J f.Letters w)).comp ((f.diagram a).vertex (.inl (point J f.Letters w)))

noncomputable def placedTile (w : External J f.Letters) (r : R) :
    IdealEmbedding (f.tile r).order (f.gluedOrder a) := (f.diagram a).vertex (.inr (w, r))

theorem copy_coordinate (w : External J f.Letters) (j : J) (x : A) :
    (f.copy a (w * old J f.Letters j)).toFun x = (f.copy a w).toFun ((a.iso j).toFun x) := by
  change ((f.diagram a).vertex (.inl (point J f.Letters (w * old J f.Letters j)))).toFun
    ((a.chart (w * old J f.Letters j)).toFun x) = _
  rw [point_mul_old, a.chart_mul_old]
  rfl

theorem copy_one (x : A) : (f.copy a 1).toFun x =
    ((f.diagram a).vertex (.inl (root J f.Letters))).toFun x := by
  change ((f.diagram a).vertex (.inl (root J f.Letters))).toFun ((a.chart 1).toFun x) = _
  rw [a.chart_one]

theorem stem_formula (w : External J f.Letters) (r : R) (x : A) :
    ((f.edgeOverlap a (.inl (w, r))).toFun ⟨(a.chart w).toFun x, f.greatest _⟩).val =
      (f.tile r).root.toFun x := by
  change (f.tile r).root.toFun ((a.chart w).inverse ((a.chart w).toFun x)) = _
  rw [(a.chart w).left_inverse]

theorem branch_formula (w : External J f.Letters) (r : R) (j : f.Child r) (x : A) :
    ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun
      ⟨((f.tile r).child j).toFun x, (((f.tile r).child j).le_iff _ _).mpr (f.greatest x)⟩).val =
      (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun x := by
  have inv := (f.vertexIdealIso ((f.tile r).child j)).left_inverse x
  change (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun
    ((f.vertexIdealIso ((f.tile r).child j)).inverse
      ((f.vertexIdealIso ((f.tile r).child j)).toFun x)) = _
  rw [inv]

theorem root_identification (w : External J f.Letters) (r : R) (x : A) :
    (f.placedTile a w r).toFun ((f.tile r).root.toFun x) = (f.copy a w).toFun x := by
  have eq := (f.diagram a).edge_identification (.inl (w, r), true)
    ⟨(a.chart w).toFun x, f.greatest _⟩
  change (f.copy a w).toFun x = (f.placedTile a w r).toFun
    ((f.edgeOverlap a (.inl (w, r))).toFun ⟨(a.chart w).toFun x, f.greatest _⟩).val at eq
  rw [f.stem_formula] at eq
  exact eq.symm

theorem child_identification (w : External J f.Letters) (r : R) (j : f.Child r) (x : A) :
    (f.placedTile a w r).toFun (((f.tile r).child j).toFun x) =
      (f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x := by
  have eq := (f.diagram a).edge_identification (.inr (w, ⟨r, j⟩), true)
    ⟨((f.tile r).child j).toFun x, (((f.tile r).child j).le_iff _ _).mpr (f.greatest x)⟩
  change (f.placedTile a w r).toFun (((f.tile r).child j).toFun x) =
    ((f.diagram a).vertex (.inl (point J f.Letters (w * generator J f.Letters ⟨r, j⟩)))).toFun
      ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun
        ⟨((f.tile r).child j).toFun x, (((f.tile r).child j).le_iff _ _).mpr (f.greatest x)⟩).val at eq
  rw [f.branch_formula] at eq
  exact eq

theorem copy_cover (z : f.Node a) : ∃ w x, (f.copy a w).toFun x = z := by
  rcases (f.diagram a).cover z with ⟨v, x, rfl⟩
  cases v with
  | inl v =>
    refine ⟨representative J f.Letters v, (a.chart (representative J f.Letters v)).inverse x, ?_⟩
    change ((f.diagram a).vertex (.inl (point J f.Letters (representative J f.Letters v)))).toFun
      ((a.chart (representative J f.Letters v)).toFun
        ((a.chart (representative J f.Letters v)).inverse x)) = _
    erw [(a.chart (representative J f.Letters v)).right_inverse, representative_spec]
  | inr c =>
    rcases (f.tile c.2).cover x with ⟨y, rfl⟩ | ⟨j, y, rfl⟩
    · exact ⟨c.1, y, (f.root_identification a c.1 c.2 y).symm⟩
    · exact ⟨c.1 * generator J f.Letters ⟨c.2, j⟩, y,
        (f.child_identification a c.1 c.2 j y).symm⟩

theorem comparison_in_copy (x y : f.Node a) (h : (f.gluedOrder a).le x y) :
    ∃ w b c, (f.copy a w).toFun b = x ∧ (f.copy a w).toFun c = y ∧ P.le b c := by
  rcases f.copy_cover a y with ⟨w, c, rfl⟩
  rcases (f.copy a w).ideal c x h with ⟨b, rfl⟩
  exact ⟨w, b, c, rfl, rfl, ((f.copy a w).le_iff b c).mp h⟩

end TileRequests.Family



namespace CosetGeometry.TileStars.Spaces

universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)
variable {B : Type u} (value : ∀ v, g.Space v → B)
variable (edges : ∀ d, g.Equation value d)

include edges in
theorem values_respect_parents {x y : g.scheme.Label} (h : g.scheme.Related x y) :
    value x.1 x.2 = value y.1 y.2 := by
  induction h with
  | parent v hv x => exact g.parents_of_equations value edges v hv x
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

noncomputable def descend (z : g.Node) : B :=
  Quotient.lift (fun x => value x.1 x.2)
    (fun _ _ h => g.values_respect_parents value edges h) (g.scheme.toGenerated z)

theorem descend_vertex (v : Vertex J S R) (x : g.Space v) :
    g.descend value edges ((g.vertex v).toFun x) = value v x := by
  change Quotient.lift _ _ (g.scheme.toGenerated ((g.scheme.vertex v).toFun x)) = _
  erw [g.scheme.toGenerated_vertex]
  rfl

end CosetGeometry.TileStars.Spaces



namespace TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

noncomputable def translationValue (g : External J f.Letters) :
    (v : TileStars.Vertex J f.Letters R) → f.Space v → f.Node a
  | .inl v, x => (f.copy a (g * representative J f.Letters v)).toFun x
  | .inr c, x => (f.placedTile a (g * c.1) c.2).toFun x

theorem translationValue_copy (g w : External J f.Letters) (x : A) :
    f.translationValue a g (.inl (point J f.Letters w)) ((a.chart w).toFun x) =
      (f.copy a (g * w)).toFun x := by
  change (f.copy a (g * representative J f.Letters (point J f.Letters w))).toFun
    ((a.iso (coordinate J f.Letters w)).toFun x) = _
  rw [← f.copy_coordinate, mul_assoc, coordinate_spec]

theorem translation_stem (g w : External J f.Letters) (r : R) :
    (f.diagram a).Equation (f.translationValue a g) (.inl (w, r), true) := by
  intro x
  change f.translationValue a g (.inl (point J f.Letters w)) x.val =
    (f.placedTile a (g * w) r).toFun ((f.tile r).root.toFun ((a.chart w).inverse x.val))
  rw [f.root_identification]
  have eq := f.translationValue_copy a g w ((a.chart w).inverse x.val)
  erw [(a.chart w).right_inverse] at eq
  exact eq

theorem translation_branch (g w : External J f.Letters) (r : R) (j : f.Child r) :
    (f.diagram a).Equation (f.translationValue a g) (.inr (w, ⟨r, j⟩), true) := by
  intro x
  let i := f.vertexIdealIso ((f.tile r).child j)
  obtain ⟨y, rfl⟩ : ∃ y, i.toFun y = x := ⟨i.inverse x, i.right_inverse x⟩
  change (f.placedTile a (g * w) r).toFun (((f.tile r).child j).toFun y) =
    f.translationValue a g (.inl (point J f.Letters (w * generator J f.Letters ⟨r, j⟩)))
      ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val
  have formula : ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val =
      (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun y := f.branch_formula a w r j y
  rw [formula, f.translationValue_copy, ← mul_assoc]
  exact f.child_identification a (g * w) r j y

theorem translation_edges (g : External J f.Letters) (d : TileStars.Dart J f.Letters R) :
    (f.diagram a).Equation (f.translationValue a g) d := by
  rcases d with ⟨e, b⟩
  have forward : (f.diagram a).Equation (f.translationValue a g) (e, true) := by
    cases e with
    | inl c => exact f.translation_stem a g c.1 c.2
    | inr c => exact f.translation_branch a g c.1 c.2.1 c.2.2
  cases b
  · exact (f.diagram a).equation_of_reverse (f.translationValue a g) (e, false) forward
  · exact forward

noncomputable def translate (g : External J f.Letters) : f.Node a → f.Node a :=
  (f.diagram a).descend (f.translationValue a g) (f.translation_edges a g)

theorem translate_vertex (g : External J f.Letters) (v : TileStars.Vertex J f.Letters R)
    (x : f.Space v) :
    f.translate a g (((f.diagram a).vertex v).toFun x) = f.translationValue a g v x :=
  (f.diagram a).descend_vertex (f.translationValue a g) (f.translation_edges a g) v x

theorem translate_copy (g w : External J f.Letters) (x : A) :
    f.translate a g ((f.copy a w).toFun x) = (f.copy a (g * w)).toFun x := by
  change f.translate a g (((f.diagram a).vertex (.inl (point J f.Letters w))).toFun
    ((a.chart w).toFun x)) = _
  erw [f.translate_vertex, f.translationValue_copy]

theorem translate_tile (g w : External J f.Letters) (r : R) (x : (f.tile r).Space) :
    f.translate a g ((f.placedTile a w r).toFun x) = (f.placedTile a (g * w) r).toFun x :=
  f.translate_vertex a g (.inr (w, r)) x

end TileRequests.Family

end PartitionPilot.Compression.RecursiveMaps

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ExternalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem translate_one (z : f.Node a) : f.translate a 1 z = z := by
  rcases f.copy_cover a z with ⟨w, x, rfl⟩
  rw [f.translate_copy, one_mul]

theorem translate_mul (g h : External J f.Letters) (z : f.Node a) :
    f.translate a (g * h) z = f.translate a g (f.translate a h z) := by
  rcases f.copy_cover a z with ⟨w, x, rfl⟩
  rw [f.translate_copy, f.translate_copy, f.translate_copy, mul_assoc]

theorem translate_left_inverse (g : External J f.Letters) (z : f.Node a) :
    f.translate a g⁻¹ (f.translate a g z) = z := by
  rw [← f.translate_mul, inv_mul_cancel, f.translate_one]

theorem translate_right_inverse (g : External J f.Letters) (z : f.Node a) :
    f.translate a g (f.translate a g⁻¹ z) = z := by
  rw [← f.translate_mul, mul_inv_cancel, f.translate_one]

theorem translate_monotone (g : External J f.Letters) (x y : f.Node a)
    (h : (f.gluedOrder a).le x y) :
    (f.gluedOrder a).le (f.translate a g x) (f.translate a g y) := by
  rcases f.comparison_in_copy a x y h with ⟨w, b, c, rfl, rfl, hbc⟩
  rw [f.translate_copy, f.translate_copy]
  exact ((f.copy a (g * w)).le_iff b c).mpr hbc

theorem translate_le_iff (g : External J f.Letters) (x y : f.Node a) :
    (f.gluedOrder a).le (f.translate a g x) (f.translate a g y) ↔ (f.gluedOrder a).le x y := by
  constructor
  · intro h
    have back := f.translate_monotone a g⁻¹ _ _ h
    rw [f.translate_left_inverse, f.translate_left_inverse] at back
    exact back
  · exact f.translate_monotone a g x y

noncomputable def externalIso (g : External J f.Letters) : MeetIso (f.gluedOrder a) (f.gluedOrder a) :=
  isoOfOrder (f.translate a g) (f.translate a g⁻¹)
    (f.translate_left_inverse a g) (f.translate_right_inverse a g) (f.translate_le_iff a g)

noncomputable def externalAction : OrderAction (External J f.Letters) (f.gluedOrder a) where
  iso := f.externalIso a
  one := f.translate_one a
  mul := f.translate_mul a

theorem externalAction_copy (g w : External J f.Letters) (x : A) :
    ((f.externalAction a).iso g).toFun ((f.copy a w).toFun x) =
      (f.copy a (g * w)).toFun x := f.translate_copy a g w x

theorem extends_old_action (j : J) (x : A) :
    ((f.externalAction a).iso (old J f.Letters j)).toFun ((f.copy a 1).toFun x) =
      (f.copy a 1).toFun ((a.iso j).toFun x) := by
  rw [f.externalAction_copy, mul_one]
  simpa only [one_mul] using f.copy_coordinate a 1 j x

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_OutwardSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

universe u
variable {J S R : Type u} [Group J] {request : S → R} (g : Spaces J S R request)

def FullRight {v w : Vertex J S R} (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) : Prop :=
  ∀ x, (g.order w).le x i.rightAnchor

theorem fullRight_reindex {v w v' w' : Vertex J S R} (hv : v = v') (hw : w = w')
    (i : PrincipalAmalgamation.Input (g.order v) (g.order w)) :
    g.FullRight (g.reindexInput hv hw i) ↔ g.FullRight i := by
  cases hv
  cases hw
  rfl

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars.Spaces

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem edge_full_at_old (d : TileStars.Dart J f.Letters R) (v : CosetGeometry.Vertex J f.Letters)
    (targetOld : TileStars.target J f.Letters R Sigma.fst d = .inl v) :
    (f.diagram a).FullRight ((f.diagram a).edgeInput d) := by
  rcases d with ⟨e, b⟩
  cases e with
  | inl c =>
    cases b with
    | false => exact f.greatest
    | true => exact False.elim (Sum.inr_ne_inl targetOld)
  | inr c =>
    cases b with
    | false => exact False.elim (Sum.inr_ne_inl targetOld)
    | true => exact f.greatest

theorem old_local_full (v : CosetGeometry.Vertex J f.Letters)
    (h : TileStars.depth J f.Letters R Sigma.fst (.inl v) ≠ 0) :
    (f.diagram a).FullRight ((f.diagram a).localGlue (.inl v) h) := by
  have nonroot : Sum.inl v ≠ TileStars.root J f.Letters R :=
    fun eq => h ((TileStars.depth_zero_iff J f.Letters R Sigma.fst _).mpr eq)
  exact ((f.diagram a).fullRight_reindex
    (TileStars.parent_eq J f.Letters R Sigma.fst (.inl v) nonroot).symm
    (TileStars.incoming_target J f.Letters R Sigma.fst (.inl v) nonroot) _).mpr
    (f.edge_full_at_old a _ v (TileStars.incoming_target J f.Letters R Sigma.fst (.inl v) nonroot))

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family



namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing

universe u

@[instance_reducible] noncomputable def chosenWellOrder (I : Type u) : LinearOrder I :=
  Classical.choose (exists_wellFoundedLT I)

end PartitionPilot.Compression.RecursiveMaps.RootedGluing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GluingBirthRanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps



namespace TileRequests

universe u

namespace Request
variable {A : Type u} {P : MeetOrder A}

instance child_countable (r : Request P) : Countable r.Child := by
  cases r <;> dsimp [Child] <;> infer_instance

end Request

namespace Family
variable {A R : Type u} {P : MeetOrder A} (f : Family P R)

instance child_countable (r : R) : Countable (f.Child r) := Request.child_countable (f.request r)

end Family
end TileRequests




universe u


end PartitionPilot.Compression.RecursiveMaps

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_MainRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Compression.RecursiveMaps

universe u
structure ActionRectangle {A G : Type u} (P : MeetOrder A) (action : G → MeetIso P P) where
  C : A
  B : A
  D : A
  first : G
  second : G
  C_le_D : P.le C D
  B_le_D : P.le B D
  agree : ∀ x, P.le x (P.meet C B) → (action first).toFun x = (action second).toFun x
  separated : P.meet ((action first).toFun D) ((action second).toFun D) =
    (action first).toFun (P.meet C B)

namespace ActionRectangle
variable {A G : Type u} {P : MeetOrder A} {action : G → MeetIso P P}

def toInput (r : ActionRectangle P action) (top : A) (greatest : ∀ x, P.le x top) :
    Rectangle.Input P where
  top := top
  greatest := greatest
  C := r.C
  B := r.B
  D := r.D
  C_le_D := r.C_le_D
  B_le_D := r.B_le_D
  g1 := action r.first
  g2 := action r.second
  agree := r.agree
  separated := r.separated

end ActionRectangle

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ProfileTransport
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u
variable {A B C : Type u} {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}

def PreservesProfiles (e : MeetEmbedding P Q) : Prop :=
  ∀ c v K F, (∃ a, F a) → ¬ P.le v K → Profile P c v K F → ProfileOver e c v K F

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_InitialRowForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction

universe u
variable {A G : Type u} [Group G] {P : MeetOrder A} (a : OrderAction G P)

theorem act_inv_right (g : G) (x : A) : (a.iso g).toFun ((a.iso g⁻¹).toFun x) = x := by
  rw [← a.mul, mul_inv_cancel, a.one]

def fixSubgroup (C : A) : Subgroup G where
  carrier := {g | ∀ x, P.le x C → (a.iso g).toFun x = x}
  one_mem' := fun x _ => a.one x
  mul_mem' {g h} hg hh x lower := by rw [a.mul, hh x lower, hg x lower]
  inv_mem' {g} hg x lower := by
    apply embedding_injective (a.iso g).toMeetEmbedding
    exact (a.act_inv_right g x).trans (hg x lower).symm

def conjugateHom (g : G) : G →* G where
  toFun h := g * h * g⁻¹
  map_one' := by simp
  map_mul' h k := by simp [mul_assoc]

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction



namespace PartitionPilot.Compression.RecursiveMaps

open CosetGeometry.OrderAction
universe u v

structure NormalSubgroupFamily (G : Type u) [Group G] where
  mem : Subgroup G → Prop
  top : mem ⊤
  upward : ∀ {K H}, mem K → K ≤ H → mem H
  inf : ∀ {K H}, mem K → mem H → mem (K ⊓ H)
  conjugate : ∀ g {K}, mem K → mem (K.map (conjugateHom g))

end PartitionPilot.Compression.RecursiveMaps



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v

structure PosetAction (G : Type v) [Group G] (P : Type u) [PartialOrder P] where
  iso : G → P ≃o P
  one : ∀ p, iso 1 p = p
  mul : ∀ g h p, iso (g * h) p = iso g (iso h p)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem empty_mem (nonempty : M.sets.Nonempty) : (∅ : ZFSet.{u}) ∈ M.sets := by
  classical
  have descend : ∀ x : ZFSet.{u}, x ∈ M.sets → (∅ : ZFSet.{u}) ∈ M.sets := by
    intro x
    induction x using ZFSet.inductionOn with
    | h x ih =>
      intro hx
      by_cases member : ∃ y, y ∈ x
      · obtain ⟨y, hy⟩ := member
        exact ih y hy (M.transitive hx hy)
      · have eq : x = ∅ := by
          apply ZFSet.ext
          intro y
          exact ⟨fun h => False.elim (member ⟨y, h⟩), fun h => False.elim (ZFSet.notMem_empty y h)⟩
        exact eq ▸ hx
  obtain ⟨x, hx⟩ := nonempty
  exact descend x hx

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_UnionEntryFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u})

theorem unorderedPair_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) : ({x, y} : ZFSet.{u}) ∈ M.sets := by
  simp only [SetFormula.pairing, realize_ex, realize_imp, realize_disj, Realize] at pairing
  obtain ⟨z, hz, spec⟩ := pairing x hx y hy
  have eq : z = ({x, y} : ZFSet.{u}) := by
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_pair]
    constructor
    · intro hw
      exact (spec w (M.transitive hz hw)).1 hw
    · intro hw
      have hwM : w ∈ M.sets := by
        rcases hw with rfl | rfl
        · exact hx
        · exact hy
      exact (spec w hwM).2 hw
  exact eq ▸ hz

theorem orderedPair_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) : ZFSet.pair x y ∈ M.sets := by
  have singleton : ({x} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx
  exact M.unorderedPair_mem pairing singleton (M.unorderedPair_mem pairing hx hy)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem union_mem (unions : Realize M.sets SetFormula.union Fin.elim0)
    {x : ZFSet.{u}} (hx : x ∈ M.sets) : ZFSet.sUnion x ∈ M.sets := by
  simp only [SetFormula.union, realize_ex, realize_imp, Realize] at unions
  obtain ⟨y, hy, spec⟩ := unions x hx
  have eq : y = ZFSet.sUnion x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · intro hz
      obtain ⟨w, _, wx, zw⟩ := (spec z (M.transitive hy hz)).1 hz
      exact ⟨w, wx, zw⟩
    · rintro ⟨w, wx, zw⟩
      have hw := M.transitive hx wx
      exact (spec z (M.transitive hw zw)).2 ⟨w, hw, wx, zw⟩
  exact eq ▸ hy

theorem binary_union_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) : x ∪ y ∈ M.sets := by
  have h := M.union_mem unions (M.unorderedPair_mem pairing hx hy)
  simpa only [ZFSet.sUnion_pair] using h

theorem power_witness (powers : Realize M.sets powerSet Fin.elim0)
    {x : ZFSet.{u}} (hx : x ∈ M.sets) :
    ∃ y ∈ M.sets, ∀ z ∈ M.sets, z ∈ y ↔ z ⊆ x := by
  simp only [powerSet, realize_ex, realize_imp, Realize] at powers
  obtain ⟨y, hy, spec⟩ := powers x hx
  refine ⟨y, hy, fun z hz => ⟨?_, ?_⟩⟩
  · intro zy w wz
    exact (spec z hz).1 zy w (M.transitive hz wz) wz
  · intro subset
    exact (spec z hz).2 (fun w _ hw => subset hw)

theorem separation_mem (separation : SeparationSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 1)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {x : ZFSet.{u}} (hx : x ∈ M.sets) :
    ZFSet.sep (fun z => Realize M.sets φ (extend z params)) x ∈ M.sets := by
  obtain ⟨y, hy, spec⟩ := separation φ params members x hx
  have eq : y = ZFSet.sep (fun z => Realize M.sets φ (extend z params)) x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · intro hz
      exact (spec z (M.transitive hy hz)).1 hz
    · intro hz
      exact (spec z (M.transitive hx hz.1)).2 hz
  exact eq ▸ hy

theorem exists_pair_bound (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    ∃ C ∈ M.sets, ∀ x ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ C := by
  obtain ⟨U, hU, specU⟩ := M.power_witness powers (M.binary_union_mem pairing unions hA hB)
  obtain ⟨C, hC, specC⟩ := M.power_witness powers hU
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hxM := M.transitive hA hx
  have hyM := M.transitive hB hy
  apply (specC _ (M.orderedPair_mem pairing hxM hyM)).2
  intro z hz
  rcases ZFSet.mem_pair.1 hz with rfl | rfl
  · have single : ({x} : ZFSet.{u}) ∈ M.sets := by
      simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hxM hxM
    apply (specU _ single).2
    intro w hw
    have eq := ZFSet.mem_singleton.1 hw
    exact ZFSet.mem_union.2 (Or.inl (eq ▸ hx))
  · apply (specU _ (M.unorderedPair_mem pairing hxM hyM)).2
    intro w hw
    rcases ZFSet.mem_pair.1 hw with rfl | rfl
    · exact ZFSet.mem_union.2 (Or.inl hx)
    · exact ZFSet.mem_union.2 (Or.inr hy)

end PartitionPilot.Forcing.TransitiveGround


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NaturalSetCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u

def SetMembers (Q : ZFSet.{u}) : Type u := Shrink Q

namespace SetMembers

noncomputable def raw {Q : ZFSet.{u}} (x : SetMembers Q) : ZFSet.{u} :=
  ((equivShrink.{u} Q).symm x).val

theorem raw_mem {Q : ZFSet.{u}} (x : SetMembers Q) : raw x ∈ Q :=
  ((equivShrink.{u} Q).symm x).property

theorem raw_injective (Q : ZFSet.{u}) : Function.Injective (@raw Q) := by
  intro x y eq
  apply (equivShrink.{u} Q).symm.injective
  exact Subtype.ext eq

noncomputable def ofMem {Q : ZFSet.{u}} (x : ZFSet.{u}) (hx : x ∈ Q) : SetMembers Q :=
  equivShrink.{u} Q ⟨x, hx⟩

theorem raw_ofMem {Q : ZFSet.{u}} (x : ZFSet.{u}) (hx : x ∈ Q) : raw (ofMem x hx) = x := by
  exact congrArg Subtype.val ((equivShrink.{u} Q).symm_apply_apply ⟨x, hx⟩)

noncomputable def presentation (Q : ZFSet.{u}) : Presentation (SetMembers Q) where
  carrier := Q
  encode := raw
  injective := raw_injective Q
  mem_carrier x := ⟨fun hx => ⟨ofMem x hx, raw_ofMem x hx⟩,
    fun ⟨a, eq⟩ => eq ▸ raw_mem a⟩

end SetMembers

end PartitionPilot.SetRealization



namespace PartitionPilot.Forcing

universe u

def natSetCode (n : Nat) : ZFSet.{u} := ZFSet.mk (PSet.ofNat n)

theorem natSetCode_succ (n : Nat) :
    natSetCode (n + 1) = insert (natSetCode n) (natSetCode n) := rfl

theorem mem_omega_iff_natSetCode (x : ZFSet.{u}) :
    x ∈ ZFSet.omega ↔ ∃ n, x = natSetCode n := by
  induction x using Quotient.inductionOn with
  | h x =>
    constructor
    · rintro ⟨⟨n⟩, h⟩
      exact ⟨n, ZFSet.sound h⟩
    · rintro ⟨n, h⟩
      exact ⟨⟨n⟩, ZFSet.exact h⟩

theorem natSetCode_mem_omega (n : Nat) : natSetCode n ∈ ZFSet.omega.{u} :=
  (mem_omega_iff_natSetCode _).2 ⟨n, rfl⟩

def zeroOrSuccessor (x : ZFSet.{u}) : Prop :=
  x = ∅ ∨ ∃ y ∈ x, x = insert y y

def naturalSetProperty (x : ZFSet.{u}) : Prop :=
  setTransitive x ∧ zeroOrSuccessor x ∧
    ∀ y ∈ x, setTransitive y ∧ zeroOrSuccessor y

theorem naturalSetProperty_empty : naturalSetProperty (∅ : ZFSet.{u}) := by
  refine ⟨?_, Or.inl rfl, ?_⟩
  · intro y hy
    exact False.elim (ZFSet.notMem_empty y hy)
  · intro y hy
    exact False.elim (ZFSet.notMem_empty y hy)

theorem naturalSetProperty_succ {x : ZFSet.{u}} (h : naturalSetProperty x) :
    naturalSetProperty (insert x x) := by
  refine ⟨?_, Or.inr ⟨x, ZFSet.mem_insert x x, rfl⟩, ?_⟩
  · intro y hy z hz
    rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · exact ZFSet.mem_insert_of_mem _ hz
    · exact ZFSet.mem_insert_of_mem x (h.1 y hy z hz)
  · intro y hy
    rcases ZFSet.mem_insert_iff.1 hy with rfl | hy
    · exact ⟨h.1, h.2.1⟩
    · exact h.2.2 y hy

theorem naturalSetProperty_member {x y : ZFSet.{u}}
    (h : naturalSetProperty x) (hy : y ∈ x) : naturalSetProperty y := by
  have facts := h.2.2 y hy
  exact ⟨facts.1, facts.2, fun z hz => h.2.2 z (h.1 y hy z hz)⟩

theorem naturalSetProperty_iff (x : ZFSet.{u}) :
    naturalSetProperty x ↔ ∃ n, x = natSetCode n := by
  constructor
  · induction x using ZFSet.inductionOn with
    | h x ih =>
      intro hx
      rcases hx.2.1 with empty | ⟨y, hy, succ⟩
      · exact ⟨0, empty⟩
      · obtain ⟨n, eq⟩ := ih y hy (naturalSetProperty_member hx hy)
        exact ⟨n + 1, by rw [succ, eq]; rfl⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact naturalSetProperty_empty
    | succ n ih => exact naturalSetProperty_succ ih

theorem naturalSetProperty_iff_mem_omega (x : ZFSet.{u}) :
    naturalSetProperty x ↔ x ∈ ZFSet.omega :=
  (naturalSetProperty_iff x).trans (mem_omega_iff_natSetCode x).symm

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedGroupCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

def Truth : {n : Nat} → BoundedFormula n → (Fin n → ZFSet.{u}) → Prop
  | _, .equal i j, env => env i = env j
  | _, .mem i j, env => env i ∈ env j
  | _, .neg φ, env => ¬ Truth φ env
  | _, .conj φ ψ, env => Truth φ env ∧ Truth ψ env
  | _, .allMem b φ, env => ∀ x ∈ env b, Truth φ (extend x env)

theorem truth_imp {n} (φ ψ : BoundedFormula n) (env : Fin n → ZFSet.{u}) :
    Truth (imp φ ψ) env ↔ (Truth φ env → Truth ψ env) := by
  classical
  simp only [imp, Truth, not_and, not_not]

theorem truth_disj {n} (φ ψ : BoundedFormula n) (env : Fin n → ZFSet.{u}) :
    Truth (disj φ ψ) env ↔ (Truth φ env ∨ Truth ψ env) := by
  classical
  simp only [disj, Truth, not_and_or, not_not]

theorem truth_exMem {n} (b : Fin n) (φ : BoundedFormula (n + 1)) (env : Fin n → ZFSet.{u}) :
    Truth (exMem b φ) env ↔ ∃ x ∈ env b, Truth φ (extend x env) := by
  classical
  simp only [exMem, Truth, not_forall, not_not, exists_prop]

theorem realize_toFormula (M : TransitiveGround.{u}) {n} (φ : BoundedFormula n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets φ.toFormula env ↔ Truth φ env := by
  induction φ with
  | equal i j => rfl
  | mem i j => rfl
  | neg φ ih => exact not_congr (ih env members)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ env members) (ihψ env members)
  | allMem b φ ih =>
    change (∀ x ∈ M.sets, Realize M.sets (SetFormula.imp (.mem 0 b.succ) φ.toFormula) (extend x env)) ↔ _
    constructor
    · intro h x hx
      have hxM := M.transitive (members b) hx
      exact (ih (extend x env) (Fin.cases hxM members)).1
        ((realize_imp M.sets _ _ _).1 (h x hxM) hx)
    · intro h x hxM
      apply (realize_imp M.sets _ _ _).2
      intro hx
      exact (ih (extend x env) (Fin.cases hxM members)).2 (h x hx)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def emptyFormula {n} (x : Fin n) : BoundedFormula n :=
  .allMem x (.neg (.equal 0 0))

def successorFormula {n} (y x : Fin n) : BoundedFormula n :=
  .conj (.mem x y) (.conj (.allMem x (.mem 0 y.succ))
    (.allMem y (disj (.equal 0 x.succ) (.mem 0 x.succ))))

def setTransitiveFormula {n} (x : Fin n) : BoundedFormula n :=
  .allMem x (.allMem 0 (.mem 0 x.succ.succ))

def zeroOrSuccessorFormula {n} (x : Fin n) : BoundedFormula n :=
  disj (emptyFormula x) (exMem x (successorFormula x.succ 0))

def naturalFormula {n} (x : Fin n) : BoundedFormula n :=
  .conj (setTransitiveFormula x) (.conj (zeroOrSuccessorFormula x)
    (.allMem x (.conj (setTransitiveFormula 0) (zeroOrSuccessorFormula 0))))

theorem truth_emptyFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (emptyFormula x) env ↔ env x = ∅ := by
  change (∀ y ∈ env x, ¬ y = y) ↔ _
  constructor
  · intro h
    exact (ZFSet.eq_empty _).2 (fun y hy => h y hy rfl)
  · intro h y hy
    exact False.elim ((ZFSet.eq_empty _).1 h y hy)

theorem truth_successorFormula {n} (y x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (successorFormula y x) env ↔ env y = insert (env x) (env x) := by
  simp only [successorFormula, Truth, truth_disj]
  change (env x ∈ env y ∧ (∀ z ∈ env x, z ∈ env y) ∧
    ∀ z ∈ env y, z = env x ∨ z ∈ env x) ↔ _
  constructor
  · rintro ⟨hx, lower, upper⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    exact ⟨upper z, fun h => h.elim (fun eq => eq.symm ▸ hx) (lower z)⟩
  · intro eq
    rw [eq]
    exact ⟨ZFSet.mem_insert _ _, fun _ hz => ZFSet.mem_insert_of_mem _ hz,
      fun _ hz => ZFSet.mem_insert_iff.1 hz⟩

theorem truth_setTransitiveFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (setTransitiveFormula x) env ↔ setTransitive (env x) := Iff.rfl

theorem truth_zeroOrSuccessorFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (zeroOrSuccessorFormula x) env ↔ zeroOrSuccessor (env x) := by
  simp only [zeroOrSuccessorFormula, truth_disj, truth_emptyFormula, truth_exMem,
    truth_successorFormula]
  rfl

theorem truth_naturalFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (naturalFormula x) env ↔ env x ∈ ZFSet.omega := by
  simp only [naturalFormula, Truth, truth_setTransitiveFormula, truth_zeroOrSuccessorFormula]
  exact naturalSetProperty_iff_mem_omega (env x)

theorem realize_naturalFormula (M : TransitiveGround.{u}) {n}
    (x : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (naturalFormula x).toFormula env ↔ env x ∈ ZFSet.omega :=
  (realize_toFormula M _ env members).trans (truth_naturalFormula x env)






theorem truth_singletonFormula {n} (z x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (singletonFormula z x) env ↔ env z = {env x} := by
  change (env x ∈ env z ∧ ∀ w ∈ env z, w = env x) ↔ _
  constructor
  · rintro ⟨member, only⟩
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_singleton]
    exact ⟨only w, fun eq => eq.symm ▸ member⟩
  · intro eq
    rw [eq]
    exact ⟨ZFSet.mem_singleton.2 rfl, fun _ h => ZFSet.mem_singleton.1 h⟩

theorem truth_unorderedPairFormula {n} (z x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (unorderedPairFormula z x y) env ↔ env z = {env x, env y} := by
  simp only [unorderedPairFormula, Truth, truth_disj]
  change (env x ∈ env z ∧ env y ∈ env z ∧ ∀ w ∈ env z, w = env x ∨ w = env y) ↔ _
  constructor
  · rintro ⟨hx, hy, only⟩
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_pair]
    refine ⟨only w, ?_⟩
    rintro (rfl | rfl)
    · exact hx
    · exact hy
  · intro eq
    rw [eq]
    exact ⟨ZFSet.mem_pair.2 (Or.inl rfl), ZFSet.mem_pair.2 (Or.inr rfl), fun _ h => ZFSet.mem_pair.1 h⟩

theorem truth_orderedPairFormula {n} (z x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (orderedPairFormula z x y) env ↔ env z = ZFSet.pair (env x) (env y) := by
  rw [orderedPairFormula, truth_exMem]
  constructor
  · rintro ⟨a, _, first, rest⟩
    have ha := (truth_singletonFormula 0 x.succ (extend a env)).1 first
    obtain ⟨b, _, second, shape⟩ := (truth_exMem _ _ _).1 rest
    have hb := (truth_unorderedPairFormula 0 x.succ.succ y.succ.succ (extend b (extend a env))).1 second
    have hz := (truth_unorderedPairFormula z.succ.succ 1 0 (extend b (extend a env))).1 shape
    change a = {env x} at ha
    change b = {env x, env y} at hb
    change env z = {a, b} at hz
    rw [hz, ha, hb]
    rfl
  · intro eq
    have ha : ({env x} : ZFSet.{u}) ∈ env z := by
      rw [eq]
      exact ZFSet.mem_pair.2 (Or.inl rfl)
    refine ⟨{env x}, ha, (truth_singletonFormula 0 x.succ _).2 rfl, ?_⟩
    apply (truth_exMem _ _ _).2
    have hb : ({env x, env y} : ZFSet.{u}) ∈ env z := by
      rw [eq]
      exact ZFSet.mem_pair.2 (Or.inr rfl)
    exact ⟨{env x, env y}, hb, (truth_unorderedPairFormula 0 x.succ.succ y.succ.succ _).2 rfl,
      (truth_unorderedPairFormula z.succ.succ 1 0 _).2 eq⟩

theorem truth_pairMembershipFormula {n} (x y r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pairMembershipFormula x y r) env ↔ ZFSet.pair (env x) (env y) ∈ env r := by
  rw [pairMembershipFormula, truth_exMem]
  constructor
  · rintro ⟨z, hz, shape⟩
    have eq := (truth_orderedPairFormula 0 x.succ y.succ (extend z env)).1 shape
    exact eq ▸ hz
  · intro member
    exact ⟨ZFSet.pair (env x) (env y), member, (truth_orderedPairFormula 0 x.succ y.succ _).2 rfl⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def graphFiberInclusionFormula {n} (x y f g : Fin n) : BoundedFormula n :=
  .allMem f (.allMem 0 (.allMem 0
    (imp (orderedPairFormula 2 x.succ.succ.succ 0)
      (pairMembershipFormula y.succ.succ.succ 0 g.succ.succ.succ))))

def graphFiberEqualityFormula {n} (x y f g : Fin n) : BoundedFormula n :=
  .conj (graphFiberInclusionFormula x y f g) (graphFiberInclusionFormula y x g f)

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

structure PartialOrderCode (Q R : ZFSet.{u}) : Prop where
  relation : R ⊆ ZFSet.prod Q Q
  refl : ∀ x ∈ Q, ZFSet.pair x x ∈ R
  antisymm : ∀ x ∈ Q, ∀ y ∈ Q, ZFSet.pair x y ∈ R → ZFSet.pair y x ∈ R → x = y
  trans : ∀ x ∈ Q, ∀ y ∈ Q, ∀ z ∈ Q,
    ZFSet.pair x y ∈ R → ZFSet.pair y z ∈ R → ZFSet.pair x z ∈ R

namespace BoundedFormula

open SetFormula

def relationOnFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem r (exMem c.succ (exMem c.succ.succ (orderedPairFormula 2 1 0)))

def reflexiveFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem c (pairMembershipFormula 0 0 r.succ)

def antisymmetricFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem c (.allMem c.succ (imp
    (.conj (pairMembershipFormula 1 0 r.succ.succ) (pairMembershipFormula 0 1 r.succ.succ)) (.equal 1 0)))

def transitiveFormula {n} (c r : Fin n) : BoundedFormula n :=
  .allMem c (.allMem c.succ (.allMem c.succ.succ (imp
    (.conj (pairMembershipFormula 2 1 r.succ.succ.succ) (pairMembershipFormula 1 0 r.succ.succ.succ))
    (pairMembershipFormula 2 0 r.succ.succ.succ))))

def partialOrderFormula {n} (c r : Fin n) : BoundedFormula n :=
  .conj (relationOnFormula c r) (.conj (reflexiveFormula c r)
    (.conj (antisymmetricFormula c r) (transitiveFormula c r)))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def orderedTripleFormula {n} (w x y z : Fin n) : BoundedFormula n :=
  exMem w (exMem 0 (.conj (orderedPairFormula 0 x.succ.succ y.succ.succ)
    (orderedPairFormula w.succ.succ 0 z.succ.succ)))

def tripleMembershipFormula {n} (x y z f : Fin n) : BoundedFormula n :=
  exMem f (orderedTripleFormula 0 x.succ y.succ z.succ)

theorem truth_orderedTripleFormula {n} (w x y z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (orderedTripleFormula w x y z) env ↔
      env w = ZFSet.pair (ZFSet.pair (env x) (env y)) (env z) := by
  simp only [orderedTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ a ∈ env w, ∃ b ∈ a, b = ZFSet.pair (env x) (env y) ∧
    env w = ZFSet.pair b (env z)) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, eq⟩
    exact eq
  · intro eq
    refine ⟨{ZFSet.pair (env x) (env y)}, ?_, ZFSet.pair (env x) (env y),
      ZFSet.mem_singleton.2 rfl, rfl, eq⟩
    rw [eq]
    exact ZFSet.mem_pair.2 (Or.inl rfl)

theorem truth_tripleMembershipFormula {n} (x y z f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (tripleMembershipFormula x y z f) env ↔
      ZFSet.pair (ZFSet.pair (env x) (env y)) (env z) ∈ env f := by
  simp only [tripleMembershipFormula, truth_exMem, truth_orderedTripleFormula]
  change (∃ w ∈ env f, w = ZFSet.pair (ZFSet.pair (env x) (env y)) (env z)) ↔ _
  exact ⟨fun ⟨_, hw, eq⟩ => eq ▸ hw, fun hw => ⟨_, hw, rfl⟩⟩

end PartitionPilot.Forcing.BoundedFormula


section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_relationBetweenFormula {n} (a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (relationBetweenFormula a b f) env ↔ env f ⊆ ZFSet.prod (env a) (env b) := by
  simp only [relationBetweenFormula, Truth, truth_exMem, truth_orderedPairFormula]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ZFSet.mem_prod.symm))

end PartitionPilot.Forcing.BoundedFormula

end


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u






def binaryRelationFormula {n} (g f : Fin n) : BoundedFormula n :=
  .allMem f (exMem g.succ (exMem g.succ.succ
    (exMem g.succ.succ.succ (orderedTripleFormula 3 2 1 0))))

def binaryFunctionFormula {n} (g f : Fin n) : BoundedFormula n :=
  .conj (binaryRelationFormula g f) (.allMem g (.allMem g.succ
    (exMem g.succ.succ (.conj (tripleMembershipFormula 2 1 0 f.succ.succ.succ)
      (.allMem g.succ.succ.succ (imp
        (tripleMembershipFormula 3 2 0 f.succ.succ.succ.succ) (.equal 0 1)))))))

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

structure GroupCode (G m i e : ZFSet.{u}) : Prop where
  mul_function : ZFSet.IsFunc (ZFSet.prod G G) G m
  inv_function : ZFSet.IsFunc G G i
  identity_mem : e ∈ G
  one_mul : ∀ x ∈ G, ZFSet.pair (ZFSet.pair e x) x ∈ m
  mul_one : ∀ x ∈ G, ZFSet.pair (ZFSet.pair x e) x ∈ m
  inv_mul : ∀ x ∈ G, ∀ y ∈ G, ZFSet.pair x y ∈ i → ZFSet.pair (ZFSet.pair y x) e ∈ m
  mul_assoc : ∀ x ∈ G, ∀ y ∈ G, ∀ z ∈ G, ∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G,
    ZFSet.pair (ZFSet.pair x y) a ∈ m → ZFSet.pair (ZFSet.pair y z) b ∈ m →
    ZFSet.pair (ZFSet.pair a z) c ∈ m → ZFSet.pair (ZFSet.pair x b) c ∈ m

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DecodedFunctionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation

universe u
variable {A B : Type u} (s : Presentation A) (t : Presentation B)

theorem exists_graph_value (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) (a : A) :
    ∃ b, ZFSet.pair (s.encode a) (t.encode b) ∈ f := by
  obtain ⟨y, rel, _⟩ := h.2 (s.encode a) (s.encode_mem a)
  have hy := (ZFSet.pair_mem_prod.1 (h.1 rel)).2
  obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
  exact ⟨b, rel⟩

noncomputable def decodeFunction (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) : A → B :=
  fun a => Classical.choose (s.exists_graph_value t f h a)

theorem decodeFunction_mem (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) (a : A) :
    ZFSet.pair (s.encode a) (t.encode (s.decodeFunction t f h a)) ∈ f :=
  Classical.choose_spec (s.exists_graph_value t f h a)

theorem decodeFunction_iff (f : ZFSet.{u}) (h : ZFSet.IsFunc s.carrier t.carrier f) (a : A) (b : B) :
    s.decodeFunction t f h a = b ↔ ZFSet.pair (s.encode a) (t.encode b) ∈ f := by
  constructor
  · intro eq
    simpa only [eq] using s.decodeFunction_mem t f h a
  · intro rel
    obtain ⟨y, _, unique⟩ := h.2 (s.encode a) (s.encode_mem a)
    apply t.injective
    exact (unique _ (s.decodeFunction_mem t f h a)).trans (unique _ rel).symm

end PartitionPilot.SetRealization.Presentation

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPartialFunctionSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def productElementFormula {n} (z a b : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (orderedPairFormula z.succ.succ 1 0))

theorem truth_productElementFormula {n} (z a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productElementFormula z a b) env ↔ env z ∈ ZFSet.prod (env a) (env b) := by
  simp only [productElementFormula, truth_exMem, truth_orderedPairFormula]
  exact ZFSet.mem_prod.symm

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_groundPower (B p : ZFSet.{u}) : p ∈ M.groundPower B ↔ p ∈ M.sets ∧ p ⊆ B := by
  rw [groundPower, ZFSet.mem_sep, ZFSet.mem_powerset]
  exact and_comm

theorem prod_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : ZFSet.prod A B ∈ M.sets := by
  obtain ⟨W, hW, bounds⟩ := M.exists_pair_bound pairing unions powers hA hB
  let params := extend A (extend B Fin.elim0)
  have selected := M.separation_mem separation (BoundedFormula.productElementFormula 0 1 2).toFormula
    params (Fin.cases hA (Fin.cases hB (fun j => Fin.elim0 j))) hW
  have correct (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (BoundedFormula.productElementFormula 0 1 2).toFormula (extend z params) ↔
        z ∈ ZFSet.prod A B :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hz (Fin.cases hA (Fin.cases hB (fun j => Fin.elim0 j))))).trans
        (BoundedFormula.truth_productElementFormula 0 1 2 _)
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.productElementFormula 0 1 2).toFormula (extend z params)) W = ZFSet.prod A B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive hW hz)).1 rel
    · intro hz
      have hzW : z ∈ W := by
        obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 hz
        exact eq.symm ▸ bounds x hx y hy
      exact ⟨hzW, (correct z (M.transitive hW hzW)).2 hz⟩
  exact eq ▸ selected

noncomputable def groundRelations (A B : ZFSet.{u}) : ZFSet.{u} := M.groundPower (ZFSet.prod A B)

theorem mem_groundRelations (A B p : ZFSet.{u}) :
    p ∈ M.groundRelations A B ↔ p ∈ M.sets ∧ p ⊆ ZFSet.prod A B := M.mem_groundPower _ _

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing

universe u

structure PartialFunctionCode (X Y p : ZFSet.{u}) : Prop where
  shape : p ⊆ ZFSet.prod X Y
  unique : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ p → y = z

namespace PartialFunctionCode

theorem empty (X Y : ZFSet.{u}) : PartialFunctionCode X Y ∅ :=
  ⟨ZFSet.empty_subset _, fun _ _ _ hp _ => False.elim (ZFSet.notMem_empty _ hp)⟩

end PartialFunctionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def partialFunctions (X Y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => PartialFunctionCode X Y p) (M.groundRelations X Y)

theorem mem_partialFunctions (X Y p : ZFSet.{u}) :
    p ∈ M.partialFunctions X Y ↔ p ∈ M.sets ∧ PartialFunctionCode X Y p := by
  rw [partialFunctions, ZFSet.mem_sep, M.mem_groundRelations]
  exact ⟨fun ⟨⟨ground, _⟩, code⟩ => ⟨ground, code⟩, fun ⟨ground, code⟩ => ⟨⟨ground, code.shape⟩, code⟩⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSizeWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace InjectionCode

theorem empty (N : ZFSet.{u}) : InjectionCode ∅ N ∅ := by
  refine ⟨⟨ZFSet.empty_subset _, ?_⟩, ?_⟩
  · intro x hx
    exact False.elim (ZFSet.notMem_empty x hx)
  · intro x _ z hx _
    exact False.elim (ZFSet.notMem_empty (ZFSet.pair x z) hx)

end InjectionCode

namespace TransitiveGround

open SetRealization SetFormula
variable (M : TransitiveGround.{u})

theorem empty_groundEmbeddable (N : ZFSet.{u}) (nonempty : M.sets.Nonempty) :
    M.groundEmbeddable ∅ N := ⟨∅, M.empty_mem nonempty, InjectionCode.empty N⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSmallFunctionSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def smallPartialFunctions (X Y N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => M.groundEmbeddable p N) (M.partialFunctions X Y)

theorem mem_smallPartialFunctions (X Y N p : ZFSet.{u}) :
    p ∈ M.smallPartialFunctions X Y N ↔
      p ∈ M.sets ∧ PartialFunctionCode X Y p ∧ M.groundEmbeddable p N := by
  rw [smallPartialFunctions, ZFSet.mem_sep, M.mem_partialFunctions]
  exact and_assoc

theorem empty_mem_smallPartialFunctions (X Y N : ZFSet.{u}) (nonempty : M.sets.Nonempty) :
    (∅ : ZFSet.{u}) ∈ M.smallPartialFunctions X Y N :=
  (M.mem_smallPartialFunctions X Y N ∅).2
    ⟨M.empty_mem nonempty, PartialFunctionCode.empty X Y, M.empty_groundEmbeddable N nonempty⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NonemptyTupleFields
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def nonemptyTupleCode : (k : Nat) → (Fin (k + 1) → ZFSet.{u}) → ZFSet.{u}
  | 0, fields => fields 0
  | k + 1, fields => ZFSet.pair (fields 0) (nonemptyTupleCode k (fun i => fields i.succ))

namespace BoundedFormula

open SetFormula

def nonemptyTupleFormula : (k : Nat) → {n : Nat} →
    Fin n → (Fin (k + 1) → Fin n) → BoundedFormula n
  | 0, _, z, fields => .equal z (fields 0)
  | k + 1, _, z, fields => exMem z (exMem 0
      (.conj (orderedPairFormula z.succ.succ (fields 0).succ.succ 0)
        (nonemptyTupleFormula k 0 (fun i => (fields i.succ).succ.succ))))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def reindex : {n m : Nat} → (Fin n → Fin m) → BoundedFormula n → BoundedFormula m
  | _, _, f, .equal i j => .equal (f i) (f j)
  | _, _, f, .mem i j => .mem (f i) (f j)
  | _, _, f, .neg φ => .neg (reindex f φ)
  | _, _, f, .conj φ ψ => .conj (reindex f φ) (reindex f ψ)
  | _, _, f, .allMem b φ => .allMem (f b) (reindex (liftIndex f) φ)

def exPairFields {n} (z : Fin n) (body : BoundedFormula (n + 2)) : BoundedFormula n :=
  exMem z (exMem 0 (exMem z.succ.succ (exMem 0
    (.conj (orderedPairFormula z.succ.succ.succ.succ 2 0)
      (reindex (Fin.cases 0 (Fin.cases 2 (fun i => i.succ.succ.succ.succ))) body)))))

end PartitionPilot.Forcing.BoundedFormula



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCopyGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def relationImage (D B r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ x ∈ D, ZFSet.pair x y ∈ r) B

theorem mem_relationImage (D B r y : ZFSet.{u}) :
    y ∈ relationImage D B r ↔ y ∈ B ∧ ∃ x ∈ D, ZFSet.pair x y ∈ r := ZFSet.mem_sep

end PartitionPilot.Forcing



section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def imageMemberFormula {n} (y d r : Fin n) : BoundedFormula n :=
  exMem d (pairMembershipFormula 0 y.succ r.succ)

def converseEntryFormula {n} (z a b r : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (.conj (orderedPairFormula z.succ.succ 0 1)
    (pairMembershipFormula 1 0 r.succ.succ)))

def composeEntryFormula {n} (z a b c r f : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (exMem c.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 0)
      (.conj (pairMembershipFormula 2 1 r.succ.succ.succ)
        (pairMembershipFormula 1 0 f.succ.succ.succ)))))

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem bounded_separation_mem (separation : SeparationSchema M.sets)
    {n} (φ : BoundedFormula (n + 1)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {D : ZFSet.{u}} (hD : D ∈ M.sets) :
    ZFSet.sep (fun z => BoundedFormula.Truth φ (extend z params)) D ∈ M.sets := by
  have selected := M.separation_mem separation φ.toFormula params members hD
  have eq : ZFSet.sep (fun z => Realize M.sets φ.toFormula (extend z params)) D =
      ZFSet.sep (fun z => BoundedFormula.Truth φ (extend z params)) D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr_right (fun hz => BoundedFormula.realize_toFormula M φ _
      (Fin.cases (M.transitive hD hz) members))
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairCompositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.FunctionGraphOn

universe u
variable {I f : ZFSet.{u}}

noncomputable def value (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} :=
  Classical.choose (h.total i.property)

theorem value_entry (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair i.val (h.value i) ∈ f :=
  Classical.choose_spec (h.total i.property)

theorem value_eq_of_entry (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I})
    {y : ZFSet.{u}} (entry : ZFSet.pair i.val y ∈ f) : h.value i = y :=
  h.unique (h.value_entry i) entry

end PartitionPilot.Forcing.FunctionGraphOn



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def compositionGraphFormula {n} (f B D L ell s : Fin n) : BoundedFormula n :=
  .conj (.allMem f (composeEntryFormula 0 B.succ D.succ L.succ ell.succ s.succ))
    (.allMem B (.allMem D.succ (.allMem L.succ.succ (imp
      (.conj (pairMembershipFormula 2 1 ell.succ.succ.succ)
        (pairMembershipFormula 1 0 s.succ.succ.succ)) (pairMembershipFormula 2 0 f.succ.succ.succ)))))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u v w

noncomputable def constantFamilyGraph (I x : ZFSet.{u}) : ZFSet.{u} := ZFSet.prod I {x}

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ParentSupportCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def orderedRightTripleFormula {n} (w x c q : Fin n) : BoundedFormula n :=
  exMem w (exMem 0 (.conj (orderedPairFormula 0 c.succ.succ q.succ.succ)
    (orderedPairFormula w.succ.succ x.succ.succ 0)))

def rightTripleMembershipFormula {n} (x c q f : Fin n) : BoundedFormula n :=
  exMem f (orderedRightTripleFormula 0 x.succ c.succ q.succ)

def relationToProductFormula {n} (a c q f : Fin n) : BoundedFormula n :=
  .allMem f (exMem a.succ (exMem c.succ.succ
    (exMem q.succ.succ.succ (orderedRightTripleFormula 3 2 1 0))))

def functionToProductFormula {n} (a c q f : Fin n) : BoundedFormula n :=
  .conj (relationToProductFormula a c q f)
    (.allMem a (exMem c.succ (exMem q.succ.succ
      (.conj (rightTripleMembershipFormula 2 1 0 f.succ.succ.succ)
        (.allMem c.succ.succ.succ (.allMem q.succ.succ.succ.succ
          (imp (rightTripleMembershipFormula 4 1 0 f.succ.succ.succ.succ.succ)
            (.conj (.equal 1 3) (.equal 0 2)))))))))

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def fiberFormula {n} (f x b r : Fin n) : BoundedFormula n :=
  .conj (.allMem f (.mem 0 b.succ)) (.allMem b
    (.conj (imp (.mem 0 f.succ) (pairMembershipFormula x.succ 0 r.succ))
      (imp (pairMembershipFormula x.succ 0 r.succ) (.mem 0 f.succ))))

def choiceUniformEntryFormula {n} (z a b r f c : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (exMem f.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (fiberFormula 0 2 b.succ.succ.succ r.succ.succ.succ)
        (pairMembershipFormula 0 1 c.succ.succ.succ)))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MapFamilyApplicationGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

noncomputable def indexedRelationSection (B C R i : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ q ∈ B, ∃ y ∈ C,
    z = ZFSet.pair q y ∧ ZFSet.pair (ZFSet.pair i q) y ∈ R) (ZFSet.prod B C)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def indexedRelationSections (I B C R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ M.groundRelations B C,
    z = ZFSet.pair i f ∧ f = indexedRelationSection B C R i)
    (ZFSet.prod I (M.groundRelations B C))

end TransitiveGround

end



open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundContainmentOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.PartialOrderCode

open SetRealization
universe u
variable {Q R : ZFSet.{u}} (h : PartialOrderCode Q R)

@[instance_reducible]
noncomputable def toPartialOrder : PartialOrder (SetMembers Q) where
  le x y := ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ R
  le_refl x := h.refl _ (SetMembers.raw_mem x)
  le_trans x y z xy yz := h.trans _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
    _ (SetMembers.raw_mem z) xy yz
  le_antisymm x y xy yx := SetMembers.raw_injective Q
    (h.antisymm _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y) xy yx)

@[instance_reducible]
noncomputable def toOrderTop (one : ZFSet.{u}) (hone : one ∈ Q)
    (greatest : ∀ x ∈ Q, ZFSet.pair x one ∈ R) :
    letI _decodedOrder := h.toPartialOrder
    OrderTop (SetMembers Q) := by
  letI decodedOrder := h.toPartialOrder
  refine { top := SetMembers.ofMem one hone, le_top := ?_ }
  intro x
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem one hone)) ∈ R
  rw [SetMembers.raw_ofMem]
  exact greatest _ (SetMembers.raw_mem x)

end PartitionPilot.Forcing.PartialOrderCode



namespace PartitionPilot.Forcing

universe u

noncomputable def reverseInclusionCode (Q : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ Q, ∃ q ∈ Q, z = ZFSet.pair p q ∧ q ⊆ p) (ZFSet.prod Q Q)

theorem mem_reverseInclusionCode (Q z : ZFSet.{u}) :
    z ∈ reverseInclusionCode Q ↔ ∃ p ∈ Q, ∃ q ∈ Q, z = ZFSet.pair p q ∧ q ⊆ p := by
  rw [reverseInclusionCode, ZFSet.mem_sep]
  exact ⟨And.right, fun ⟨p, hp, q, hq, eq, subset⟩ =>
    ⟨ZFSet.mem_prod.2 ⟨p, hp, q, hq, eq⟩, p, hp, q, hq, eq, subset⟩⟩

theorem pair_mem_reverseInclusionCode (Q p q : ZFSet.{u}) :
    ZFSet.pair p q ∈ reverseInclusionCode Q ↔ p ∈ Q ∧ q ∈ Q ∧ q ⊆ p := by
  rw [mem_reverseInclusionCode]
  constructor
  · rintro ⟨a, ha, b, hb, eq, subset⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, subset⟩
  · rintro ⟨hp, hq, subset⟩
    exact ⟨p, hp, q, hq, rfl, subset⟩

theorem reverseInclusion_partialOrder (Q : ZFSet.{u}) : PartialOrderCode Q (reverseInclusionCode Q) where
  relation := fun _ hz => (ZFSet.mem_sep.1 hz).1
  refl p hp := (pair_mem_reverseInclusionCode Q p p).2 ⟨hp, hp, fun _ hx => hx⟩
  antisymm p _ q _ pq qp := ZFSet.ext (fun _ =>
    ⟨fun hz => ((pair_mem_reverseInclusionCode Q q p).1 qp).2.2 hz,
      fun hz => ((pair_mem_reverseInclusionCode Q p q).1 pq).2.2 hz⟩)
  trans p hp q _ r hr pq qr := (pair_mem_reverseInclusionCode Q p r).2 ⟨hp, hr,
    fun _ hx => ((pair_mem_reverseInclusionCode Q p q).1 pq).2.2
      (((pair_mem_reverseInclusionCode Q q r).1 qr).2.2 hx)⟩

theorem reverseInclusion_empty_top {Q : ZFSet.{u}} (empty : (∅ : ZFSet.{u}) ∈ Q) :
    ∀ p ∈ Q, ZFSet.pair p ∅ ∈ reverseInclusionCode Q :=
  fun p hp => (pair_mem_reverseInclusionCode Q p ∅).2 ⟨hp, empty, ZFSet.empty_subset p⟩

namespace BoundedFormula

open SetFormula

def subsetFormula {n} (a b : Fin n) : BoundedFormula n := .allMem a (.mem 0 b.succ)

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSmallFunctionPermutations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

@[instance_reducible]
noncomputable def smallFunctionOrder (X Y N : ZFSet.{u}) :
    PartialOrder (SetMembers (M.smallPartialFunctions X Y N)) :=
  (reverseInclusion_partialOrder (M.smallPartialFunctions X Y N)).toPartialOrder

@[instance_reducible]
noncomputable def smallFunctionTop (X Y N : ZFSet.{u}) (nonempty : M.sets.Nonempty) :
    letI _smallOrder := M.smallFunctionOrder X Y N
    OrderTop (SetMembers (M.smallPartialFunctions X Y N)) :=
  (reverseInclusion_partialOrder (M.smallPartialFunctions X Y N)).toOrderTop ∅
    (M.empty_mem_smallPartialFunctions X Y N nonempty)
    (reverseInclusion_empty_top (M.empty_mem_smallPartialFunctions X Y N nonempty))

end PartitionPilot.Forcing.TransitiveGround


section



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula SetRealization
universe u

def entryTransportFormula {n} (a b r x y : Fin n) : BoundedFormula n :=
  exMem x (exMem x.succ (exMem y.succ.succ
    (.conj (orderedPairFormula a.succ.succ.succ 2 0)
      (.conj (orderedPairFormula b.succ.succ.succ 1 0)
        (pairMembershipFormula 2 1 r.succ.succ.succ)))))

def entryPermutationFormula {n} (z r x y c : Fin n) : BoundedFormula n :=
  exMem c (exMem c.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (entryTransportFormula 1 0 r.succ.succ x.succ.succ y.succ.succ)))

end PartitionPilot.Forcing.BoundedFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace BoundedFormula

def chronologyPairFormula {n} (z T : Fin n) : BoundedFormula n :=
  exMem T (exMem T.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (disj (.equal 0 1) (.mem 0 1))))

def chronologyPairsEquationFormula {n} (J T : Fin n) : BoundedFormula n :=
  .conj (.allMem J (chronologyPairFormula 0 T.succ))
    (.allMem T (.allMem T.succ (imp (disj (.equal 0 1) (.mem 0 1))
      (pairMembershipFormula 1 0 J.succ.succ))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SeparationFulfillmentCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




universe u

structure PosetActionCode (G P m e R A : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc (ZFSet.prod G P) P A
  one : ∀ p ∈ P, ZFSet.pair (ZFSet.pair e p) p ∈ A
  mul : ∀ g ∈ G, ∀ h ∈ G, ∀ k ∈ G, ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P,
    ZFSet.pair (ZFSet.pair g h) k ∈ m → ZFSet.pair (ZFSet.pair h p) q ∈ A →
    ZFSet.pair (ZFSet.pair g q) r ∈ A → ZFSet.pair (ZFSet.pair k p) r ∈ A
  monotone : ∀ g ∈ G, ∀ p ∈ P, ∀ q ∈ P, ∀ r ∈ P, ∀ s ∈ P,
    ZFSet.pair (ZFSet.pair g p) r ∈ A → ZFSet.pair (ZFSet.pair g q) s ∈ A →
    ZFSet.pair p q ∈ R → ZFSet.pair r s ∈ R

namespace BoundedFormula

open SetFormula

def actionOneFormula {n} (p e a : Fin n) : BoundedFormula n :=
  .allMem p (tripleMembershipFormula e.succ 0 0 a.succ)

def actionMulFormula {n} (g p m a : Fin n) : BoundedFormula n :=
  .allMem g (.allMem g.succ (.allMem g.succ.succ (.allMem p.succ.succ.succ
    (.allMem p.succ.succ.succ.succ (.allMem p.succ.succ.succ.succ.succ
      (imp (.conj (tripleMembershipFormula 5 4 3 m.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 4 2 1 a.succ.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 5 1 0 a.succ.succ.succ.succ.succ.succ)))
        (tripleMembershipFormula 3 2 0 a.succ.succ.succ.succ.succ.succ)))))))

def actionMonotoneFormula {n} (g p r a : Fin n) : BoundedFormula n :=
  .allMem g (.allMem p.succ (.allMem p.succ.succ (.allMem p.succ.succ.succ
    (.allMem p.succ.succ.succ.succ
      (imp (.conj (tripleMembershipFormula 4 3 1 a.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 4 2 0 a.succ.succ.succ.succ.succ)
          (pairMembershipFormula 3 2 r.succ.succ.succ.succ.succ)))
        (pairMembershipFormula 1 0 r.succ.succ.succ.succ.succ))))))

end BoundedFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_DecodedGroundGroups
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroupCode

open SetRealization
universe u
variable {G m i e : ZFSet.{u}} (h : GroupCode G m i e)

noncomputable def mul (x y : SetMembers G) : SetMembers G :=
  ((SetMembers.presentation G).product (SetMembers.presentation G)).decodeFunction
    (SetMembers.presentation G) m h.mul_function (x, y)

noncomputable def inv (x : SetMembers G) : SetMembers G :=
  (SetMembers.presentation G).decodeFunction (SetMembers.presentation G) i h.inv_function x

noncomputable def one : SetMembers G := SetMembers.ofMem e h.identity_mem

theorem raw_one : SetMembers.raw h.one = e := SetMembers.raw_ofMem e h.identity_mem

theorem mul_mem (x y : SetMembers G) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y)) (SetMembers.raw (h.mul x y)) ∈ m :=
  ((SetMembers.presentation G).product (SetMembers.presentation G)).decodeFunction_mem
    (SetMembers.presentation G) m h.mul_function (x, y)

theorem inv_mem (x : SetMembers G) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw (h.inv x)) ∈ i :=
  (SetMembers.presentation G).decodeFunction_mem (SetMembers.presentation G) i h.inv_function x

theorem mul_eq_iff (x y z : SetMembers G) : h.mul x y = z ↔
    ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y)) (SetMembers.raw z) ∈ m :=
  ((SetMembers.presentation G).product (SetMembers.presentation G)).decodeFunction_iff
    (SetMembers.presentation G) m h.mul_function (x, y) z

theorem decoded_one_mul (x : SetMembers G) : h.mul h.one x = x := by
  apply (h.mul_eq_iff _ _ _).2
  rw [h.raw_one]
  exact h.one_mul _ (SetMembers.raw_mem x)

theorem decoded_mul_one (x : SetMembers G) : h.mul x h.one = x := by
  apply (h.mul_eq_iff _ _ _).2
  rw [h.raw_one]
  exact h.mul_one _ (SetMembers.raw_mem x)

theorem decoded_inv_mul (x : SetMembers G) : h.mul (h.inv x) x = h.one := by
  apply (h.mul_eq_iff _ _ _).2
  rw [h.raw_one]
  exact h.inv_mul _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem (h.inv x)) (h.inv_mem x)

theorem decoded_mul_assoc (x y z : SetMembers G) :
    h.mul (h.mul x y) z = h.mul x (h.mul y z) := by
  apply Eq.symm
  apply (h.mul_eq_iff _ _ _).2
  exact h.mul_assoc _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y) _ (SetMembers.raw_mem z)
    _ (SetMembers.raw_mem (h.mul x y)) _ (SetMembers.raw_mem (h.mul y z))
    _ (SetMembers.raw_mem (h.mul (h.mul x y) z)) (h.mul_mem x y) (h.mul_mem y z)
    (h.mul_mem (h.mul x y) z)

@[instance_reducible] noncomputable def toGroup : Group (SetMembers G) where
  mul := h.mul
  one := h.one
  inv := h.inv
  mul_assoc := h.decoded_mul_assoc
  one_mul := h.decoded_one_mul
  mul_one := h.decoded_mul_one
  inv_mul_cancel := h.decoded_inv_mul

end PartitionPilot.Forcing.GroupCode

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section



namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]

noncomputable def actionGraph (a : PosetAction G P) (s : Presentation P) (t : Presentation G) : ZFSet.{u} :=
  (t.product s).graph s (fun x => a.iso x.1 x.2)

theorem triple_mem_actionGraph (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (g : G) (p q : P) :
    ZFSet.pair (ZFSet.pair (t.encode g) (s.encode p)) (s.encode q) ∈ a.actionGraph s t ↔ a.iso g p = q :=
  (t.product s).pair_mem_graph s (fun x => a.iso x.1 x.2) (g, p) q

end PartitionPilot.Forcing.PosetAction

end


section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def actionRestrictionEntryFormula {n} (z g p : Fin n) : BoundedFormula n :=
  exMem g (exMem p.succ (exMem p.succ.succ
    (orderedTripleFormula z.succ.succ.succ 2 1 0)))

end PartitionPilot.Forcing.BoundedFormula

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMixtureNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u})

theorem infinity_witness (infinite : Realize M.sets infinity Fin.elim0) :
    ∃ I ∈ M.sets, (∅ : ZFSet.{u}) ∈ I ∧ ∀ x ∈ I, insert x x ∈ I := by
  simp only [infinity, emptySetFormula, successorFormula, realize_ex, realize_imp, realize_disj, Realize] at infinite
  obtain ⟨I, hI, ⟨e, he, eI, empty⟩, successors⟩ := infinite
  have eqEmpty : e = ∅ := by
    apply ZFSet.ext
    intro z
    exact ⟨fun hz => False.elim (empty z (M.transitive he hz) hz),
      fun hz => False.elim (ZFSet.notMem_empty z hz)⟩
  refine ⟨I, hI, eqEmpty ▸ eI, ?_⟩
  intro x hx
  have hxM := M.transitive hI hx
  obtain ⟨y, hy, yI, spec⟩ := successors x hxM hx
  have eq : y = insert x x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hz
      exact (spec z (M.transitive hy hz)).1 hz
    · intro hz
      have hzM : z ∈ M.sets := by
        rcases hz with rfl | hz
        · exact hxM
        · exact M.transitive hxM hz
      exact (spec z hzM).2 hz
  exact eq ▸ yI

end PartitionPilot.Forcing.TransitiveGround

end



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalNumbers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem omega_subset_inductive (I : ZFSet.{u}) (empty : (∅ : ZFSet.{u}) ∈ I)
    (successor : ∀ x ∈ I, insert x x ∈ I) : ZFSet.omega ⊆ I := by
  intro x hx
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
  clear hx
  induction n with
  | zero => exact empty
  | succ n ih => exact successor (natSetCode n) ih

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem omega_mem (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : ZFSet.omega ∈ M.sets := by
  obtain ⟨I, hI, empty, successor⟩ := M.infinity_witness infinite
  have subset := omega_subset_inductive I empty successor
  have selected := M.separation_mem separation (BoundedFormula.naturalFormula 0).toFormula
    Fin.elim0 (fun i => Fin.elim0 i) hI
  have eq : ZFSet.sep (fun x => Realize M.sets (BoundedFormula.naturalFormula 0).toFormula
      (extend x Fin.elim0)) I = ZFSet.omega := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, rel⟩
      exact (BoundedFormula.realize_naturalFormula M 0 (extend x Fin.elim0)
        (Fin.cases (M.transitive hI hx) (fun i => Fin.elim0 i))).1 rel
    · intro hx
      have hxI := subset hx
      exact ⟨hxI, (BoundedFormula.realize_naturalFormula M 0 (extend x Fin.elim0)
        (Fin.cases (M.transitive hI hxI) (fun i => Fin.elim0 i))).2 hx⟩
  exact eq ▸ selected

theorem natSetCode_mem (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (n : Nat) : natSetCode n ∈ M.sets :=
  M.transitive (M.omega_mem separation infinite) (natSetCode_mem_omega n)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundSuccessorInjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem setSuccessor_injective : Function.Injective (fun x : ZFSet.{u} => insert x x) := by
  intro x y eq
  change insert x x = insert y y at eq
  have xy : x = y ∨ x ∈ y := ZFSet.mem_insert_iff.1 (eq ▸ ZFSet.mem_insert x x)
  have yx : y = x ∨ y ∈ x := ZFSet.mem_insert_iff.1 (eq.symm ▸ ZFSet.mem_insert y y)
  rcases xy with eq | xy
  · exact eq
  · rcases yx with eq | yx
    · exact eq.symm
    · exact False.elim (ZFSet.mem_asymm xy yx)

theorem setSuccessor_ne_empty (x : ZFSet.{u}) : insert x x ≠ (∅ : ZFSet.{u}) := by
  intro eq
  exact ZFSet.notMem_empty x (eq ▸ ZFSet.mem_insert x x)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem insert_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {a D : ZFSet.{u}} (ha : a ∈ M.sets) (hD : D ∈ M.sets) : insert a D ∈ M.sets := by
  have single : ({a} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha
  have joined := M.binary_union_mem pairing unions single hD
  have eq : ({a} : ZFSet.{u}) ∪ D = insert a D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union, ZFSet.mem_singleton, ZFSet.mem_insert_iff]
  exact eq ▸ joined

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedSumPresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem natSetCode_injective : Function.Injective (natSetCode : Nat → ZFSet.{u}) := by
  intro m n eq
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => exact False.elim (setSuccessor_ne_empty (natSetCode n) eq.symm)
  | succ m ih =>
    cases n with
    | zero => exact False.elim (setSuccessor_ne_empty (natSetCode m) eq)
    | succ n => exact congrArg Nat.succ (ih (setSuccessor_injective eq))

theorem natSetCode_mem_iff (m n : Nat) : natSetCode m ∈ natSetCode n ↔ m < n := by
  induction n with
  | zero =>
    exact ⟨fun h => False.elim (ZFSet.notMem_empty _ h), fun h => False.elim (Nat.not_lt_zero m h)⟩
  | succ n ih =>
    rw [natSetCode_succ, ZFSet.mem_insert_iff, natSetCode_injective.eq_iff, ih]
    omega

theorem mem_natSetCode (x : ZFSet.{u}) (n : Nat) :
    x ∈ natSetCode n ↔ ∃ m < n, x = natSetCode m := by
  constructor
  · intro hx
    have natural := naturalSetProperty_member ((naturalSetProperty_iff (natSetCode n)).2 ⟨n, rfl⟩) hx
    obtain ⟨m, eq⟩ := (naturalSetProperty_iff x).1 natural
    exact ⟨m, (natSetCode_mem_iff m n).1 (eq ▸ hx), eq⟩
  · rintro ⟨m, hm, rfl⟩
    exact (natSetCode_mem_iff m n).2 hm

def natPresentation : Presentation (ULift.{u} Nat) where
  carrier := ZFSet.omega
  encode n := natSetCode n.down
  injective := fun _ _ eq => ULift.ext _ _ (natSetCode_injective eq)
  mem_carrier x := by
    rw [mem_omega_iff_natSetCode]
    exact ⟨fun ⟨n, eq⟩ => ⟨⟨n⟩, eq.symm⟩, fun ⟨n, eq⟩ => ⟨n.down, eq.symm⟩⟩

def natInitialPresentation (n : Nat) : Presentation (ULift.{u} (Fin n)) where
  carrier := natSetCode n
  encode i := natSetCode i.down.val
  injective := fun _ _ eq => ULift.ext _ _ (Fin.ext (natSetCode_injective eq))
  mem_carrier x := by
    rw [mem_natSetCode]
    exact ⟨fun ⟨m, hm, eq⟩ => ⟨⟨⟨m, hm⟩⟩, eq.symm⟩,
      fun ⟨m, eq⟩ => ⟨m.down.val, m.down.isLt, eq.symm⟩⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})

noncomputable def finiteWords (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun f => ∃ n ∈ ZFSet.omega, ZFSet.IsFunc n A f)
    (M.groundRelations ZFSet.omega A)

theorem mem_finiteWords_iff (A f : ZFSet.{u}) :
    f ∈ M.finiteWords A ↔ f ∈ M.sets ∧ ∃ n ∈ ZFSet.omega, ZFSet.IsFunc n A f := by
  rw [finiteWords, ZFSet.mem_sep, M.mem_groundRelations]
  constructor
  · exact fun ⟨⟨ground, _⟩, code⟩ => ⟨ground, code⟩
  · rintro ⟨ground, n, hn, function⟩
    refine ⟨⟨ground, ?_⟩, n, hn, function⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    obtain ⟨j, _, rfl⟩ := (mem_natSetCode x k).1 hx
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega j, hy⟩

theorem mem_finiteWords (A f : ZFSet.{u}) :
    f ∈ M.finiteWords A ↔
      f ∈ M.sets ∧ ∃ n : Nat, ZFSet.IsFunc (natSetCode n) A f := by
  rw [M.mem_finiteWords_iff]
  constructor
  · rintro ⟨ground, n, hn, function⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ⟨ground, k, function⟩
  · rintro ⟨ground, n, function⟩
    exact ⟨ground, natSetCode n, natSetCode_mem_omega n, function⟩

end TransitiveGround

end PartitionPilot.Forcing


section

namespace PartitionPilot.Compression.RecursiveMaps.RationalHeights.Fraction

theorem intCode_surjective : Function.Surjective intCode := by
  intro n
  by_cases even : n % 2 = 0
  · exact ⟨Int.ofNat (n / 2), by simp only [intCode]; omega⟩
  · exact ⟨Int.negSucc (n / 2), by simp only [intCode]; omega⟩

end PartitionPilot.Compression.RecursiveMaps.RationalHeights.Fraction

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundCountableQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def canonicalRepresentativeFormula {n} (x s e c omega : Fin n) : BoundedFormula n :=
  exMem omega (.conj (pairMembershipFormula x.succ 0 c.succ)
    (.allMem s.succ (imp (pairMembershipFormula x.succ.succ 0 e.succ.succ)
      (.allMem 1 (.neg (pairMembershipFormula 1 0 c.succ.succ.succ))))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_StageOneDataBoundLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def stageOneAssignment (t u w : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair t (ZFSet.pair u w)

noncomputable def stageOneAssignments (I T : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod I (ZFSet.prod T T)

namespace BoundedFormula

def stageOneAssignmentFormula {n : Nat} (z t u w : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 2 z ![t, u, w]

end BoundedFormula

end

open SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementPairClassGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula
universe u v
variable (M : TransitiveGround.{u})

theorem finite_set_code
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    {S : Set ZFSet.{u}} (finite : S.Finite) :
    S ⊆ M.sets → ∃ D ∈ M.sets, D.toSet = S := by
  induction S, finite using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨∅, M.empty_mem nonempty, ZFSet.coe_empty⟩
  | @insert a S fresh finite ih =>
    intro members
    obtain ⟨D, hD, eq⟩ := ih (fun _ hx => members (Set.mem_insert_of_mem _ hx))
    refine ⟨insert a D, M.insert_mem pairing unions (members (Set.mem_insert a S)) hD, ?_⟩
    exact (ZFSet.coe_insert a D).trans (congrArg (insert a) eq)

theorem finite_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    {D : ZFSet.{u}} (finite : D.toSet.Finite) (members : ∀ x ∈ D, x ∈ M.sets) : D ∈ M.sets := by
  obtain ⟨E, hE, eq⟩ := M.finite_set_code pairing unions nonempty finite (fun x hx => members x hx)
  exact SetLike.coe_injective (show (E : Set ZFSet) = (D : Set ZFSet) from eq) ▸ hE

theorem finite_range_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (nonempty : M.sets.Nonempty)
    {A : Type v} [Finite A] [Small.{u} A] (f : A → ZFSet.{u}) (members : ∀ a, f a ∈ M.sets) :
    ZFSet.range f ∈ M.sets := by
  apply M.finite_mem pairing unions nonempty
  · change (ZFSet.range f : Set ZFSet).Finite
    rw [ZFSet.coe_range]
    simpa only [Set.image_univ] using Set.finite_univ.image f
  · intro x hx
    obtain ⟨a, rfl⟩ := ZFSet.mem_range.1 hx
    exact members a

theorem finite_function_graph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {A B : Type u} [Finite A] (s : Presentation A) (t : Presentation B) (f : A → B)
    (hA : s.carrier ∈ M.sets) (hB : t.carrier ∈ M.sets) : s.graph t f ∈ M.sets := by
  have ground := M.finite_range_mem pairing unions ⟨s.carrier, hA⟩
    (fun a => ZFSet.pair (s.encode a) (t.encode (f a)))
    (fun a => M.orderedPair_mem pairing (M.transitive hA (s.encode_mem a))
      (M.transitive hB (t.encode_mem (f a))))
  have eq : ZFSet.range (fun a => ZFSet.pair (s.encode a) (t.encode (f a))) = s.graph t f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range, s.mem_graph]
  exact eq ▸ ground

end TransitiveGround



open SetRealization SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteIterationTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u

structure IterationTraceCode (N D B step base t : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc D B t
  seed : ZFSet.pair ∅ base ∈ t
  next : ∀ i ∈ N, ∀ j ∈ D, ∀ x ∈ B, ∀ y ∈ B,
    j = insert i i → ZFSet.pair i x ∈ t → ZFSet.pair j y ∈ t → ZFSet.pair x y ∈ step

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FiniteWordMapCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization
universe u
variable {B : Type u} (s : Presentation B)

noncomputable def finiteWordGraph (xs : List B) : ZFSet.{u} :=
  (natInitialPresentation xs.length).graph s (fun i => xs.get i.down)

theorem finiteWordGraph_function (xs : List B) :
    ZFSet.IsFunc (natSetCode xs.length) s.carrier (finiteWordGraph s xs) :=
  (natInitialPresentation xs.length).graph_isFunc s _

theorem mem_finiteWordGraph (xs : List B) (z : ZFSet.{u}) :
    z ∈ finiteWordGraph s xs ↔
      ∃ i : Fin xs.length, z = ZFSet.pair (natSetCode i.val) (s.encode (xs.get i)) := by
  rw [finiteWordGraph, Presentation.mem_graph]
  exact ⟨fun ⟨i, eq⟩ => ⟨i.down, eq.symm⟩, fun ⟨i, eq⟩ => ⟨⟨i⟩, eq.symm⟩⟩

theorem pair_mem_finiteWordGraph (xs : List B) (k : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode k) y ∈ finiteWordGraph s xs ↔
      ∃ h : k < xs.length, y = s.encode (xs.get ⟨k, h⟩) := by
  rw [mem_finiteWordGraph]
  constructor
  · rintro ⟨i, eq⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    have same : k = i.val := natSetCode_injective first
    subst k
    exact ⟨i.isLt, second⟩
  · rintro ⟨h, eq⟩
    exact ⟨⟨k, h⟩, congrArg (ZFSet.pair (natSetCode k)) eq⟩

namespace TransitiveGround
open SetFormula

theorem finiteWordGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (xs : List B) (hB : s.carrier ∈ M.sets) : finiteWordGraph s xs ∈ M.sets :=
  M.finite_function_graph_mem pairing unions (natInitialPresentation xs.length) s _
    (M.natSetCode_mem separation infinite xs.length) hB

end TransitiveGround

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (hB : s.carrier ∈ M.sets)

include pairing unions separation infinite hB
theorem finiteWordGraph_mem_finiteWords (xs : List B) :
    finiteWordGraph s xs ∈ M.finiteWords s.carrier :=
  (M.mem_finiteWords s.carrier _).2
    ⟨finiteWordGraph_mem s M pairing unions separation infinite xs hB,
      xs.length, finiteWordGraph_function s xs⟩

end TransitiveGround

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCoinitialOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

open SetFormula

def coinitialBelowFormula {n} (order F target B : Fin n) : BoundedFormula n :=
  .conj (.allMem B (.mem 0 F.succ))
    (.allMem target (exMem B.succ (pairMembershipFormula 0 1 order.succ.succ)))

end BoundedFormula

namespace BoundedFormula

open SetFormula

def fiberCoveredFormula {n} (order target parts i B : Fin n) : BoundedFormula n :=
  .allMem target (imp (pairMembershipFormula i.succ 0 parts.succ)
    (exMem B.succ (pairMembershipFormula 0 1 order.succ.succ)))

def basisChoiceEntryFormula {n} (z I W order target parts : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (fiberCoveredFormula order.succ.succ target.succ.succ parts.succ.succ 1 0)))

end BoundedFormula

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalBasis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def birthEssentialFormula {n} (x f t r birth : Fin n) : BoundedFormula n :=
  .allMem f (.allMem t.succ (.allMem t.succ.succ
    (imp (.conj (pairMembershipFormula 2 x.succ.succ.succ r.succ.succ.succ)
      (.conj (pairMembershipFormula 2 1 birth.succ.succ.succ)
        (pairMembershipFormula x.succ.succ.succ 0 birth.succ.succ.succ))) (.neg (.mem 1 0)))))

end BoundedFormula

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageFromCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

structure MeetOrderCode (L r μ : ZFSet.{u}) : Prop where
  order : PartialOrderCode L r
  operation : ZFSet.IsFunc (ZFSet.prod L L) L μ
  lower_left : ∀ x y z, ZFSet.pair (ZFSet.pair x y) z ∈ μ → ZFSet.pair z x ∈ r
  lower_right : ∀ x y z, ZFSet.pair (ZFSet.pair x y) z ∈ μ → ZFSet.pair z y ∈ r
  greatest : ∀ x y z w, w ∈ L → ZFSet.pair (ZFSet.pair x y) z ∈ μ →
    ZFSet.pair w x ∈ r → ZFSet.pair w y ∈ r → ZFSet.pair w z ∈ r

structure MeetFilterCode (L r μ F : ZFSet.{u}) : Prop where
  subset : F ⊆ L
  nonempty : F.Nonempty
  upward : ∀ x ∈ F, ∀ y ∈ L, ZFSet.pair x y ∈ r → y ∈ F
  closed_meet : ∀ x ∈ F, ∀ y ∈ F, ∀ z,
    ZFSet.pair (ZFSet.pair x y) z ∈ μ → z ∈ F

structure StrictLexHeightCode (L C Q r height qlt : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc L (ZFSet.prod C Q) height
  strict : ∀ x ∈ L, ∀ y ∈ L, ∀ c q d v,
    ZFSet.pair x y ∈ r → x ≠ y →
      ZFSet.pair x (ZFSet.pair c q) ∈ height →
        ZFSet.pair y (ZFSet.pair d v) ∈ height →
          c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ qlt)

end



section

universe u v

def OldBridgeCode (L r μ birth t x y : ZFSet.{u}) : Prop :=
  (∃ z a, ZFSet.pair (ZFSet.pair x y) z ∈ μ ∧ ZFSet.pair z a ∈ birth ∧ a ∈ t) ∨
  (∃ z ∈ L, ∃ a, ZFSet.pair z a ∈ birth ∧ a ∈ t ∧
    ((ZFSet.pair x z ∈ r ∧ ZFSet.pair z y ∈ r) ∨
      (ZFSet.pair y z ∈ r ∧ ZFSet.pair z x ∈ r)))

end



section
universe u

structure GroundMainStage (M : TransitiveGround.{u}) (C D rD : ZFSet.{u}) where
  carrier : ZFSet.{u}
  order : ZFSet.{u}
  meetGraph : ZFSet.{u}
  actors : ZFSet.{u}
  multiplication : ZFSet.{u}
  inverse : ZFSet.{u}
  identity : ZFSet.{u}
  action : ZFSet.{u}
  bottom : ZFSet.{u}
  top : ZFSet.{u}
  height : ZFSet.{u}
  carrier_ground : carrier ∈ M.sets
  order_ground : order ∈ M.sets
  meet_ground : meetGraph ∈ M.sets
  actors_ground : actors ∈ M.sets
  multiplication_ground : multiplication ∈ M.sets
  inverse_ground : inverse ∈ M.sets
  action_ground : action ∈ M.sets
  height_ground : height ∈ M.sets
  columns_ground : C ∈ M.sets
  coordinates_ground : D ∈ M.sets
  coordinate_order_ground : rD ∈ M.sets
  meet : MeetOrderCode carrier order meetGraph
  group_code : GroupCode actors multiplication inverse identity
  action_code : PosetActionCode actors carrier multiplication identity order action
  bottom_mem : bottom ∈ carrier
  least : ∀ x ∈ carrier, ZFSet.pair bottom x ∈ order
  top_mem : top ∈ carrier
  greatest : ∀ x ∈ carrier, ZFSet.pair x top ∈ order
  height_code : StrictLexHeightCode carrier C D order height rD
  height_range_ground : relationImage carrier (ZFSet.prod C D) height ∈ M.sets
  height_range_countable : M.groundEmbeddable (relationImage carrier (ZFSet.prod C D) height) ZFSet.omega





noncomputable def taggedBirth (P N birth stamp : ZFSet.{u}) : ZFSet.{u} :=
  birth ∪ ZFSet.prod (ZFSet.prod {P} N) {stamp}

theorem pair_mem_taggedBirth (P N birth stamp x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ taggedBirth P N birth stamp ↔
      ZFSet.pair x t ∈ birth ∨ (x ∈ ZFSet.prod {P} N ∧ t = stamp) := by
  rw [taggedBirth, ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem taggedBirth_subset (P N birth stamp : ZFSet.{u}) : birth ⊆ taggedBirth P N birth stamp :=
  fun _ hx => ZFSet.mem_union.2 (Or.inl hx)

theorem taggedBirth_stamp_iff {P N birth stamp x : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp) :
    ZFSet.pair x stamp ∈ taggedBirth P N birth stamp ↔ x ∈ ZFSet.prod {P} N := by
  rw [pair_mem_taggedBirth]
  exact ⟨fun h => h.elim (fun old => False.elim (ZFSet.mem_irrefl stamp (earlier x stamp old))) And.left,
    fun hx => Or.inr ⟨hx, rfl⟩⟩

namespace GroundMainStage
open SetFormula
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

@[ext] theorem ext {first second : GroundMainStage M C D rD}
    (carrier : first.carrier = second.carrier)
    (order : first.order = second.order)
    (meetGraph : first.meetGraph = second.meetGraph)
    (actors : first.actors = second.actors)
    (multiplication : first.multiplication = second.multiplication)
    (inverse : first.inverse = second.inverse)
    (identity : first.identity = second.identity)
    (action : first.action = second.action)
    (bottom : first.bottom = second.bottom)
    (top : first.top = second.top)
    (height : first.height = second.height) : first = second := by
  cases first
  cases second
  cases carrier
  cases order
  cases meetGraph
  cases actors
  cases multiplication
  cases inverse
  cases identity
  cases action
  cases bottom
  cases top
  cases height
  rfl

end GroundMainStage

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IndexedAttachmentCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

noncomputable def attachmentIdeal (Q rQ a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun q => ZFSet.pair q a ∈ rQ) Q

noncomputable def freshPart (Q rQ a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun q => ZFSet.pair q a ∉ rQ) Q

theorem mem_attachmentIdeal (Q rQ a q : ZFSet.{u}) :
    q ∈ attachmentIdeal Q rQ a ↔ q ∈ Q ∧ ZFSet.pair q a ∈ rQ :=
  ZFSet.mem_sep

theorem mem_freshPart (Q rQ a q : ZFSet.{u}) :
    q ∈ freshPart Q rQ a ↔ q ∈ Q ∧ ZFSet.pair q a ∉ rQ :=
  ZFSet.mem_sep

theorem attachmentIdeal_not_freshPart {Q rQ a q : ZFSet.{u}}
    (hq : q ∈ attachmentIdeal Q rQ a) : q ∉ freshPart Q rQ a := by
  intro fresh
  exact ((mem_freshPart Q rQ a q).1 fresh).2 ((mem_attachmentIdeal Q rQ a q).1 hq).2

noncomputable def attachmentShadowGraph (Q P μQ ell a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ q ∈ Q, ∃ p ∈ P, z = ZFSet.pair q p ∧
    ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μQ ∧ ZFSet.pair c p ∈ ell)
    (ZFSet.prod Q P)

theorem mem_attachmentShadowGraph (Q P μQ ell a z : ZFSet.{u}) :
    z ∈ attachmentShadowGraph Q P μQ ell a ↔
      ∃ q ∈ Q, ∃ p ∈ P, z = ZFSet.pair q p ∧
        ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μQ ∧ ZFSet.pair c p ∈ ell := by
  rw [attachmentShadowGraph, ZFSet.mem_sep]
  exact ⟨And.right, fun h => ⟨by
    obtain ⟨q, hq, p, hp, rfl, _⟩ := h
    exact ZFSet.pair_mem_prod.2 ⟨hq, hp⟩, h⟩⟩

theorem pair_mem_attachmentShadowGraph (Q P μQ ell a q p : ZFSet.{u}) :
    ZFSet.pair q p ∈ attachmentShadowGraph Q P μQ ell a ↔
      q ∈ Q ∧ p ∈ P ∧
        ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μQ ∧ ZFSet.pair c p ∈ ell := by
  rw [mem_attachmentShadowGraph]
  constructor
  · rintro ⟨q', hq, p', hp, equal, c, hc, meet, image⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hq, hp, c, hc, meet, image⟩
  · rintro ⟨hq, hp, c, hc, meet, image⟩
    exact ⟨q, hq, p, hp, rfl, c, hc, meet, image⟩

theorem meet_entry_in_attachmentIdeal {Q rQ μQ a q c : ZFSet.{u}}
    (meet : MeetOrderCode Q rQ μQ)
    (entry : ZFSet.pair (ZFSet.pair q a) c ∈ μQ) :
    c ∈ attachmentIdeal Q rQ a :=
  (mem_attachmentIdeal Q rQ a c).2
    ⟨(ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2, meet.lower_right q a c entry⟩

theorem attachmentShadowGraph_function {Q P rQ μQ ell a : ZFSet.{u}}
    (meet : MeetOrderCode Q rQ μQ) (ha : a ∈ Q)
    (ellFunc : ZFSet.IsFunc (attachmentIdeal Q rQ a) P ell) :
    ZFSet.IsFunc Q P (attachmentShadowGraph Q P μQ ell a) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro q hq
  obtain ⟨c, entry, meetUnique⟩ := meet.operation.2 (ZFSet.pair q a)
    (ZFSet.pair_mem_prod.2 ⟨hq, ha⟩)
  have hc := meet_entry_in_attachmentIdeal meet entry
  obtain ⟨p, image, imageUnique⟩ := ellFunc.2 c hc
  have hp := (ZFSet.pair_mem_prod.1 (ellFunc.1 image)).2
  refine ⟨p, (pair_mem_attachmentShadowGraph Q P μQ ell a q p).2
    ⟨hq, hp, c, ((mem_attachmentIdeal Q rQ a c).1 hc).1, entry, image⟩, ?_⟩
  intro p' shadow
  obtain ⟨_, _, c', _, entry', image'⟩ :=
    (pair_mem_attachmentShadowGraph Q P μQ ell a q p').1 shadow
  have equal := meetUnique c' entry'
  subst c'
  exact imageUnique p' image'

def familyPointBound (Qs : ZFSet.{u}) : ZFSet.{u} := ⋃₀ ⋃₀ ⋃₀ Qs

theorem mem_familyPointBound_of_entry {Qs i Q q : ZFSet.{u}}
    (entry : ZFSet.pair i Q ∈ Qs) (hq : q ∈ Q) : q ∈ familyPointBound Qs :=
  ZFSet.mem_sUnion.2 ⟨Q, pair_second_mem_doubleUnion entry, hq⟩

noncomputable def indexedAttachmentDomain (I Qs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ q ∈ Q,
    ZFSet.pair i Q ∈ Qs ∧ z = ZFSet.pair i q)
    (ZFSet.prod I (familyPointBound Qs))

noncomputable def indexedAttachmentFresh (I Qs rs anchors : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ⋃₀ ⋃₀ Qs, ∃ r ∈ ⋃₀ ⋃₀ rs,
    ∃ a ∈ ⋃₀ ⋃₀ anchors, ∃ q ∈ Q,
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ ZFSet.pair i a ∈ anchors ∧
      z = ZFSet.pair i q ∧ ZFSet.pair q a ∉ r)
    (indexedAttachmentDomain I Qs)

theorem indexedAttachmentDomain_subset (I Qs : ZFSet.{u}) :
    indexedAttachmentDomain I Qs ⊆ ZFSet.prod I (familyPointBound Qs) :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem indexedAttachmentFresh_subset (I Qs rs anchors : ZFSet.{u}) :
    indexedAttachmentFresh I Qs rs anchors ⊆ indexedAttachmentDomain I Qs :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_indexedAttachmentDomain (I Qs z : ZFSet.{u}) :
    z ∈ indexedAttachmentDomain I Qs ↔
      ∃ i ∈ I, ∃ q, z = ZFSet.pair i q ∧ ∃ Q, ZFSet.pair i Q ∈ Qs ∧ q ∈ Q := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, q, hq, entry, equal⟩ := (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, q, equal, Q, entry, hq⟩
  · rintro ⟨i, hi, q, rfl, Q, entry, hq⟩
    exact ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hi, mem_familyPointBound_of_entry entry hq⟩,
        i, hi, Q, pair_second_mem_doubleUnion entry, q, hq, entry, rfl⟩

theorem pair_mem_indexedAttachmentDomain (I Qs i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ indexedAttachmentDomain I Qs ↔
      i ∈ I ∧ ∃ Q, ZFSet.pair i Q ∈ Qs ∧ q ∈ Q := by
  rw [mem_indexedAttachmentDomain]
  constructor
  · rintro ⟨j, hj, p, equal, Q, entry, hq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, Q, entry, hq⟩
  · rintro ⟨hi, Q, entry, hq⟩
    exact ⟨i, hi, q, rfl, Q, entry, hq⟩

theorem mem_indexedAttachmentFresh (I Qs rs anchors z : ZFSet.{u}) :
    z ∈ indexedAttachmentFresh I Qs rs anchors ↔
      ∃ i ∈ I, ∃ q, z = ZFSet.pair i q ∧ ∃ Q r a,
        ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ ZFSet.pair i a ∈ anchors ∧
        q ∈ Q ∧ ZFSet.pair q a ∉ r := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, r, _, a, _, q, hq, entryQ, entryR, entryA, equal, fresh⟩ :=
      (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, q, equal, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
  · rintro ⟨i, hi, q, rfl, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
    exact ZFSet.mem_sep.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, entryQ, hq⟩,
        i, hi, Q, pair_second_mem_doubleUnion entryQ, r, pair_second_mem_doubleUnion entryR,
        a, pair_second_mem_doubleUnion entryA, q, hq, entryQ, entryR, entryA, rfl, fresh⟩

theorem pair_mem_indexedAttachmentFresh (I Qs rs anchors i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ indexedAttachmentFresh I Qs rs anchors ↔
      i ∈ I ∧ ∃ Q r a, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧
        ZFSet.pair i a ∈ anchors ∧ q ∈ Q ∧ ZFSet.pair q a ∉ r := by
  rw [mem_indexedAttachmentFresh]
  constructor
  · rintro ⟨j, hj, p, equal, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
  · rintro ⟨hi, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩
    exact ⟨i, hi, q, rfl, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩

theorem pair_mem_indexedAttachmentDomain_of_entry {I Qs i q Q : ZFSet.{u}}
    (family : FunctionGraphOn I Qs) (entry : ZFSet.pair i Q ∈ Qs) :
    ZFSet.pair i q ∈ indexedAttachmentDomain I Qs ↔ q ∈ Q := by
  rw [pair_mem_indexedAttachmentDomain]
  constructor
  · rintro ⟨_, R, other, hq⟩
    exact family.unique other entry ▸ hq
  · intro hq
    exact ⟨family.pair_source entry, Q, entry, hq⟩

theorem pair_mem_indexedAttachmentFresh_of_entries
    {I Qs rs anchors i q Q r a : ZFSet.{u}}
    (spaces : FunctionGraphOn I Qs) (orders : FunctionGraphOn I rs)
    (points : FunctionGraphOn I anchors) (entryQ : ZFSet.pair i Q ∈ Qs)
    (entryR : ZFSet.pair i r ∈ rs) (entryA : ZFSet.pair i a ∈ anchors) :
    ZFSet.pair i q ∈ indexedAttachmentFresh I Qs rs anchors ↔ q ∈ freshPart Q r a := by
  rw [pair_mem_indexedAttachmentFresh, mem_freshPart]
  constructor
  · rintro ⟨_, Q', r', a', otherQ, otherR, otherA, hq, fresh⟩
    have equalQ := spaces.unique otherQ entryQ
    have equalR := orders.unique otherR entryR
    have equalA := points.unique otherA entryA
    subst Q'
    subst r'
    subst a'
    exact ⟨hq, fresh⟩
  · rintro ⟨hq, fresh⟩
    exact ⟨spaces.pair_source entryQ, Q, r, a, entryQ, entryR, entryA, hq, fresh⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NaturalStepFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

def graphRestrictionFormula {n} (p a b f : Fin n) : BoundedFormula n :=
  .conj (.allMem p (.conj (.mem 0 f.succ) (productElementFormula 0 a.succ b.succ)))
    (.allMem f (imp (productElementFormula 0 a.succ b.succ) (.mem 0 p.succ)))

end BoundedFormula

end




open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFilterCopies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

structure MeetEmbeddingCode (A L rA rL μA μL e : ZFSet.{u}) : Prop where
  injection : InjectionCode A L e
  monotone : ∀ x y x' y', ZFSet.pair x y ∈ rA →
    ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ rL
  map_meet : ∀ x y z x' y' z', ZFSet.pair (ZFSet.pair x y) z ∈ μA →
    ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair z z' ∈ e →
      ZFSet.pair (ZFSet.pair x' y') z' ∈ μL

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAttachmentEmbeddings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem taggedExtension_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N : ZFSet.{u}} (hP : P ∈ M.sets) (hN : N ∈ M.sets) :
    taggedExtension P N ∈ M.sets := by
  have singleton : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact M.binary_union_mem pairing unions hP
    (M.prod_mem pairing unions powers separation singleton hN)

end TransitiveGround




universe u






noncomputable def attachmentOldEmbeddingGraph (P : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ P, z = ZFSet.pair x x) (ZFSet.prod P P)

theorem mem_attachmentOldEmbeddingGraph (P z : ZFSet.{u}) :
    z ∈ attachmentOldEmbeddingGraph P ↔ ∃ x ∈ P, z = ZFSet.pair x x := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨x, hx, rfl⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hx⟩, x, hx, rfl⟩

theorem pair_mem_attachmentOldEmbeddingGraph (P x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ attachmentOldEmbeddingGraph P ↔ x ∈ P ∧ y = x := by
  rw [mem_attachmentOldEmbeddingGraph]
  constructor
  · rintro ⟨z, hz, eq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hz, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨_, hx, rfl⟩

theorem attachmentOldEmbeddingGraph_isFunc (P N : ZFSet.{u}) :
    ZFSet.IsFunc P (taggedExtension P N) (attachmentOldEmbeddingGraph P) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_attachmentOldEmbeddingGraph P z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, old_mem_taggedExtension hx⟩
  · intro x hx
    exact ⟨x, (pair_mem_attachmentOldEmbeddingGraph P x x).2 ⟨hx, rfl⟩,
      fun y hy => ((pair_mem_attachmentOldEmbeddingGraph P x y).1 hy).2⟩






namespace BoundedFormula

open SetFormula

def attachmentOldEmbeddingEntryFormula {n} (z p : Fin n) : BoundedFormula n :=
  exMem p (orderedPairFormula z.succ 0 0)

end BoundedFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FixedTopCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

def GreatestLowerBoundCode (L r x y z : ZFSet.{u}) : Prop :=
  ZFSet.pair z x ∈ r ∧ ZFSet.pair z y ∈ r ∧
    ∀ w ∈ L, ZFSet.pair w x ∈ r → ZFSet.pair w y ∈ r → ZFSet.pair w z ∈ r

noncomputable def canonicalMeetGraph (L r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => ∃ x ∈ L, ∃ y ∈ L, ∃ z ∈ L,
    v = ZFSet.pair (ZFSet.pair x y) z ∧ GreatestLowerBoundCode L r x y z)
    (ZFSet.prod (ZFSet.prod L L) L)

theorem canonicalMeetGraph_subset (L r : ZFSet.{u}) :
    canonicalMeetGraph L r ⊆ ZFSet.prod (ZFSet.prod L L) L := by
  intro v hv
  exact (ZFSet.mem_sep.1 hv).1

theorem mem_canonicalMeetGraph (L r v : ZFSet.{u}) :
    v ∈ canonicalMeetGraph L r ↔ ∃ x ∈ L, ∃ y ∈ L, ∃ z ∈ L,
      v = ZFSet.pair (ZFSet.pair x y) z ∧ GreatestLowerBoundCode L r x y z := by
  constructor
  · intro hv
    exact (ZFSet.mem_sep.1 hv).2
  · intro h
    obtain ⟨x, hx, y, hy, z, hz, eq, glb⟩ := h
    subst v
    exact ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, hz⟩,
        x, hx, y, hy, z, hz, rfl, glb⟩

theorem pair_mem_canonicalMeetGraph (L r x y z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair x y) z ∈ canonicalMeetGraph L r ↔
      x ∈ L ∧ y ∈ L ∧ z ∈ L ∧ GreatestLowerBoundCode L r x y z := by
  rw [mem_canonicalMeetGraph]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, eq, h⟩
    have outer := ZFSet.pair_inj.1 eq
    have inner := ZFSet.pair_inj.1 outer.1
    rcases inner with ⟨rfl, rfl⟩
    rcases outer.2 with rfl
    exact ⟨ha, hb, hc, h⟩
  · rintro ⟨hx, hy, hz, h⟩
    exact ⟨x, hx, y, hy, z, hz, rfl, h⟩

theorem GreatestLowerBoundCode.unique {L r x y z w : ZFSet.{u}}
    (order : PartialOrderCode L r) (hz : z ∈ L) (hw : w ∈ L)
    (left : GreatestLowerBoundCode L r x y z)
    (right : GreatestLowerBoundCode L r x y w) : z = w := by
  exact order.antisymm z hz w hw (right.2.2 z hz left.1 left.2.1)
    (left.2.2 w hw right.1 right.2.1)

theorem canonicalMeetGraph_code {L r : ZFSet.{u}} (order : PartialOrderCode L r)
    (existsGLB : ∀ x ∈ L, ∀ y ∈ L, ∃ z ∈ L, GreatestLowerBoundCode L r x y z) :
    MeetOrderCode L r (canonicalMeetGraph L r) := by
  refine ⟨order, ⟨canonicalMeetGraph_subset L r, ?_⟩, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ha
    obtain ⟨z, hz, h⟩ := existsGLB x hx y hy
    refine ⟨z, (pair_mem_canonicalMeetGraph L r x y z).2 ⟨hx, hy, hz, h⟩, ?_⟩
    intro w hw
    have other := (pair_mem_canonicalMeetGraph L r x y w).1 hw
    exact GreatestLowerBoundCode.unique order other.2.2.1 hz other.2.2.2 h
  · intro x y z h
    exact ((pair_mem_canonicalMeetGraph L r x y z).1 h).2.2.2.1
  · intro x y z h
    exact ((pair_mem_canonicalMeetGraph L r x y z).1 h).2.2.2.2.1
  · intro x y z w hw h hleft hright
    exact ((pair_mem_canonicalMeetGraph L r x y z).1 h).2.2.2.2.2 w hw hleft hright

namespace MeetOrderCode

noncomputable def meetValue {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ)
    (x y : {a : ZFSet.{u} // a ∈ L}) : {a : ZFSet.{u} // a ∈ L} :=
  let witness := code.operation.2 (ZFSet.pair x.val y.val)
    (ZFSet.pair_mem_prod.2 ⟨x.property, y.property⟩)
  ⟨Classical.choose witness,
    (ZFSet.pair_mem_prod.1 (code.operation.1 (Classical.choose_spec witness).1)).2⟩

theorem meetValue_entry {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ)
    (x y : {a : ZFSet.{u} // a ∈ L}) :
    ZFSet.pair (ZFSet.pair x.val y.val) (code.meetValue x y).val ∈ μ :=
  (Classical.choose_spec (code.operation.2 (ZFSet.pair x.val y.val)
    (ZFSet.pair_mem_prod.2 ⟨x.property, y.property⟩))).1

noncomputable def toMeetOrder {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    PartitionPilot.MeetOrder {a : ZFSet.{u} // a ∈ L} where
  le x y := ZFSet.pair x.val y.val ∈ r
  meet := code.meetValue
  refl x := code.order.refl x.val x.property
  trans {x y z} := code.order.trans x.val x.property y.val y.property z.val z.property
  antisymm {x y} hxy hyx := Subtype.ext (code.order.antisymm x.val x.property y.val y.property hxy hyx)
  meet_le_left x y := code.lower_left x.val y.val _ (code.meetValue_entry x y)
  meet_le_right x y := code.lower_right x.val y.val _ (code.meetValue_entry x y)
  le_meet {x y z} := code.greatest y.val z.val _ x.val x.property (code.meetValue_entry y z)

theorem toMeetOrder_meet_entry {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ)
    (x y : {a : ZFSet.{u} // a ∈ L}) :
    ZFSet.pair (ZFSet.pair x.val y.val) (code.toMeetOrder.meet x y).val ∈ μ :=
  code.meetValue_entry x y

end MeetOrderCode

noncomputable def fixedTopCarrier (P : ZFSet.{u}) : ZFSet.{u} := insert P P

noncomputable def fixedTopOrder (P r : ZFSet.{u}) : ZFSet.{u} :=
  r ∪ ZFSet.prod (fixedTopCarrier P) {P}

theorem pair_mem_fixedTopOrder (P r x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ fixedTopOrder P r ↔
      ZFSet.pair x y ∈ r ∨ (x ∈ fixedTopCarrier P ∧ y = P) := by
  rw [fixedTopOrder, ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem fixedTopOrder_old_iff {P r x y : ZFSet.{u}} (hy : y ∈ P) :
    ZFSet.pair x y ∈ fixedTopOrder P r ↔ ZFSet.pair x y ∈ r := by
  rw [pair_mem_fixedTopOrder]
  constructor
  · rintro (old | ⟨_, equal⟩)
    · exact old
    · exact False.elim (ZFSet.mem_irrefl P (equal ▸ hy))
  · exact Or.inl

theorem fixedTopOrder_no_new_below {P r x y : ZFSet.{u}}
    (old : PartialOrderCode P r) (hy : y ∈ P) (entry : ZFSet.pair x y ∈ fixedTopOrder P r) :
    x ∈ P :=
  (ZFSet.pair_mem_prod.1 (old.relation ((fixedTopOrder_old_iff hy).1 entry))).1

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_SeparationTileCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def attachmentTagFormula {n} (x p nset : Fin n) : BoundedFormula n :=
  exMem nset (orderedPairFormula x.succ p.succ 0)

def attachmentOldNewFormula {n} (x y p nset shadow r : Fin n) : BoundedFormula n :=
  .conj (.mem x p) (exMem nset (exMem p.succ
    (.conj (orderedPairFormula y.succ.succ p.succ.succ 1)
      (.conj (pairMembershipFormula 1 0 shadow.succ.succ)
        (pairMembershipFormula x.succ.succ 0 r.succ.succ)))))

end BoundedFormula





def codedAttachmentFreshLe (P inside shadow upper x y : ZFSet.{u}) : Prop :=
  ZFSet.pair x y ∈ inside ∨
    ∃ s ∈ P, ZFSet.pair y s ∈ shadow ∧ ZFSet.pair x s ∈ upper

def codedAttachmentLe (P N r inside shadow upper x y : ZFSet.{u}) : Prop :=
  (x ∈ P ∧ y ∈ P ∧ ZFSet.pair x y ∈ r) ∨
  (x ∈ P ∧ ∃ q ∈ N, ∃ s ∈ P,
    y = ZFSet.pair P q ∧ ZFSet.pair q s ∈ shadow ∧ ZFSet.pair x s ∈ r) ∨
  (y ∈ P ∧ ∃ q ∈ N, x = ZFSet.pair P q ∧ ZFSet.pair q y ∈ upper) ∨
  (∃ q ∈ N, ∃ t ∈ N, x = ZFSet.pair P q ∧ y = ZFSet.pair P t ∧
    codedAttachmentFreshLe P inside shadow upper q t)

noncomputable def codedAttachmentOrder (P N r inside shadow upper : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ taggedExtension P N, ∃ y ∈ taggedExtension P N,
    z = ZFSet.pair x y ∧ codedAttachmentLe P N r inside shadow upper x y)
    (ZFSet.prod (taggedExtension P N) (taggedExtension P N))

theorem pair_mem_codedAttachmentOrder (P N r inside shadow upper x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ codedAttachmentOrder P N r inside shadow upper ↔
      x ∈ taggedExtension P N ∧ y ∈ taggedExtension P N ∧
        codedAttachmentLe P N r inside shadow upper x y := by
  simp only [codedAttachmentOrder, ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.pair_inj]
  constructor
  · rintro ⟨⟨hx, hy⟩, a, _, b, _, ⟨rfl, rfl⟩, lower⟩
    exact ⟨hx, hy, lower⟩
  · rintro ⟨hx, hy, lower⟩
    exact ⟨⟨hx, hy⟩, x, hx, y, hy, ⟨rfl, rfl⟩, lower⟩

theorem codedAttachmentOrder_shape (P N r inside shadow upper : ZFSet.{u}) :
    codedAttachmentOrder P N r inside shadow upper ⊆
      ZFSet.prod (taggedExtension P N) (taggedExtension P N) :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

namespace BoundedFormula
open SetFormula

def codedAttachmentFreshLeFormula {n} (x y p inside shadow upper : Fin n) : BoundedFormula n :=
  disj (pairMembershipFormula x y inside) (exMem p
    (.conj (pairMembershipFormula y.succ 0 shadow.succ)
      (pairMembershipFormula x.succ 0 upper.succ)))

def codedAttachmentLeFormula {n} (x y p nset r inside shadow upper : Fin n) : BoundedFormula n :=
  disj (.conj (.mem x p) (.conj (.mem y p) (pairMembershipFormula x y r)))
    (disj (attachmentOldNewFormula x y p nset shadow r)
      (disj (.conj (.mem y p) (exMem nset
        (.conj (orderedPairFormula x.succ p.succ 0)
          (pairMembershipFormula 0 y.succ upper.succ))))
        (exMem nset (exMem nset.succ
          (.conj (orderedPairFormula x.succ.succ p.succ.succ 1)
            (.conj (orderedPairFormula y.succ.succ p.succ.succ 0)
              (codedAttachmentFreshLeFormula 1 0 p.succ.succ inside.succ.succ
                shadow.succ.succ upper.succ.succ)))))))

def codedAttachmentOrderEntryFormula {n} (z l p nset r inside shadow upper : Fin n) :
    BoundedFormula n :=
  exMem l (exMem l.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (codedAttachmentLeFormula 1 0 p.succ.succ nset.succ.succ r.succ.succ
      inside.succ.succ shadow.succ.succ upper.succ.succ)))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def greatestLowerBoundFormula {n} (l r x y z : Fin n) : BoundedFormula n :=
  .conj (pairMembershipFormula z x r) (.conj (pairMembershipFormula z y r)
    (allMem l (imp (pairMembershipFormula 0 x.succ r.succ)
      (imp (pairMembershipFormula 0 y.succ r.succ) (pairMembershipFormula 0 z.succ r.succ)))))

def canonicalMeetEntryFormula {n} (v l r : Fin n) : BoundedFormula n :=
  exMem l (exMem l.succ (exMem l.succ.succ
    (.conj (orderedTripleFormula v.succ.succ.succ 2 1 0)
      (greatestLowerBoundFormula l.succ.succ.succ r.succ.succ.succ 2 1 0))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSingleAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

structure SingleAttachmentInputs (P Q rP rQ μP μQ ell F a e : ZFSet.{u}) : Prop where
  oldOrder : MeetOrderCode P rP μP
  templateOrder : MeetOrderCode Q rQ μQ
  anchor_mem : a ∈ Q
  base_function : ZFSet.IsFunc (attachmentIdeal Q rQ a) P ell
  base_order : ∀ x y x' y', ZFSet.pair x x' ∈ ell → ZFSet.pair y y' ∈ ell →
    (ZFSet.pair x' y' ∈ rP ↔ ZFSet.pair x y ∈ rQ)
  base_meet : ∀ x y z x' y' z', ZFSet.pair (ZFSet.pair x y) z ∈ μQ →
    ZFSet.pair x x' ∈ ell → ZFSet.pair y y' ∈ ell → ZFSet.pair z z' ∈ ell →
      ZFSet.pair (ZFSet.pair x' y') z' ∈ μP
  filter : MeetFilterCode P rP μP F
  separator_mem : e ∈ P
  base_le_separator : ∀ b, ZFSet.pair a b ∈ ell → ZFSet.pair b e ∈ rP
  separator_not_le_base : ∀ b, ZFSet.pair a b ∈ ell → ZFSet.pair e b ∉ rP
  separator_le_upper : ∀ y ∈ F, ZFSet.pair e y ∈ rP

namespace SingleAttachmentInputs

variable {P Q rP rQ μP μQ ell F a e : ZFSet.{u}}
variable (d : SingleAttachmentInputs P Q rP rQ μP μQ ell F a e)

abbrev Base := {q : {q : ZFSet.{u} // q ∈ Q} //
  d.templateOrder.toMeetOrder.le q ⟨a, d.anchor_mem⟩}

theorem base_mem (q : d.Base) : q.val.val ∈ attachmentIdeal Q rQ a :=
  (mem_attachmentIdeal Q rQ a q.val.val).2 ⟨q.val.property, q.property⟩

noncomputable def baseMap (q : d.Base) : {p : ZFSet.{u} // p ∈ P} :=
  ⟨(d.base_function.2 q.val.val (d.base_mem q)).choose,
    (ZFSet.pair_mem_prod.1 (d.base_function.1
      (d.base_function.2 q.val.val (d.base_mem q)).choose_spec.1)).2⟩

theorem baseMap_entry (q : d.Base) : ZFSet.pair q.val.val (d.baseMap q).val ∈ ell :=
  (d.base_function.2 q.val.val (d.base_mem q)).choose_spec.1

noncomputable def baseEmbedding :
    MeetEmbedding (Attachment.idealOrder d.templateOrder.toMeetOrder ⟨a, d.anchor_mem⟩)
      d.oldOrder.toMeetOrder where
  toFun := d.baseMap
  le_iff x y := d.base_order _ _ _ _ (d.baseMap_entry x) (d.baseMap_entry y)
  map_meet x y := by
    apply Subtype.ext
    have entry := d.base_meet _ _ _ _ _ _
      (d.templateOrder.toMeetOrder_meet_entry x.val y.val)
      (d.baseMap_entry x) (d.baseMap_entry y)
      (d.baseMap_entry ((Attachment.idealOrder d.templateOrder.toMeetOrder
        ⟨a, d.anchor_mem⟩).meet x y))
    obtain ⟨z, _, unique⟩ := d.oldOrder.operation.2
      (ZFSet.pair (d.baseMap x).val (d.baseMap y).val)
      (ZFSet.pair_mem_prod.2 ⟨(d.baseMap x).property, (d.baseMap y).property⟩)
    exact (unique _ entry).trans
      (unique _ (d.oldOrder.toMeetOrder_meet_entry (d.baseMap x) (d.baseMap y))).symm

noncomputable def templates : Attachment.Templates d.oldOrder.toMeetOrder Unit where
  Space _ := {q : ZFSet.{u} // q ∈ Q}
  order _ := d.templateOrder.toMeetOrder
  anchor _ := ⟨a, d.anchor_mem⟩
  embed _ := d.baseEmbedding
  upper _ x := x.val ∈ F
  upper_nonempty _ := by
    obtain ⟨x, hx⟩ := d.filter.nonempty
    exact ⟨⟨x, d.filter.subset hx⟩, hx⟩
  upper_up := by
    intro i x y hx lower
    exact d.filter.upward x.val hx y.val y.property lower
  upper_meet := by
    intro i x y hx hy
    exact d.filter.closed_meet x.val hx y.val hy _
      (d.oldOrder.toMeetOrder_meet_entry x y)
  separator _ := ⟨e, d.separator_mem⟩
  base_le_separator _ := d.base_le_separator _ (d.baseMap_entry _)
  separator_not_le_base _ := d.separator_not_le_base _ (d.baseMap_entry _)
  separator_le_upper _ _ hy := d.separator_le_upper _ hy

theorem shadow_entry (q : d.templates.Fresh) :
    ZFSet.pair q.2.val.val (d.templates.shadow q).val ∈
      attachmentShadowGraph Q P μQ ell a := by
  apply (pair_mem_attachmentShadowGraph Q P μQ ell a _ _).2
  refine ⟨q.2.val.property, (d.templates.shadow q).property,
    (d.templateOrder.toMeetOrder.meet q.2.val ⟨a, d.anchor_mem⟩).val,
    (d.templateOrder.toMeetOrder.meet q.2.val ⟨a, d.anchor_mem⟩).property,
    d.templateOrder.toMeetOrder_meet_entry _ _, ?_⟩
  exact d.baseMap_entry (Attachment.cut d.templateOrder.toMeetOrder ⟨a, d.anchor_mem⟩ q.2.val)

end SingleAttachmentInputs






structure AttachmentBatchInputs
    (P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}) : Prop where
  oldOrder : MeetOrderCode P rP μP
  spaces : FunctionGraphOn I Qs
  relations : FunctionGraphOn I rs
  meets : FunctionGraphOn I μs
  anchors : FunctionGraphOn I As
  embeddings : FunctionGraphOn I Es
  filters : FunctionGraphOn I Fs
  separators : FunctionGraphOn I Ss
  valid : ∀ i ∈ I, ∀ Q r μ a ell F e,
    ZFSet.pair i Q ∈ Qs → ZFSet.pair i r ∈ rs → ZFSet.pair i μ ∈ μs →
    ZFSet.pair i a ∈ As → ZFSet.pair i ell ∈ Es → ZFSet.pair i F ∈ Fs →
    ZFSet.pair i e ∈ Ss → SingleAttachmentInputs P Q rP r μP μ ell F a e

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

noncomputable abbrev space (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.spaces.value i
noncomputable abbrev rel (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.relations.value i
noncomputable abbrev meet (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.meets.value i
noncomputable abbrev anchor (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.anchors.value i
noncomputable abbrev embed (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.embeddings.value i
noncomputable abbrev filter (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.filters.value i
noncomputable abbrev separator (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} := d.separators.value i

theorem space_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.space i) ∈ Qs :=
  d.spaces.value_entry i

theorem rel_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.rel i) ∈ rs :=
  d.relations.value_entry i

theorem meet_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.meet i) ∈ μs :=
  d.meets.value_entry i

theorem anchor_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.anchor i) ∈ As :=
  d.anchors.value_entry i

theorem embed_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.embed i) ∈ Es :=
  d.embeddings.value_entry i

theorem filter_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.filter i) ∈ Fs :=
  d.filters.value_entry i

theorem separator_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (d.separator i) ∈ Ss :=
  d.separators.value_entry i

theorem fiber (i : {i : ZFSet.{u} // i ∈ I}) :
    SingleAttachmentInputs P (d.space i) rP (d.rel i) μP (d.meet i)
      (d.embed i) (d.filter i) (d.anchor i) (d.separator i) :=
  d.valid i.val i.property _ _ _ _ _ _ _ (d.space_entry i) (d.rel_entry i)
    (d.meet_entry i) (d.anchor_entry i) (d.embed_entry i) (d.filter_entry i) (d.separator_entry i)

noncomputable def templates :
    Attachment.Templates d.oldOrder.toMeetOrder {i : ZFSet.{u} // i ∈ I} where
  Space i := {q : ZFSet.{u} // q ∈ d.space i}
  order i := (d.fiber i).templateOrder.toMeetOrder
  anchor i := ⟨d.anchor i, (d.fiber i).anchor_mem⟩
  embed i := (d.fiber i).baseEmbedding
  upper i x := x.val ∈ d.filter i
  upper_nonempty i := by
    obtain ⟨x, hx⟩ := (d.fiber i).filter.nonempty
    exact ⟨⟨x, (d.fiber i).filter.subset hx⟩, hx⟩
  upper_up := by
    intro i x y hx lower
    exact (d.fiber i).filter.upward x.val hx y.val y.property lower
  upper_meet := by
    intro i x y hx hy
    exact (d.fiber i).filter.closed_meet x.val hx y.val hy _
      (d.oldOrder.toMeetOrder_meet_entry x y)
  separator i := ⟨d.separator i, (d.fiber i).separator_mem⟩
  base_le_separator i := (d.fiber i).base_le_separator _ ((d.fiber i).baseMap_entry _)
  separator_not_le_base i := (d.fiber i).separator_not_le_base _ ((d.fiber i).baseMap_entry _)
  separator_le_upper i _ hy := (d.fiber i).separator_le_upper _ hy

end AttachmentBatchInputs

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTemplateIntervalFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

open SetFormula

def indexedAttachmentDomainEntryFormula {n} (z i qs bound : Fin n) : BoundedFormula n :=
  exMem i (exMem bound.succ (exMem 0
    (.conj (pairMembershipFormula 2 1 qs.succ.succ.succ)
      (orderedPairFormula z.succ.succ.succ 2 0))))

theorem truth_indexedAttachmentDomainEntryFormula {n} (z i qs bound : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedAttachmentDomainEntryFormula z i qs bound) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env bound, ∃ q ∈ Q,
        ZFSet.pair j Q ∈ env qs ∧ env z = ZFSet.pair j q := by
  simp only [indexedAttachmentDomainEntryFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_orderedPairFormula]
  rfl

def indexedAttachmentFreshEntryFormula {n}
    (z i qs rs anchors qBound rBound aBound : Fin n) : BoundedFormula n :=
  exMem i (exMem qBound.succ (exMem rBound.succ.succ
    (exMem aBound.succ.succ.succ (exMem 2
      (.conj (pairMembershipFormula 4 3 qs.succ.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 4 2 rs.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 4 1 anchors.succ.succ.succ.succ.succ)
            (.conj (orderedPairFormula z.succ.succ.succ.succ.succ 4 0)
              (.neg (pairMembershipFormula 0 1 2))))))))))

theorem truth_indexedAttachmentFreshEntryFormula {n}
    (z i qs rs anchors qBound rBound aBound : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (indexedAttachmentFreshEntryFormula z i qs rs anchors qBound rBound aBound) env ↔
      ∃ j ∈ env i, ∃ Q ∈ env qBound, ∃ r ∈ env rBound, ∃ a ∈ env aBound, ∃ q ∈ Q,
        ZFSet.pair j Q ∈ env qs ∧ ZFSet.pair j r ∈ env rs ∧ ZFSet.pair j a ∈ env anchors ∧
        env z = ZFSet.pair j q ∧ ZFSet.pair q a ∉ r := by
  simp only [indexedAttachmentFreshEntryFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_orderedPairFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem familyPointBound_mem (unions : Realize M.sets SetFormula.union Fin.elim0)
    {Qs : ZFSet.{u}} (hQs : Qs ∈ M.sets) : familyPointBound Qs ∈ M.sets :=
  M.union_mem unions (M.union_mem unions (M.union_mem unions hQs))

theorem indexedAttachmentDomain_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs : ZFSet.{u}} (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) :
    indexedAttachmentDomain I Qs ∈ M.sets := by
  have bound := M.union_mem unions (M.union_mem unions hQs)
  let params := extend I (extend Qs (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedAttachmentDomainEntryFormula 0 1 2 3) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases bound (fun j => Fin.elim0 j))))
    (M.prod_mem pairing unions powers separation hI (M.familyPointBound_mem unions hQs))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedAttachmentDomainEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod I (familyPointBound Qs)) = indexedAttachmentDomain I Qs := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedAttachmentDomain, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedAttachmentDomainEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

theorem indexedAttachmentFresh_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs rs anchors : ZFSet.{u}} (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAnchors : anchors ∈ M.sets) :
    indexedAttachmentFresh I Qs rs anchors ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have rBound := M.union_mem unions (M.union_mem unions hrs)
  have aBound := M.union_mem unions (M.union_mem unions hAnchors)
  let params := extend I (extend Qs (extend rs (extend anchors
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion rs))
      (extend (ZFSet.sUnion (ZFSet.sUnion anchors)) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.indexedAttachmentFreshEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases hrs (Fin.cases hAnchors
      (Fin.cases qBound (Fin.cases rBound (Fin.cases aBound (fun j => Fin.elim0 j))))))))
    (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.indexedAttachmentFreshEntryFormula 0 1 2 3 4 5 6 7) (extend z params))
      (indexedAttachmentDomain I Qs) = indexedAttachmentFresh I Qs rs anchors := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedAttachmentFresh, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_indexedAttachmentFreshEntryFormula 0 1 2 3 4 5 6 7 _)
  exact equal ▸ selected

end TransitiveGround






structure BatchHeightEndpointCode
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (C D oldH rD Cs los his : ZFSet.{u}) : Prop where
  columns : ZFSet.IsFunc I C Cs
  lows : ZFSet.IsFunc I D los
  highs : ZFSet.IsFunc I D his
  base : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ c lo,
    ZFSet.pair i.val c ∈ Cs → ZFSet.pair i.val lo ∈ los →
      ZFSet.pair (d.templates.base i).val (ZFSet.pair c lo) ∈ oldH
  gap : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ lo hi,
    ZFSet.pair i.val lo ∈ los → ZFSet.pair i.val hi ∈ his → ZFSet.pair lo hi ∈ rD
  upper : ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ c hi c' v,
    ZFSet.pair i.val c ∈ Cs → ZFSet.pair i.val hi ∈ his →
      ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH →
        (c = c' ∧ hi = v) ∨ c ∈ c'

namespace BatchHeightEndpointCode

theorem interval_upper
    {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD Cs los his : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (endpoints : BatchHeightEndpointCode d C D oldH rD Cs los his)
    (i : {i : ZFSet.{u} // i ∈ I}) {c hi q c' v : ZFSet.{u}}
    (column : ZFSet.pair i.val c ∈ Cs) (upper : ZFSet.pair i.val hi ∈ his)
    (below : ZFSet.pair q hi ∈ rD)
    (separator : ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH) :
    c ∈ c' ∨ (c = c' ∧ ZFSet.pair q v ∈ rD) := by
  rcases endpoints.upper i c hi c' v column upper separator with ⟨same, rfl⟩ | smaller
  · exact Or.inr ⟨same, below⟩
  · exact Or.inl smaller

end BatchHeightEndpointCode

end




universe u

namespace BoundedFormula

open SetFormula

def endpointRightTripleFormula {n} (z x y w : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (orderedPairFormula 0 y.succ.succ w.succ.succ)
    (orderedPairFormula z.succ.succ x.succ.succ 0)))

def endpointRightMembershipFormula {n} (x y w f : Fin n) : BoundedFormula n :=
  exMem f (endpointRightTripleFormula 0 x.succ y.succ w.succ)

def endpointTupleFormula {n} (z i c lo hi : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (.conj (endpointRightTripleFormula 0 c.succ.succ lo.succ.succ hi.succ.succ)
    (orderedPairFormula z.succ.succ i.succ.succ 0)))

def batchHeightEndpointFormula : BoundedFormula 12 :=
  exMem 1 (exMem 11 (exMem 13 (exMem 5 (exMem 6 (exMem 8 (exMem 10 (exMem 11 (exMem 11 (exMem 13
    (.conj (endpointTupleFormula 10 9 4 3 2)
      (.conj (pairMembershipFormula 9 8 15)
        (.conj (pairMembershipFormula 9 7 16)
          (.conj (pairMembershipFormula 8 6 7)
            (.conj (pairMembershipFormula 9 5 17)
              (.conj (endpointRightMembershipFormula 6 4 3 18)
                (.conj (endpointRightMembershipFormula 5 1 0 18)
                  (.conj (pairMembershipFormula 3 2 19)
                    (disj (.conj (.equal 4 1) (.equal 2 0)) (.mem 4 1)))))))))))))))))))

end BoundedFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBatchAttachmentGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

noncomputable def batchAttachmentShadowGraph (I P Qs μs As Es : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ZFSet.sUnion (ZFSet.sUnion Qs),
    ∃ μ ∈ ZFSet.sUnion (ZFSet.sUnion μs), ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion As),
    ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es), ∃ q ∈ Q, ∃ p ∈ P,
      z = ZFSet.pair (ZFSet.pair i q) p ∧ ZFSet.pair i Q ∈ Qs ∧
      ZFSet.pair i μ ∈ μs ∧ ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧
      ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μ ∧ ZFSet.pair c p ∈ ell)
    (ZFSet.prod (indexedAttachmentDomain I Qs) P)

noncomputable def batchAttachmentTemplateGraph (I P Qs rs As Es : ZFSet.{u}) : ZFSet.{u} :=
  let D := indexedAttachmentDomain I Qs
  let N := indexedAttachmentFresh I Qs rs As
  let L := taggedExtension P N
  ZFSet.sep (fun z => ∃ x ∈ D, ∃ y ∈ L, z = ZFSet.pair x y ∧
    ((∃ i ∈ I, ∃ q ∈ familyPointBound Qs, x = ZFSet.pair i q ∧
      ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es), ZFSet.pair i ell ∈ Es ∧ ZFSet.pair q y ∈ ell) ∨
      (x ∈ N ∧ y = ZFSet.pair P x))) (ZFSet.prod D L)

noncomputable def batchTemplateGraph (I P Qs rs As Es i : ZFSet.{u}) : ZFSet.{u} :=
  let L := taggedExtension P (indexedAttachmentFresh I Qs rs As)
  ZFSet.sep (fun z => ∃ q ∈ familyPointBound Qs, ∃ y ∈ L,
    z = ZFSet.pair q y ∧ ZFSet.pair (ZFSet.pair i q) y ∈
      batchAttachmentTemplateGraph I P Qs rs As Es)
    (ZFSet.prod (familyPointBound Qs) L)

theorem batchAttachmentShadowGraph_shape (I P Qs μs As Es : ZFSet.{u}) :
    batchAttachmentShadowGraph I P Qs μs As Es ⊆ ZFSet.prod (indexedAttachmentDomain I Qs) P :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_batchAttachmentShadowGraph (I P Qs μs As Es i q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) p ∈ batchAttachmentShadowGraph I P Qs μs As Es ↔
      i ∈ I ∧ ∃ Q μ a ell, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i μ ∈ μs ∧
        ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧
          ZFSet.pair q p ∈ attachmentShadowGraph Q P μ ell a := by
  constructor
  · intro hz
    obtain ⟨j, hj, Q, _, μ, _, a, _, ell, _, u, hu, v, hv,
      equal, eQ, eμ, ea, eell, c, hc, meet, image⟩ := (ZFSet.mem_sep.1 hz).2
    obtain ⟨indices, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 indices
    exact ⟨hj, Q, μ, a, ell, eQ, eμ, ea, eell,
      (pair_mem_attachmentShadowGraph Q P μ ell a _ _).2 ⟨hu, hv, c, hc, meet, image⟩⟩
  · rintro ⟨hi, Q, μ, a, ell, eQ, eμ, ea, eell, entry⟩
    obtain ⟨hq, hp, c, hc, meet, image⟩ := (pair_mem_attachmentShadowGraph Q P μ ell a q p).1 entry
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, eQ, hq⟩, hp⟩,
      i, hi, Q, pair_second_mem_doubleUnion eQ, μ, pair_second_mem_doubleUnion eμ,
      a, pair_second_mem_doubleUnion ea, ell, pair_second_mem_doubleUnion eell,
      q, hq, p, hp, rfl, eQ, eμ, ea, eell, c, hc, meet, image⟩

theorem batchAttachmentTemplateGraph_shape (I P Qs rs As Es : ZFSet.{u}) :
    batchAttachmentTemplateGraph I P Qs rs As Es ⊆
      ZFSet.prod (indexedAttachmentDomain I Qs) (taggedExtension P (indexedAttachmentFresh I Qs rs As)) := by
  intro z hz
  dsimp only [batchAttachmentTemplateGraph] at hz
  exact (ZFSet.mem_sep.1 hz).1

theorem pair_mem_batchAttachmentTemplateGraph (I P Qs rs As Es i q y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es ↔
      ZFSet.pair i q ∈ indexedAttachmentDomain I Qs ∧
      y ∈ taggedExtension P (indexedAttachmentFresh I Qs rs As) ∧
      ((∃ ell, ZFSet.pair i ell ∈ Es ∧ ZFSet.pair q y ∈ ell) ∨
        (ZFSet.pair i q ∈ indexedAttachmentFresh I Qs rs As ∧ y = ZFSet.pair P (ZFSet.pair i q))) := by
  dsimp only [batchAttachmentTemplateGraph]
  constructor
  · intro hz
    have shape := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨x, _, v, _, equal, branch⟩ := (ZFSet.mem_sep.1 hz).2
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    refine ⟨shape.1, shape.2, ?_⟩
    rcases branch with ⟨j, _, u, _, equal, ell, _, entry, image⟩ | fresh
    · obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      exact Or.inl ⟨ell, entry, image⟩
    · exact Or.inr fresh
  · rintro ⟨domain, hy, branch⟩
    refine ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨domain, hy⟩,
      ZFSet.pair i q, domain, y, hy, rfl, ?_⟩
    rcases branch with ⟨ell, entry, image⟩ | fresh
    · obtain ⟨hi, hq⟩ := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset I Qs domain)
      exact Or.inl ⟨i, hi, q, hq, rfl, ell, pair_second_mem_doubleUnion entry, entry, image⟩
    · exact Or.inr fresh

theorem pair_mem_batchTemplateGraph (I P Qs rs As Es i q y : ZFSet.{u}) :
    ZFSet.pair q y ∈ batchTemplateGraph I P Qs rs As Es i ↔
      ZFSet.pair (ZFSet.pair i q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es := by
  dsimp only [batchTemplateGraph]
  constructor
  · intro hz
    obtain ⟨u, _, v, _, equal, entry⟩ := (ZFSet.mem_sep.1 hz).2
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact entry
  · intro entry
    have shape := ZFSet.pair_mem_prod.1 (batchAttachmentTemplateGraph_shape I P Qs rs As Es entry)
    have hq := (ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset I Qs shape.1)).2
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hq, shape.2⟩, q, hq, y, shape.2, rfl, entry⟩

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
include d

theorem batch_shadow_entry_iff (i : {i : ZFSet.{u} // i ∈ I}) (q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) p ∈ batchAttachmentShadowGraph I P Qs μs As Es ↔
      ZFSet.pair q p ∈ attachmentShadowGraph (d.space i) P (d.meet i) (d.embed i) (d.anchor i) := by
  rw [pair_mem_batchAttachmentShadowGraph]
  constructor
  · rintro ⟨_, Q, μ, a, ell, eQ, eμ, ea, eell, entry⟩
    have eqQ := d.spaces.unique eQ (d.space_entry i)
    have eqμ := d.meets.unique eμ (d.meet_entry i)
    have eqa := d.anchors.unique ea (d.anchor_entry i)
    have eqell := d.embeddings.unique eell (d.embed_entry i)
    exact eqQ ▸ eqμ ▸ eqa ▸ eqell ▸ entry
  · intro entry
    exact ⟨i.property, d.space i, d.meet i, d.anchor i, d.embed i,
      d.space_entry i, d.meet_entry i, d.anchor_entry i, d.embed_entry i, entry⟩

theorem batch_shadow_function :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) P (batchAttachmentShadowGraph I P Qs μs As Es) := by
  refine ⟨batchAttachmentShadowGraph_shape I P Qs μs As Es, ?_⟩
  intro x hx
  obtain ⟨i, hi, q, rfl, Q, eQ, hq⟩ := (mem_indexedAttachmentDomain I Qs x).1 hx
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have qQ : q ∈ d.space j := d.spaces.unique eQ (d.space_entry j) ▸ hq
  obtain ⟨p, entry, unique⟩ := (attachmentShadowGraph_function
    (d.fiber j).templateOrder (d.fiber j).anchor_mem (d.fiber j).base_function).2 q qQ
  exact ⟨p, (d.batch_shadow_entry_iff j q p).2 entry,
    fun y hy => unique y ((d.batch_shadow_entry_iff j q y).1 hy)⟩

theorem batch_template_entry_iff (i : {i : ZFSet.{u} // i ∈ I}) (q y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es ↔
      ZFSet.pair q y ∈ d.embed i ∨
        (q ∈ freshPart (d.space i) (d.rel i) (d.anchor i) ∧
          y = ZFSet.pair P (ZFSet.pair i.val q)) := by
  rw [pair_mem_batchAttachmentTemplateGraph]
  constructor
  · rintro ⟨_, _, branch⟩
    rcases branch with ⟨ell, eell, entry⟩ | ⟨fresh, equal⟩
    · exact Or.inl (d.embeddings.unique eell (d.embed_entry i) ▸ entry)
    · exact Or.inr ⟨(pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
        (d.space_entry i) (d.rel_entry i) (d.anchor_entry i)).1 fresh, equal⟩
  · intro branch
    rcases branch with entry | ⟨fresh, rfl⟩
    · have shape := ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 entry)
      exact ⟨(pair_mem_indexedAttachmentDomain_of_entry d.spaces (d.space_entry i)).2
        ((mem_attachmentIdeal _ _ _ _).1 shape.1).1, old_mem_taggedExtension shape.2,
        Or.inl ⟨d.embed i, d.embed_entry i, entry⟩⟩
    · have indexed := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
        (d.space_entry i) (d.rel_entry i) (d.anchor_entry i)).2 fresh
      exact ⟨indexedAttachmentFresh_subset I Qs rs As indexed, pair_mem_taggedExtension.2 indexed,
        Or.inr ⟨indexed, rfl⟩⟩

theorem batch_template_total (i : {i : ZFSet.{u} // i ∈ I}) {q : ZFSet.{u}}
    (hq : q ∈ d.space i) :
    ∃ y, ZFSet.pair (ZFSet.pair i.val q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es := by
  classical
  by_cases below : ZFSet.pair q (d.anchor i) ∈ d.rel i
  · obtain ⟨y, entry, _⟩ := (d.fiber i).base_function.2 q
      ((mem_attachmentIdeal _ _ _ _).2 ⟨hq, below⟩)
    exact ⟨y, (d.batch_template_entry_iff i q y).2 (Or.inl entry)⟩
  · exact ⟨ZFSet.pair P (ZFSet.pair i.val q), (d.batch_template_entry_iff i q _).2
      (Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨hq, below⟩, rfl⟩)⟩

theorem batch_template_unique (i : {i : ZFSet.{u} // i ∈ I}) {q y z : ZFSet.{u}}
    (hy : ZFSet.pair (ZFSet.pair i.val q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es)
    (hz : ZFSet.pair (ZFSet.pair i.val q) z ∈ batchAttachmentTemplateGraph I P Qs rs As Es) : y = z := by
  rcases (d.batch_template_entry_iff i q y).1 hy with hy | hy
  · rcases (d.batch_template_entry_iff i q z).1 hz with hz | hz
    · have source := (ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 hy)).1
      obtain ⟨v, _, unique⟩ := (d.fiber i).base_function.2 q source
      exact (unique y hy).trans (unique z hz).symm
    · exact False.elim (attachmentIdeal_not_freshPart
        (ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 hy)).1 hz.1)
  · rcases (d.batch_template_entry_iff i q z).1 hz with hz | hz
    · exact False.elim (attachmentIdeal_not_freshPart
        (ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 hz)).1 hy.1)
    · exact hy.2.trans hz.2.symm

theorem batch_template_function :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) (taggedExtension P (indexedAttachmentFresh I Qs rs As))
      (batchAttachmentTemplateGraph I P Qs rs As Es) := by
  refine ⟨batchAttachmentTemplateGraph_shape I P Qs rs As Es, ?_⟩
  intro x hx
  obtain ⟨i, hi, q, rfl, Q, eQ, hq⟩ := (mem_indexedAttachmentDomain I Qs x).1 hx
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have qQ : q ∈ d.space j := d.spaces.unique eQ (d.space_entry j) ▸ hq
  obtain ⟨y, entry⟩ := d.batch_template_total j qQ
  exact ⟨y, entry, fun z hz => d.batch_template_unique j hz entry⟩

theorem batch_template_fiber_function (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.IsFunc (d.space i) (taggedExtension P (indexedAttachmentFresh I Qs rs As))
      (batchTemplateGraph I P Qs rs As Es i.val) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    dsimp only [batchTemplateGraph] at hz
    obtain ⟨q, _, y, hy, rfl, entry⟩ := (ZFSet.mem_sep.1 hz).2
    have domain := (ZFSet.pair_mem_prod.1 (d.batch_template_function.1 entry)).1
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain_of_entry d.spaces (d.space_entry i)).1 domain, hy⟩
  · intro q hq
    obtain ⟨y, entry⟩ := d.batch_template_total i hq
    exact ⟨y, (pair_mem_batchTemplateGraph I P Qs rs As Es i.val q y).2 entry,
      fun z hz => d.batch_template_unique i
        ((pair_mem_batchTemplateGraph I P Qs rs As Es i.val q z).1 hz) entry⟩

end AttachmentBatchInputs

namespace BoundedFormula

open SetFormula

def batchShadowGraphFormula : BoundedFormula 11 :=
  exMem 1 (exMem 8 (exMem 10 (exMem 12 (exMem 14 (exMem 3 (exMem 8
    (.conj (orderedTripleFormula 7 6 1 0)
      (.conj (pairMembershipFormula 6 5 10)
        (.conj (pairMembershipFormula 6 4 11)
          (.conj (pairMembershipFormula 6 3 12)
            (.conj (pairMembershipFormula 6 2 13)
              (exMem 5 (.conj (tripleMembershipFormula 2 4 0 5)
                (pairMembershipFormula 0 1 3))))))))))))))

def batchTemplateGraphFormula : BoundedFormula 9 :=
  exMem 1 (exMem 3 (.conj (orderedPairFormula 2 1 0)
    (disj (exMem 6 (exMem 8 (.conj (orderedPairFormula 3 1 0)
      (exMem 11 (.conj (pairMembershipFormula 2 0 11) (pairMembershipFormula 1 3 0))))))
      (.conj (.mem 1 10) (orderedPairFormula 0 5 1)))))

theorem truth_batchTemplateGraphFormula (env : Fin 9 → ZFSet.{u}) :
    Truth batchTemplateGraphFormula env ↔
      ∃ x ∈ env 1, ∃ y ∈ env 2, env 0 = ZFSet.pair x y ∧
        ((∃ i ∈ env 4, ∃ q ∈ env 5, x = ZFSet.pair i q ∧
          ∃ ell ∈ env 7, ZFSet.pair i ell ∈ env 6 ∧ ZFSet.pair q y ∈ ell) ∨
          (x ∈ env 8 ∧ y = ZFSet.pair (env 3) x)) := by
  simp only [batchTemplateGraphFormula, truth_exMem, Truth, truth_disj,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

def batchTemplateFiberFormula : BoundedFormula 5 :=
  exMem 1 (exMem 3 (.conj (orderedPairFormula 2 1 0) (tripleMembershipFormula 5 1 0 6)))

theorem truth_batchTemplateFiberFormula (env : Fin 5 → ZFSet.{u}) :
    Truth batchTemplateFiberFormula env ↔
      ∃ q ∈ env 1, ∃ y ∈ env 2, env 0 = ZFSet.pair q y ∧
        ZFSet.pair (ZFSet.pair (env 3) q) y ∈ env 4 := by
  simp only [batchTemplateFiberFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchAttachmentTemplateGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    batchAttachmentTemplateGraph I P Qs rs As Es ∈ M.sets := by
  let D := indexedAttachmentDomain I Qs
  let N := indexedAttachmentFresh I Qs rs As
  let L := taggedExtension P N
  have hD : D ∈ M.sets := M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs
  have hN : N ∈ M.sets := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hL : L ∈ M.sets := M.taggedExtension_mem pairing unions powers separation hP hN
  have hPoints := M.familyPointBound_mem unions hQs
  have hE := M.union_mem unions (M.union_mem unions hEs)
  let params := extend D (extend L (extend P (extend I (extend (familyPointBound Qs)
    (extend Es (extend (ZFSet.sUnion (ZFSet.sUnion Es)) (extend N Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchTemplateGraphFormula params
    (Fin.cases hD (Fin.cases hL (Fin.cases hP (Fin.cases hI (Fin.cases hPoints
      (Fin.cases hEs (Fin.cases hE (Fin.cases hN (fun j => Fin.elim0 j)))))))))
    (M.prod_mem pairing unions powers separation hD hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchTemplateGraphFormula
      (extend z params)) (ZFSet.prod D L) = batchAttachmentTemplateGraph I P Qs rs As Es := by
    apply ZFSet.ext
    intro z
    dsimp only [batchAttachmentTemplateGraph]
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchTemplateGraphFormula _)
  exact equal ▸ selected

theorem batchTemplateGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es i : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)
    (hi : i ∈ M.sets) : batchTemplateGraph I P Qs rs As Es i ∈ M.sets := by
  let L := taggedExtension P (indexedAttachmentFresh I Qs rs As)
  let graph := batchAttachmentTemplateGraph I P Qs rs As Es
  have hPoints := M.familyPointBound_mem unions hQs
  have hL : L ∈ M.sets := M.taggedExtension_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
  have hGraph : graph ∈ M.sets := M.batchAttachmentTemplateGraph_mem
    pairing unions powers separation hI hP hQs hrs hAs hEs
  let params := extend (familyPointBound Qs) (extend L (extend i (extend graph Fin.elim0)))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchTemplateFiberFormula params
    (Fin.cases hPoints (Fin.cases hL (Fin.cases hi (Fin.cases hGraph (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hPoints hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchTemplateFiberFormula
      (extend z params)) (ZFSet.prod (familyPointBound Qs) L) = batchTemplateGraph I P Qs rs As Es i := by
    apply ZFSet.ext
    intro z
    dsimp only [batchTemplateGraph]
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchTemplateFiberFormula _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BatchAttachmentRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v w

structure CodedTemplateAttachment {J : Type v} {P r μ : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J)
    (N inside shadow upper : ZFSet.{u}) where
  freshCode : b.Fresh → ZFSet.{u}
  fresh_mem : ∀ q, freshCode q ∈ N
  fresh_injective : Function.Injective freshCode
  fresh_surjective : ∀ z ∈ N, ∃ q, freshCode q = z
  shadow_entry : ∀ q, ZFSet.pair (freshCode q) (b.shadow q).val ∈ shadow
  shadow_value : ∀ q s, ZFSet.pair (freshCode q) s ∈ shadow → s = (b.shadow q).val
  inside_iff : ∀ q t, ZFSet.pair (freshCode q) (freshCode t) ∈ inside ↔ b.Inside q t
  upper_iff : ∀ q p, ZFSet.pair (freshCode q) p.val ∈ upper ↔ b.upper q.1 p

namespace CodedTemplateAttachment
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

def encode : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh) → ZFSet.{u}
  | .inl p => p.val
  | .inr q => ZFSet.pair P (d.freshCode q)

noncomputable abbrev carrier (_d : CodedTemplateAttachment old b N inside shadow upper) := taggedExtension P N
noncomputable abbrev order (_d : CodedTemplateAttachment old b N inside shadow upper) :=
  codedAttachmentOrder P N r inside shadow upper
noncomputable abbrev meetGraph := canonicalMeetGraph d.carrier d.order

theorem encode_mem (x : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh) : d.encode x ∈ d.carrier := by
  cases x with
  | inl p => exact old_mem_taggedExtension p.property
  | inr q => exact pair_mem_taggedExtension.2 (d.fresh_mem q)

theorem encode_surjective : ∀ z ∈ d.carrier,
    ∃ x : {p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh, d.encode x = z := by
  intro z hz
  rcases mem_taggedExtension.1 hz with old | ⟨q, hq, eq⟩
  · exact ⟨.inl ⟨z, old⟩, rfl⟩
  · obtain ⟨t, rfl⟩ := d.fresh_surjective q hq
    exact ⟨.inr t, eq.symm⟩

theorem fresh_le_iff (q t : b.Fresh) :
    codedAttachmentFreshLe P inside shadow upper (d.freshCode q) (d.freshCode t) ↔
      b.extension.le (.inr q) (.inr t) := by
  change (_ ∨ _) ↔ (_ ∨ _)
  apply or_congr (d.inside_iff q t)
  constructor
  · rintro ⟨s, _, entry, above⟩
    have eq := d.shadow_value t s entry
    exact (d.upper_iff q (b.shadow t)).1 (eq ▸ above)
  · intro above
    exact ⟨(b.shadow t).val, (b.shadow t).property, d.shadow_entry t,
      (d.upper_iff q (b.shadow t)).2 above⟩

theorem le_encode (x y : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh)) :
    ZFSet.pair (d.encode x) (d.encode y) ∈ d.order ↔ b.extension.le x y := by
  rw [pair_mem_codedAttachmentOrder]
  have bounded : d.encode x ∈ d.carrier ∧ d.encode y ∈ d.carrier :=
    ⟨d.encode_mem x, d.encode_mem y⟩
  simp only [bounded.1, bounded.2, true_and]
  cases x with
  | inl p =>
    cases y with
    | inl s =>
      change codedAttachmentLe P N r inside shadow upper p.val s.val ↔ ZFSet.pair p.val s.val ∈ r
      constructor
      · rintro (h | h | h | h)
        · exact h.2.2
        · obtain ⟨_, q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ s.property))
        · obtain ⟨_, q, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
        · obtain ⟨q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
      · intro lower
        exact Or.inl ⟨p.property, s.property, lower⟩
    | inr q =>
      change codedAttachmentLe P N r inside shadow upper p.val (ZFSet.pair P (d.freshCode q)) ↔
        ZFSet.pair p.val (b.shadow q).val ∈ r
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.2.1)
        · obtain ⟨_, t, _, s, _, eq, image, lower⟩ := h
          have same : d.freshCode q = t := (ZFSet.pair_inj.1 eq).2
          subst t
          exact d.shadow_value q s image ▸ lower
        · obtain ⟨_, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
        · obtain ⟨t, _, s, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro lower
        exact Or.inr (Or.inl ⟨p.property, d.freshCode q, d.fresh_mem q,
          (b.shadow q).val, (b.shadow q).property, rfl,
          d.shadow_entry q, lower⟩)
  | inr q =>
    cases y with
    | inl p =>
      change codedAttachmentLe P N r inside shadow upper (ZFSet.pair P (d.freshCode q)) p.val ↔
        b.upper q.1 p
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · obtain ⟨_, t, _, eq, rel⟩ := h
          have same : d.freshCode q = t := (ZFSet.pair_inj.1 eq).2
          subst t
          exact (d.upper_iff q p).1 rel
        · obtain ⟨s, _, t, _, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro above
        exact Or.inr (Or.inr (Or.inl ⟨p.property, d.freshCode q, d.fresh_mem q,
          rfl, (d.upper_iff q p).2 above⟩))
    | inr t =>
      rw [← d.fresh_le_iff]
      change codedAttachmentLe P N r inside shadow upper
        (ZFSet.pair P (d.freshCode q)) (ZFSet.pair P (d.freshCode t)) ↔
          codedAttachmentFreshLe P inside shadow upper (d.freshCode q) (d.freshCode t)
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · exact False.elim (pair_tag_not_mem P (d.freshCode q) h.1)
        · exact False.elim (pair_tag_not_mem P (d.freshCode t) h.1)
        · obtain ⟨s, _, v, _, eqQ, eqT, lower⟩ := h
          have sameQ := (ZFSet.pair_inj.1 eqQ).2
          have sameT := (ZFSet.pair_inj.1 eqT).2
          exact sameQ.symm ▸ sameT.symm ▸ lower
      · intro lower
        exact Or.inr (Or.inr (Or.inr ⟨d.freshCode q, d.fresh_mem q,
          d.freshCode t, d.fresh_mem t, rfl, rfl, lower⟩))

theorem partialOrder : PartialOrderCode d.carrier d.order where
  relation := codedAttachmentOrder_shape P N r inside shadow upper
  refl z hz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    exact (d.le_encode x x).2 (b.extension.refl x)
  antisymm z hz w hw zw wz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    exact congrArg d.encode (b.extension.antisymm
      ((d.le_encode x y).1 zw) ((d.le_encode y x).1 wz))
  trans z hz w hw v hv zw wv := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    obtain ⟨t, rfl⟩ := d.encode_surjective v hv
    exact (d.le_encode x t).2 (b.extension.trans
      ((d.le_encode x y).1 zw) ((d.le_encode y t).1 wv))

theorem encoded_meet_glb (x y : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh)) :
    GreatestLowerBoundCode d.carrier d.order (d.encode x) (d.encode y)
      (d.encode (b.extension.meet x y)) := by
  refine ⟨(d.le_encode _ _).2 (b.extension.meet_le_left x y),
    (d.le_encode _ _).2 (b.extension.meet_le_right x y), ?_⟩
  intro w hw wx wy
  obtain ⟨z, rfl⟩ := d.encode_surjective w hw
  exact (d.le_encode _ _).2 (b.extension.le_meet
    ((d.le_encode _ _).1 wx) ((d.le_encode _ _).1 wy))

theorem meetOrder : MeetOrderCode d.carrier d.order d.meetGraph := by
  apply canonicalMeetGraph_code d.partialOrder
  intro x hx y hy
  obtain ⟨s, rfl⟩ := d.encode_surjective x hx
  obtain ⟨t, rfl⟩ := d.encode_surjective y hy
  exact ⟨d.encode (b.extension.meet s t), d.encode_mem _, d.encoded_meet_glb s t⟩

theorem encoded_meet_entry (x y : ({p : ZFSet.{u} // p ∈ P} ⊕ b.Fresh)) :
    ZFSet.pair (ZFSet.pair (d.encode x) (d.encode y))
      (d.encode (b.extension.meet x y)) ∈ d.meetGraph :=
  (pair_mem_canonicalMeetGraph _ _ _ _ _).2
    ⟨d.encode_mem x, d.encode_mem y, d.encode_mem _, d.encoded_meet_glb x y⟩

end CodedTemplateAttachment

end



section

universe u

noncomputable def batchAttachmentInsideGraph (I Qs rs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ZFSet.sUnion (ZFSet.sUnion Qs),
    ∃ r ∈ ZFSet.sUnion (ZFSet.sUnion rs),
    ∃ q ∈ Q, ∃ t ∈ Q, z = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair i t) ∧
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ ZFSet.pair q t ∈ r)
    (ZFSet.prod (indexedAttachmentDomain I Qs) (indexedAttachmentDomain I Qs))

noncomputable def batchAttachmentUpperGraph (I P Qs Fs : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ZFSet.sUnion (ZFSet.sUnion Qs),
    ∃ F ∈ ZFSet.sUnion (ZFSet.sUnion Fs),
    ∃ q ∈ Q, ∃ p ∈ P, z = ZFSet.pair (ZFSet.pair i q) p ∧
      ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i F ∈ Fs ∧ p ∈ F)
    (ZFSet.prod (indexedAttachmentDomain I Qs) P)

theorem mem_batchAttachmentInsideGraph (I Qs rs z : ZFSet.{u}) :
    z ∈ batchAttachmentInsideGraph I Qs rs ↔
      ∃ i ∈ I, ∃ Q r q t, z = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair i t) ∧
        ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧ q ∈ Q ∧ t ∈ Q ∧ ZFSet.pair q t ∈ r := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, r, _, q, hq, t, ht, eq, entryQ, entryR, lower⟩ := (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, Q, r, q, t, eq, entryQ, entryR, hq, ht, lower⟩
  · rintro ⟨i, hi, Q, r, q, t, rfl, entryQ, entryR, hq, ht, lower⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, entryQ, hq⟩,
        (pair_mem_indexedAttachmentDomain I Qs i t).2 ⟨hi, Q, entryQ, ht⟩⟩,
      i, hi, Q, pair_second_mem_doubleUnion entryQ, r, pair_second_mem_doubleUnion entryR,
      q, hq, t, ht, rfl, entryQ, entryR, lower⟩

theorem mem_batchAttachmentUpperGraph (I P Qs Fs z : ZFSet.{u}) :
    z ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      ∃ i ∈ I, ∃ Q F q p, z = ZFSet.pair (ZFSet.pair i q) p ∧
        ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i F ∈ Fs ∧ q ∈ Q ∧ p ∈ P ∧ p ∈ F := by
  constructor
  · intro hz
    obtain ⟨i, hi, Q, _, F, _, q, hq, p, hp, eq, entryQ, entryF, upper⟩ := (ZFSet.mem_sep.1 hz).2
    exact ⟨i, hi, Q, F, q, p, eq, entryQ, entryF, hq, hp, upper⟩
  · rintro ⟨i, hi, Q, F, q, p, rfl, entryQ, entryF, hq, hp, upper⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, entryQ, hq⟩, hp⟩,
      i, hi, Q, pair_second_mem_doubleUnion entryQ, F, pair_second_mem_doubleUnion entryF,
      q, hq, p, hp, rfl, entryQ, entryF, upper⟩

theorem pair_mem_batchAttachmentInsideGraph (I Qs rs i q j t : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) (ZFSet.pair j t) ∈ batchAttachmentInsideGraph I Qs rs ↔
      i = j ∧ i ∈ I ∧ ∃ Q r, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i r ∈ rs ∧
        q ∈ Q ∧ t ∈ Q ∧ ZFSet.pair q t ∈ r := by
  rw [mem_batchAttachmentInsideGraph]
  constructor
  · rintro ⟨k, hk, Q, r, x, y, eq, entryQ, entryR, hx, hy, lower⟩
    have outer := ZFSet.pair_inj.1 eq
    have left := ZFSet.pair_inj.1 outer.1
    have right := ZFSet.pair_inj.1 outer.2
    rcases left with ⟨rfl, rfl⟩
    rcases right with ⟨rfl, rfl⟩
    exact ⟨rfl, hk, Q, r, entryQ, entryR, hx, hy, lower⟩
  · rintro ⟨rfl, hi, Q, r, entryQ, entryR, hq, ht, lower⟩
    exact ⟨i, hi, Q, r, q, t, rfl, entryQ, entryR, hq, ht, lower⟩

theorem pair_mem_batchAttachmentUpperGraph (I P Qs Fs i q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) p ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      i ∈ I ∧ p ∈ P ∧ ∃ Q F, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i F ∈ Fs ∧ q ∈ Q ∧ p ∈ F := by
  rw [mem_batchAttachmentUpperGraph]
  constructor
  · rintro ⟨j, hj, Q, F, x, y, eq, entryQ, entryF, hx, hy, upper⟩
    have outer := ZFSet.pair_inj.1 eq
    have inner := ZFSet.pair_inj.1 outer.1
    rcases inner with ⟨rfl, rfl⟩
    rcases outer.2 with rfl
    exact ⟨hj, hy, Q, F, entryQ, entryF, hx, upper⟩
  · rintro ⟨hi, hp, Q, F, entryQ, entryF, hq, upper⟩
    exact ⟨i, hi, Q, F, q, p, rfl, entryQ, entryF, hq, hp, upper⟩

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem inside_entry_iff (i j : {i : ZFSet.{u} // i ∈ I}) (q t : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) (ZFSet.pair j.val t) ∈ batchAttachmentInsideGraph I Qs rs ↔
      i = j ∧ q ∈ d.space i ∧ t ∈ d.space i ∧ ZFSet.pair q t ∈ d.rel i := by
  rw [pair_mem_batchAttachmentInsideGraph]
  constructor
  · rintro ⟨same, _, Q, r, entryQ, entryR, hq, ht, lower⟩
    have eqQ : d.space i = Q := d.spaces.value_eq_of_entry i entryQ
    have eqR : d.rel i = r := d.relations.value_eq_of_entry i entryR
    exact ⟨Subtype.ext same, eqQ.symm ▸ hq, eqQ.symm ▸ ht, eqR.symm ▸ lower⟩
  · rintro ⟨rfl, hq, ht, lower⟩
    exact ⟨rfl, i.property, d.space i, d.rel i, d.space_entry i, d.rel_entry i, hq, ht, lower⟩

theorem upper_entry_iff (i : {i : ZFSet.{u} // i ∈ I}) (q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) p ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      q ∈ d.space i ∧ p ∈ P ∧ p ∈ d.filter i := by
  rw [pair_mem_batchAttachmentUpperGraph]
  constructor
  · rintro ⟨_, hp, Q, F, entryQ, entryF, hq, upper⟩
    have eqQ : d.space i = Q := d.spaces.value_eq_of_entry i entryQ
    have eqF : d.filter i = F := d.filters.value_eq_of_entry i entryF
    exact ⟨eqQ.symm ▸ hq, hp, eqF.symm ▸ upper⟩
  · rintro ⟨hq, hp, upper⟩
    exact ⟨i.property, hp, d.space i, d.filter i, d.space_entry i, d.filter_entry i, hq, upper⟩

end AttachmentBatchInputs

end



namespace AttachmentBatchInputs

universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

noncomputable def freshCode (q : d.templates.Fresh) : ZFSet.{u} :=
  ZFSet.pair q.1.val q.2.val.val

theorem freshCode_mem (q : d.templates.Fresh) :
    d.freshCode q ∈ indexedAttachmentFresh I Qs rs As :=
  (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry q.1) (d.rel_entry q.1) (d.anchor_entry q.1)).2
      ((mem_freshPart _ _ _ _).2 ⟨q.2.val.property, q.2.property⟩)

theorem freshCode_injective : Function.Injective d.freshCode := by
  rintro ⟨i, q⟩ ⟨j, t⟩ equal
  have parts := ZFSet.pair_inj.1 equal
  have same : i = j := Subtype.ext parts.1
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext (Subtype.ext parts.2))

theorem freshCode_surjective : ∀ z ∈ indexedAttachmentFresh I Qs rs As,
    ∃ q : d.templates.Fresh, d.freshCode q = z := by
  intro z hz
  obtain ⟨i, hi, q, equal, _⟩ := (mem_indexedAttachmentFresh I Qs rs As z).1 hz
  subst z
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have fresh := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 hz
  have parts := (mem_freshPart _ _ _ q).1 fresh
  exact ⟨⟨j, ⟨⟨q, parts.1⟩, parts.2⟩⟩, rfl⟩

theorem freshCode_shadow_entry (q : d.templates.Fresh) :
    ZFSet.pair (d.freshCode q) (d.templates.shadow q).val ∈
      batchAttachmentShadowGraph I P Qs μs As Es := by
  apply (d.batch_shadow_entry_iff q.1 q.2.val.val _).2
  exact (d.fiber q.1).shadow_entry ⟨(), q.2⟩

theorem freshCode_shadow_value (q : d.templates.Fresh) (s : ZFSet.{u})
    (entry : ZFSet.pair (d.freshCode q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    s = (d.templates.shadow q).val := by
  have domain := indexedAttachmentFresh_subset I Qs rs As (d.freshCode_mem q)
  obtain ⟨v, _, unique⟩ := d.batch_shadow_function.2 (d.freshCode q) domain
  exact (unique s entry).trans (unique _ (d.freshCode_shadow_entry q)).symm

theorem freshCode_inside_iff (q t : d.templates.Fresh) :
    ZFSet.pair (d.freshCode q) (d.freshCode t) ∈ batchAttachmentInsideGraph I Qs rs ↔
      d.templates.Inside q t := by
  rcases q with ⟨i, q⟩
  rcases t with ⟨j, t⟩
  change ZFSet.pair (ZFSet.pair i.val q.val.val) (ZFSet.pair j.val t.val.val) ∈
    batchAttachmentInsideGraph I Qs rs ↔ _
  rw [d.inside_entry_iff]
  constructor
  · rintro ⟨same, _, _, lower⟩
    cases same
    exact ⟨rfl, lower⟩
  · rintro ⟨same, lower⟩
    cases same
    exact ⟨rfl, q.val.property, t.val.property, lower⟩

theorem freshCode_upper_iff (q : d.templates.Fresh) (p : {p : ZFSet.{u} // p ∈ P}) :
    ZFSet.pair (d.freshCode q) p.val ∈ batchAttachmentUpperGraph I P Qs Fs ↔
      d.templates.upper q.1 p := by
  change ZFSet.pair (ZFSet.pair q.1.val q.2.val.val) p.val ∈
    batchAttachmentUpperGraph I P Qs Fs ↔ _
  rw [d.upper_entry_iff]
  exact ⟨fun h => h.2.2, fun h => ⟨q.2.val.property, p.property, h⟩⟩

noncomputable def coding :
    CodedTemplateAttachment d.oldOrder d.templates
      (indexedAttachmentFresh I Qs rs As) (batchAttachmentInsideGraph I Qs rs)
      (batchAttachmentShadowGraph I P Qs μs As Es) (batchAttachmentUpperGraph I P Qs Fs) where
  freshCode := d.freshCode
  fresh_mem := d.freshCode_mem
  fresh_injective := d.freshCode_injective
  fresh_surjective := d.freshCode_surjective
  shadow_entry := d.freshCode_shadow_entry
  shadow_value := d.freshCode_shadow_value
  inside_iff := d.freshCode_inside_iff
  upper_iff := d.freshCode_upper_iff

noncomputable abbrev batchCarrier := d.coding.carrier
noncomputable abbrev batchOrder := d.coding.order
noncomputable abbrev batchMeetGraph := canonicalMeetGraph d.batchCarrier d.batchOrder

theorem batch_meetOrder : MeetOrderCode d.batchCarrier d.batchOrder d.batchMeetGraph :=
  d.coding.meetOrder

end AttachmentBatchInputs




universe u

namespace BoundedFormula

open SetFormula

def pairOfPairsFormula {n} (z a b c d : Fin n) : BoundedFormula n :=
  exMem z (exMem 0 (exMem z.succ.succ (exMem 0
    (.conj (orderedPairFormula 2 a.succ.succ.succ.succ b.succ.succ.succ.succ)
      (.conj (orderedPairFormula 0 c.succ.succ.succ.succ d.succ.succ.succ.succ)
        (orderedPairFormula z.succ.succ.succ.succ 2 0))))))

def batchAttachmentInsideEntryFormula {n} (z i qs rs qb rb : Fin n) : BoundedFormula n :=
  exMem i (exMem qb.succ (exMem rb.succ.succ (exMem 1 (exMem 2
    (.conj (pairOfPairsFormula z.succ.succ.succ.succ.succ 4 1 4 0)
      (.conj (pairMembershipFormula 4 3 qs.succ.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 4 2 rs.succ.succ.succ.succ.succ)
          (pairMembershipFormula 1 0 2))))))))

def batchAttachmentUpperEntryFormula {n} (z i p qs fs qb fb : Fin n) : BoundedFormula n :=
  exMem i (exMem qb.succ (exMem fb.succ.succ (exMem 1
    (exMem p.succ.succ.succ.succ
      (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 4 1 0)
        (.conj (pairMembershipFormula 4 3 qs.succ.succ.succ.succ.succ)
          (.conj (pairMembershipFormula 4 2 fs.succ.succ.succ.succ.succ) (.mem 0 2))))))))

end BoundedFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedTemplateShadowLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.CodedTemplateAttachment
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem old_lower_iff (p : {p : ZFSet.{u} // p ∈ P}) (q : b.Fresh) :
    ZFSet.pair p.val (d.encode (.inr q)) ∈ d.order ↔
      ZFSet.pair p.val (b.shadow q).val ∈ r :=
  d.le_encode (.inl p) (.inr q)

theorem old_upper_iff (q : b.Fresh) (p : {p : ZFSet.{u} // p ∈ P}) :
    ZFSet.pair (d.encode (.inr q)) p.val ∈ d.order ↔ b.upper q.1 p :=
  d.le_encode (.inr q) (.inl p)

theorem cross_lower_iff (q t : b.Fresh) (different : q.1 ≠ t.1) :
    ZFSet.pair (d.encode (.inr q)) (d.encode (.inr t)) ∈ d.order ↔
      b.upper q.1 (b.shadow t) :=
  (d.le_encode (.inr q) (.inr t)).trans (b.cross_le_iff q t different)

theorem encoded_cross_meet (q t : b.Fresh) (different : q.1 ≠ t.1)
    (notQT : ZFSet.pair (d.encode (.inr q)) (d.encode (.inr t)) ∉ d.order)
    (notTQ : ZFSet.pair (d.encode (.inr t)) (d.encode (.inr q)) ∉ d.order) :
    ZFSet.pair (ZFSet.pair (d.encode (.inr q)) (d.encode (.inr t)))
      (old.toMeetOrder.meet (b.shadow q) (b.shadow t)).val ∈ d.meetGraph := by
  have eq := b.cross_meet_eq q t different
    (fun lower => notQT ((d.le_encode _ _).2 lower))
    (fun lower => notTQ ((d.le_encode _ _).2 lower))
  have result := d.encoded_meet_entry (.inr q) (.inr t)
  rw [eq] at result
  exact result

theorem least_preserved {zero : ZFSet.{u}} (hzero : zero ∈ P)
    (least : ∀ p ∈ P, ZFSet.pair zero p ∈ r) :
    ∀ z ∈ d.carrier, ZFSet.pair zero z ∈ d.order := by
  intro z hz
  obtain ⟨x, rfl⟩ := d.encode_surjective z hz
  exact (d.le_encode (.inl ⟨zero, hzero⟩) x).2
    (b.least_preserved ⟨zero, hzero⟩ (fun p => least p.val p.property) x)

end PartitionPilot.Forcing.CodedTemplateAttachment

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.CodedTemplateAttachment
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem encoded_embedding_order_iff {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder b.extension)
    (function : ZFSet.IsFunc A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph)
    {x y x' y' : ZFSet.{u}} (hx : ZFSet.pair x x' ∈ graph) (hy : ZFSet.pair y y' ∈ graph) :
    ZFSet.pair x' y' ∈ d.order ↔ ZFSet.pair x y ∈ r := by
  have hxA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
  have hyA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
  obtain ⟨w, _, uniqueX⟩ := function.2 x hxA
  obtain ⟨v, _, uniqueY⟩ := function.2 y hyA
  have eqX := (uniqueX x' hx).trans (uniqueX _ (entries ⟨x, hxA⟩)).symm
  have eqY := (uniqueY y' hy).trans (uniqueY _ (entries ⟨y, hyA⟩)).symm
  rw [eqX, eqY, d.le_encode]
  exact embedding.le_iff ⟨x, hxA⟩ ⟨y, hyA⟩

theorem encoded_embedding_code {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder b.extension)
    (function : ZFSet.IsFunc A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph) :
    MeetEmbeddingCode A d.carrier r d.order μ d.meetGraph graph := by
  refine ⟨⟨function, ?_⟩, ?_, ?_⟩
  · intro x y z hx hy
    have xA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
    have yA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
    have zL := (ZFSet.pair_mem_prod.1 (function.1 hx)).2
    have refl := d.partialOrder.refl z zL
    exact source.order.antisymm x xA y yA
      ((d.encoded_embedding_order_iff source embedding function entries hx hy).1 refl)
      ((d.encoded_embedding_order_iff source embedding function entries hy hx).1 refl)
  · intro x y x' y' lower hx hy
    exact (d.encoded_embedding_order_iff source embedding function entries hx hy).2 lower
  · intro x y z x' y' z' meet hx hy hz
    have hxA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
    have hyA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
    have hzA := (ZFSet.pair_mem_prod.1 (function.1 hz)).1
    let X : {x : ZFSet.{u} // x ∈ A} := ⟨x, hxA⟩
    let Y : {y : ZFSet.{u} // y ∈ A} := ⟨y, hyA⟩
    let Z : {z : ZFSet.{u} // z ∈ A} := ⟨z, hzA⟩
    have image_eq (t : {t : ZFSet.{u} // t ∈ A}) (v : ZFSet.{u})
        (entry : ZFSet.pair t.val v ∈ graph) : v = d.encode (embedding.toFun t) := by
      obtain ⟨w, _, unique⟩ := function.2 t.val t.property
      exact (unique v entry).trans (unique _ (entries t)).symm
    have meet_eq : source.toMeetOrder.meet X Y = Z := by
      apply Subtype.ext
      obtain ⟨w, _, unique⟩ := source.operation.2 (ZFSet.pair x y)
        (ZFSet.pair_mem_prod.2 ⟨hxA, hyA⟩)
      exact (unique _ (source.toMeetOrder_meet_entry X Y)).trans (unique z meet).symm
    have mapped : embedding.toFun Z =
        b.extension.meet (embedding.toFun X) (embedding.toFun Y) := by
      rw [← meet_eq]
      exact embedding.map_meet X Y
    rw [image_eq X x' hx, image_eq Y y' hy, image_eq Z z' hz, mapped]
    exact d.encoded_meet_entry (embedding.toFun X) (embedding.toFun Y)

theorem old_embedding_code :
    MeetEmbeddingCode P d.carrier r d.order μ d.meetGraph (attachmentOldEmbeddingGraph P) := by
  apply d.encoded_embedding_code old b.oldEmbedding
    (attachmentOldEmbeddingGraph_isFunc P N)
  intro p
  exact (pair_mem_attachmentOldEmbeddingGraph P p.val p.val).2 ⟨p.property, rfl⟩

end PartitionPilot.Forcing.CodedTemplateAttachment

namespace PartitionPilot.Forcing.AttachmentBatchInputs

universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
include d

theorem batch_template_graph_entry (i : {i : ZFSet.{u} // i ∈ I})
    (q : {q : ZFSet.{u} // q ∈ d.space i}) :
    ZFSet.pair q.val (d.coding.encode (d.templates.represent i q)) ∈
      batchTemplateGraph I P Qs rs As Es i.val := by
  classical
  apply (pair_mem_batchTemplateGraph I P Qs rs As Es i.val q.val _).2
  apply (d.batch_template_entry_iff i q.val _).2
  by_cases below : (d.fiber i).templateOrder.toMeetOrder.le q
      ⟨d.anchor i, (d.fiber i).anchor_mem⟩
  · rw [d.templates.represent_old i q below]
    exact Or.inl ((d.fiber i).baseMap_entry ⟨q, below⟩)
  · rw [d.templates.represent_new i q below]
    exact Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨q.property, below⟩, rfl⟩

theorem batch_template_embedding_code (i : {i : ZFSet.{u} // i ∈ I}) :
    MeetEmbeddingCode (d.space i) d.batchCarrier (d.rel i) d.batchOrder
      (d.meet i) d.batchMeetGraph (batchTemplateGraph I P Qs rs As Es i.val) :=
  d.coding.encoded_embedding_code (d.fiber i).templateOrder (d.templates.templateEmbedding i)
    (d.batch_template_fiber_function i) (d.batch_template_graph_entry i)

end PartitionPilot.Forcing.AttachmentBatchInputs

namespace PartitionPilot.Forcing.AttachmentBatchInputs
universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

noncomputable def batchFreshNode (i : {i : ZFSet.{u} // i ∈ I}) {q : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) : d.templates.Fresh :=
  ⟨i, ⟨⟨q, ((mem_freshPart _ _ _ q).1 hq).1⟩, ((mem_freshPart _ _ _ q).1 hq).2⟩⟩

end PartitionPilot.Forcing.AttachmentBatchInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_AttachmentOldCodeLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.AttachmentBatchInputs
universe u
variable {P r μ J Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ J Qs rs μs As Es Fs Ss)

theorem old_order_iff {x y : ZFSet.{u}} (hx : x ∈ P) (hy : y ∈ P) :
    ZFSet.pair x y ∈ d.batchOrder ↔ ZFSet.pair x y ∈ r :=
  d.coding.le_encode (.inl ⟨x, hx⟩) (.inl ⟨y, hy⟩)

theorem old_meet_entry {x y z : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair x y) z ∈ μ) :
    ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph := by
  have shape := ZFSet.pair_mem_prod.1 (d.oldOrder.operation.1 entry)
  have inputs := ZFSet.pair_mem_prod.1 shape.1
  exact d.coding.old_embedding_code.map_meet x y z x y z entry
    ((pair_mem_attachmentOldEmbeddingGraph P x x).2 ⟨inputs.1, rfl⟩)
    ((pair_mem_attachmentOldEmbeddingGraph P y y).2 ⟨inputs.2, rfl⟩)
    ((pair_mem_attachmentOldEmbeddingGraph P z z).2 ⟨shape.2, rfl⟩)

theorem old_meet_iff {x y z : ZFSet.{u}} (hx : x ∈ P) (hy : y ∈ P) :
    ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ μ := by
  constructor
  · intro entry
    obtain ⟨w, old, _⟩ := d.oldOrder.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    have same : z = w :=
      (show FunctionGraphOn (ZFSet.prod d.batchCarrier d.batchCarrier) d.batchMeetGraph from
        ⟨d.batchCarrier, d.batch_meetOrder.operation⟩).unique entry (d.old_meet_entry old)
    exact same.symm ▸ old
  · exact d.old_meet_entry

end PartitionPilot.Forcing.AttachmentBatchInputs

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundActionFilterImages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

def actionImageFormula {n} (y A g F : Fin n) : BoundedFormula n :=
  exMem F (tripleMembershipFormula g.succ 0 y.succ A.succ)

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskRepresentativeCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula SetRealization
universe u

def actionSectionEntryFormula {n} (z g a p : Fin n) : BoundedFormula n :=
  exMem p (exMem p.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (tripleMembershipFormula g.succ.succ 1 0 a.succ.succ)))

def actionSectionFormula {n} (f g a p : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula p p f) (.allMem p (.allMem p.succ
    (.conj (imp (pairMembershipFormula 1 0 f.succ.succ)
      (tripleMembershipFormula g.succ.succ 1 0 a.succ.succ))
      (imp (tripleMembershipFormula g.succ.succ 1 0 a.succ.succ)
        (pairMembershipFormula 1 0 f.succ.succ)))))

theorem truth_actionSectionEntryFormula {n} (z g a p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionSectionEntryFormula z g a p) env ↔
      ∃ x ∈ env p, ∃ y ∈ env p, env z = ZFSet.pair x y ∧
        ZFSet.pair (ZFSet.pair (env g) x) y ∈ env a := by
  simp only [actionSectionEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

theorem truth_actionSectionFormula {n} (f g a p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionSectionFormula f g a p) env ↔
      env f ⊆ ZFSet.prod (env p) (env p) ∧ ∀ x ∈ env p, ∀ y ∈ env p,
        (ZFSet.pair x y ∈ env f ↔ ZFSet.pair (ZFSet.pair (env g) x) y ∈ env a) := by
  simp only [actionSectionFormula, Truth, truth_relationBetweenFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ← iff_def]
  rfl

variable {G P : Type u} [Group G] [PartialOrder P]

theorem actionSectionEntry_correct (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (g : G) (z : ZFSet.{u}) :
    Truth (actionSectionEntryFormula 0 1 2 3)
      (extend z (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        z ∈ s.graph s (a.iso g) := by
  rw [truth_actionSectionEntryFormula]
  constructor
  · rintro ⟨x, hx, y, hy, eq, rel⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨q, rfl⟩ := (s.mem_carrier y).1 hy
    change z = ZFSet.pair (s.encode p) (s.encode q) at eq
    rw [eq, s.pair_mem_graph]
    exact (a.triple_mem_actionGraph s t g p q).1 rel
  · intro member
    obtain ⟨p, eq⟩ := (s.mem_graph s (a.iso g) z).1 member
    exact ⟨s.encode p, s.encode_mem p, s.encode (a.iso g p), s.encode_mem _, eq.symm,
      (a.triple_mem_actionGraph s t g p (a.iso g p)).2 rfl⟩

theorem actionSection_correct (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (g : G) (F : ZFSet.{u}) :
    Truth (actionSectionFormula 0 1 2 3)
      (extend F (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        F = s.graph s (a.iso g) := by
  rw [truth_actionSectionFormula]
  constructor
  · rintro ⟨shape, spec⟩
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (shape hz)
      obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
      obtain ⟨q, rfl⟩ := (s.mem_carrier y).1 hy
      rw [eq, s.pair_mem_graph]
      exact (a.triple_mem_actionGraph s t g p q).1 ((spec _ hx _ hy).1 (eq ▸ hz))
    · intro hz
      obtain ⟨p, eq⟩ := (s.mem_graph s (a.iso g) z).1 hz
      exact eq ▸ (spec _ (s.encode_mem p) _ (s.encode_mem (a.iso g p))).2
        ((a.triple_mem_actionGraph s t g p (a.iso g p)).2 rfl)
  · intro eq
    subst F
    refine ⟨(s.graph_isFunc s (a.iso g)).1, ?_⟩
    intro x hx y hy
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨q, rfl⟩ := (s.mem_carrier y).1 hy
    exact (s.pair_mem_graph s (a.iso g) p q).trans (a.triple_mem_actionGraph s t g p q).symm

end BoundedFormula

namespace BoundedFormula

open SetFormula
universe u

def meetFilterFormula {n} (P r μ F : Fin n) : BoundedFormula n :=
  .conj (.allMem F (.mem 0 P.succ))
    (.conj (exMem F (.equal 0 0))
      (.conj
        (.allMem F (.allMem P.succ
          (imp (pairMembershipFormula 1 0 r.succ.succ) (.mem 0 F.succ.succ))))
        (.allMem F (.allMem F.succ (.allMem P.succ.succ
          (imp (tripleMembershipFormula 2 1 0 μ.succ.succ.succ)
            (.mem 0 F.succ.succ.succ)))))))

def restrictedActionFormula {n} (P r A g source target base : Fin n) : BoundedFormula n :=
  let entry := pairMembershipFormula 1 0 base.succ.succ
  let restricted := .conj (pairMembershipFormula 1 source.succ.succ r.succ.succ)
    (tripleMembershipFormula g.succ.succ 1 0 A.succ.succ)
  .conj (relationBetweenFormula P P base)
    (.conj (tripleMembershipFormula g source target A)
      (.allMem P (.allMem P.succ
        (.conj (imp entry restricted) (imp restricted entry)))))

end BoundedFormula

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundActionPostcomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def actionPostcomposeEntryFormula {n} (v P A g base : Fin n) : BoundedFormula n :=
  exMem P (exMem P.succ (.conj (orderedPairFormula v.succ.succ 1 0)
    (exMem P.succ.succ (.conj (pairMembershipFormula 2 0 base.succ.succ.succ)
      (tripleMembershipFormula g.succ.succ.succ 0 1 A.succ.succ.succ)))))

def actionPostcomposeFormula {n} (P A g base output : Fin n) : BoundedFormula n :=
  let entry := pairMembershipFormula 1 0 output.succ.succ
  let composed := exMem P.succ.succ
    (.conj (pairMembershipFormula 2 0 base.succ.succ.succ)
      (tripleMembershipFormula g.succ.succ.succ 0 1 A.succ.succ.succ))
  .conj (relationBetweenFormula P P output) (.allMem P (.allMem P.succ
    (.conj (imp entry composed) (imp composed entry))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskTransportFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def actionImageEqualityFormula {n} (P A g F output : Fin n) : BoundedFormula n :=
  .conj (.allMem output (.mem 0 P.succ))
    (.allMem P (.conj
      (imp (.mem 0 output.succ) (actionImageFormula 0 A.succ g.succ F.succ))
      (imp (actionImageFormula 0 A.succ g.succ F.succ) (.mem 0 output.succ))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalWordRewriteFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def actorSingletonWordFormula {n} (w zero g : Fin n) : BoundedFormula n :=
  exMem w (.conj (nonemptyTupleFormula 2 0
    (Fin.cases zero.succ (Fin.cases zero.succ (Fin.cases g.succ Fin.elim0))))
    (singletonFormula w.succ 0))

def actorDoubleWordFormula {n} (w zero unit g h : Fin n) : BoundedFormula n :=
  exMem w (exMem w.succ
    (.conj (nonemptyTupleFormula 2 1
      (Fin.cases zero.succ.succ (Fin.cases zero.succ.succ (Fin.cases g.succ.succ Fin.elim0))))
      (.conj (nonemptyTupleFormula 2 0
        (Fin.cases unit.succ.succ (Fin.cases zero.succ.succ (Fin.cases h.succ.succ Fin.elim0))))
        (unorderedPairFormula w.succ.succ 1 0))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TileStarIncomingCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem finiteWordGraph_chain_trace {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (x : B) (xs : List B) (chain : List.IsChain r (x :: xs)) :
    IterationTraceCode (natSetCode xs.length) (natSetCode (xs.length + 1))
      s.carrier R (s.encode x) (finiteWordGraph s (x :: xs)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.length_cons] using finiteWordGraph_function s (x :: xs)
  · apply (pair_mem_finiteWordGraph s (x :: xs) 0 _).2
    exact ⟨by simp, rfl⟩
  · intro i hi j _ a _ b _ succ prev next
    obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i xs.length).1 hi
    have jcode : j = natSetCode (k + 1) := succ
    obtain ⟨_, avalue⟩ := (pair_mem_finiteWordGraph s (x :: xs) k a).1 prev
    obtain ⟨_, bvalue⟩ := (pair_mem_finiteWordGraph s (x :: xs) (k + 1) b).1 (jcode ▸ next)
    rw [avalue, bvalue, edges]
    simpa only [List.get_eq_getElem] using
      chain.getElem k (by simpa only [List.length_cons] using Nat.succ_lt_succ hk)





inductive RelationPathSteps {B : Type u} (r : B → B → Prop) : Nat → B → B → Prop
  | nil (x : B) : RelationPathSteps r 0 x x
  | tail {n : Nat} {x y z : B} : RelationPathSteps r n x y → r y z → RelationPathSteps r (n + 1) x z

theorem chain_append_last {B : Type u} {r : B → B → Prop} {x z : B} {xs : List B}
    (chain : List.IsChain r (x :: xs)) (edge : r ((x :: xs).getLast (List.cons_ne_nil _ _)) z) :
    List.IsChain r (x :: (xs ++ [z])) := by
  induction xs generalizing x with
  | nil => exact .cons_cons edge (.singleton _)
  | cons next rest ih =>
    obtain ⟨first, tail⟩ := List.isChain_cons_cons.mp chain
    exact .cons_cons first (ih tail (by simpa only [List.getLast_cons_cons] using edge))

namespace RelationPathSteps
variable {B : Type u} {r : B → B → Prop} {n : Nat} {x y z : B}

theorem append {m : Nat} (first : RelationPathSteps r n x y) (second : RelationPathSteps r m y z) :
    RelationPathSteps r (n + m) x z := by
  induction second with
  | nil => exact first
  | tail previous edge ih => exact .tail (ih first) edge

theorem cons (edge : r x y) (path : RelationPathSteps r n y z) : RelationPathSteps r (n + 1) x z := by
  simpa only [Nat.add_comm] using (RelationPathSteps.tail (RelationPathSteps.nil x) edge).append path

theorem chain (path : RelationPathSteps r n x y) :
    ∃ xs : List B, List.IsChain r (x :: xs) ∧
      (x :: xs).getLast (List.cons_ne_nil _ _) = y ∧ xs.length = n := by
  induction path with
  | nil x => exact ⟨[], .singleton _, rfl, rfl⟩
  | @tail n x y z previous edge ih =>
    obtain ⟨xs, chain, last, length⟩ := ih
    refine ⟨xs ++ [z], chain_append_last chain (last.symm ▸ edge), ?_, ?_⟩
    · simp
    · simp only [List.length_append, List.length_singleton, length]

end RelationPathSteps

theorem IterationTraceCode.pathSteps {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {n : Nat} {t : ZFSet.{u}} {x : B}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier R (s.encode x) t) :
    ∀ k ≤ n, ∀ y, ZFSet.pair (natSetCode k) (s.encode y) ∈ t → RelationPathSteps r k x y := by
  intro k
  induction k with
  | zero =>
    intro _ y entry
    have same := (show FunctionGraphOn (natSetCode (n + 1)) t from ⟨s.carrier, trace.function⟩).unique trace.seed entry
    have equal := s.injective same
    subst y
    exact .nil x
  | succ k ih =>
    intro hk y entry
    obtain ⟨a, prev, _⟩ := trace.function.2 (natSetCode k) ((natSetCode_mem_iff _ _).2 (by omega))
    obtain ⟨b, equal⟩ := (s.mem_carrier a).1 (ZFSet.pair_mem_prod.1 (trace.function.1 prev)).2
    have previous : ZFSet.pair (natSetCode k) (s.encode b) ∈ t := equal.symm ▸ prev
    have edge := trace.next (natSetCode k) ((natSetCode_mem_iff _ _).2 (by omega))
      (natSetCode (k + 1)) ((natSetCode_mem_iff _ _).2 (by omega))
      _ (s.encode_mem b) _ (s.encode_mem y) rfl previous entry
    exact .tail (ih (by omega) b previous) ((edges b y).1 edge)

theorem RelationPathSteps.exists_trace {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {n : Nat} {x y : B} (path : RelationPathSteps r n x y) :
    ∃ xs : List B, IterationTraceCode (natSetCode n) (natSetCode (n + 1))
      s.carrier R (s.encode x) (finiteWordGraph s xs) ∧ ZFSet.pair (natSetCode n) (s.encode y) ∈ finiteWordGraph s xs := by
  obtain ⟨xs, chain, last, rfl⟩ := path.chain
  refine ⟨x :: xs, finiteWordGraph_chain_trace s r edges x xs chain, ?_⟩
  apply (pair_mem_finiteWordGraph s (x :: xs) xs.length _).2
  refine ⟨by simp, ?_⟩
  rw [← last]
  simp only [List.get_eq_getElem, List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel]

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def relationPathLengths (A R root : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ y ∈ A, ∃ d ∈ ZFSet.omega, ∃ t ∈ M.finiteWords A,
    z = ZFSet.pair n y ∧ d = insert n n ∧ IterationTraceCode n d A R root t ∧ ZFSet.pair n y ∈ t)
    (ZFSet.prod ZFSet.omega A)

theorem pair_mem_relationPathLengths (A R root n y : ZFSet.{u}) :
    ZFSet.pair n y ∈ M.relationPathLengths A R root ↔ n ∈ ZFSet.omega ∧ y ∈ A ∧
      ∃ d ∈ ZFSet.omega, ∃ t ∈ M.finiteWords A,
        d = insert n n ∧ IterationTraceCode n d A R root t ∧ ZFSet.pair n y ∈ t := by
  rw [relationPathLengths, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n', hn, y', hy, d, hd, t, ht, equal, succ, trace, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hn, hy, d, hd, t, ht, succ, trace, entry⟩
  · rintro ⟨hn, hy, d, hd, t, ht, succ, trace, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hn, hy⟩, n, hn, y, hy, d, hd, t, ht, rfl, succ, trace, entry⟩

theorem relationPathLengths_iff_steps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (hB : s.carrier ∈ M.sets) (root y : B) (n : Nat) :
    ZFSet.pair (natSetCode n) (s.encode y) ∈ M.relationPathLengths s.carrier R (s.encode root) ↔
      RelationPathSteps r n root y := by
  rw [M.pair_mem_relationPathLengths]
  constructor
  · rintro ⟨_, _, d, _, t, _, succ, trace, out⟩
    have dcode : d = natSetCode (n + 1) := succ
    exact (dcode ▸ trace).pathSteps s r edges n (Nat.le_refl n) y out
  · intro path
    obtain ⟨xs, trace, out⟩ := path.exists_trace s r edges
    exact ⟨natSetCode_mem_omega n, s.encode_mem y, natSetCode (n + 1), natSetCode_mem_omega _,
      finiteWordGraph s xs, finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
      rfl, trace, out⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def shortestLengthGraph (A lengths : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ A, ∃ n ∈ ZFSet.omega, z = ZFSet.pair y n ∧
    ZFSet.pair n y ∈ lengths ∧ ∀ k ∈ n, ZFSet.pair k y ∉ lengths) (ZFSet.prod A ZFSet.omega)

theorem pair_mem_shortestLengthGraph (A lengths y n : ZFSet.{u}) :
    ZFSet.pair y n ∈ shortestLengthGraph A lengths ↔ y ∈ A ∧ n ∈ ZFSet.omega ∧
      ZFSet.pair n y ∈ lengths ∧ ∀ k ∈ n, ZFSet.pair k y ∉ lengths := by
  rw [shortestLengthGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y', hy, n', hn, equal, entry, minimal⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hy, hn, entry, minimal⟩
  · rintro ⟨hy, hn, entry, minimal⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hy, hn⟩, y, hy, n, hn, rfl, entry, minimal⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def relationDepthGraph (A R root : ZFSet.{u}) : ZFSet.{u} :=
  shortestLengthGraph A (M.relationPathLengths A R root)

end TransitiveGround

variable {B : Type u} (s : Presentation B) (depth : B → Nat) {lengths : ZFSet.{u}}
variable (valid : ∀ x, ZFSet.pair (natSetCode (depth x)) (s.encode x) ∈ lengths)
variable (minimal : ∀ x n, ZFSet.pair (natSetCode n) (s.encode x) ∈ lengths → depth x ≤ n)
include valid minimal

theorem shortestLengthGraph_entry (x : B) (n : Nat) :
    ZFSet.pair (s.encode x) (natSetCode n) ∈ shortestLengthGraph s.carrier lengths ↔ n = depth x := by
  rw [pair_mem_shortestLengthGraph]
  constructor
  · rintro ⟨_, _, entry, least⟩
    have lower := minimal x n entry
    have notLower : ¬ depth x < n := fun h => least _ ((natSetCode_mem_iff _ _).2 h) (valid x)
    omega
  · rintro rfl
    refine ⟨s.encode_mem x, natSetCode_mem_omega _, valid x, ?_⟩
    intro k hk entry
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode k (depth x)).1 hk
    exact Nat.not_lt_of_ge (minimal x n entry) hn

theorem shortestLengthGraph_eq_graph :
    shortestLengthGraph s.carrier lengths = s.graph natPresentation (fun x => ⟨depth x⟩) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, n, hn, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have equal := (shortestLengthGraph_entry s depth valid minimal x n).1 entry
    exact (s.pair_mem_graph natPresentation (fun x => ⟨depth x⟩) x ⟨n⟩).2 (congrArg ULift.up equal.symm)
  · intro entry
    obtain ⟨x, rfl⟩ := (s.mem_graph natPresentation (fun x => ⟨depth x⟩) z).1 entry
    exact (shortestLengthGraph_entry s depth valid minimal x (depth x)).2 rfl

end PartitionPilot.Forcing



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars
open Forcing SetRealization SetFormula
universe u
variable (J S R : Type u) [Group J] (request : S → R)
local notation "adj" => fun x y => ∃ d : Dart J S R, source J S R request d = x ∧ target J S R request d = y

theorem Follows.pathSteps {x y : Vertex J S R} {L : List (Dart J S R)}
    (path : Follows J S R request x L y) : RelationPathSteps adj L.length x y := by
  induction path with
  | nil => exact .nil _
  | cons d tail ih => exact ih.cons ⟨d, rfl, rfl⟩

theorem follows_of_pathSteps {n : Nat} {x y : Vertex J S R} (path : RelationPathSteps adj n x y) :
    ∃ L : List (Dart J S R), Follows J S R request x L y ∧ L.length = n := by
  induction path with
  | nil x => exact ⟨[], Follows.nil x, rfl⟩
  | @tail n x y z previous edge ih =>
    obtain ⟨L, followed, length⟩ := ih
    obtain ⟨d, src, tgt⟩ := edge
    have oneEdge : Follows J S R request y [d] z := by
      rw [← src, ← tgt]
      exact Follows.cons d (Follows.nil _)
    exact ⟨L ++ [d], follows_append J S R request followed oneEdge,
      by simp only [List.length_append, List.length_singleton, length]⟩

theorem depth_pathSteps (x : Vertex J S R) :
    RelationPathSteps adj (depth J S R request x) (root J S R) x :=
  (rootPath_follows J S R request x).pathSteps J S R request

theorem depth_le_steps {x : Vertex J S R} {n : Nat}
    (path : RelationPathSteps adj n (root J S R) x) : depth J S R request x ≤ n := by
  obtain ⟨L, followed, rfl⟩ := follows_of_pathSteps J S R request path
  exact rootPath_shortest J S R request followed

variable (M : Forcing.TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (s : Presentation (Vertex J S R)) {adjacency : ZFSet.{u}}
variable (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ adjacency ↔
  ∃ d : Dart J S R, TileStars.source J S R request d = x ∧ TileStars.target J S R request d = y)
variable (hV : s.carrier ∈ M.sets)

include pairing unions separation infinite edges hV in
theorem depthGraph_eq_graph :
    M.relationDepthGraph s.carrier adjacency (s.encode (root J S R)) =
      s.graph natPresentation (fun x => ⟨depth J S R request x⟩) := by
  change shortestLengthGraph s.carrier
    (M.relationPathLengths s.carrier adjacency (s.encode (root J S R))) = _
  apply shortestLengthGraph_eq_graph s (depth J S R request)
    (lengths := M.relationPathLengths s.carrier adjacency (s.encode (root J S R)))
  · intro x
    exact (M.relationPathLengths_iff_steps pairing unions separation infinite s
      (fun x y => ∃ d : Dart J S R, source J S R request d = x ∧ target J S R request d = y)
      edges hV (root J S R) x (depth J S R request x)).2 (depth_pathSteps J S R request x)
  · intro x n entry
    exact depth_le_steps J S R request
      ((M.relationPathLengths_iff_steps pairing unions separation infinite s
        (fun x y => ∃ d : Dart J S R, source J S R request d = x ∧ target J S R request d = y)
        edges hV (root J S R) x n).1 entry)

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalCopyRelations
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

abbrev FlatLabel := External J f.Letters × A

noncomputable def flatVertex (r : R) : Option (f.Child r) → IdealEmbedding P (f.tile r).order
  | none => (f.tile r).root
  | some j => (f.tile r).child j

def flatWord (w : External J f.Letters) (r : R) : Option (f.Child r) → External J f.Letters
  | none => w
  | some j => w * generator J f.Letters ⟨r, j⟩

theorem flatVertex_cover (r : R) (z : (f.tile r).Space) :
    ∃ i x, (f.flatVertex r i).toFun x = z := by
  rcases (f.tile r).cover z with ⟨x, eq⟩ | ⟨j, x, eq⟩
  · exact ⟨none, x, eq⟩
  · exact ⟨some j, x, eq⟩

theorem flatVertex_copy (w : External J f.Letters) (r : R) (i : Option (f.Child r)) (x : A) :
    (f.placedTile a w r).toFun ((f.flatVertex r i).toFun x) =
      (f.copy a (f.flatWord w r i)).toFun x := by
  cases i with
  | none => exact f.root_identification a w r x
  | some j => exact f.child_identification a w r j x

inductive FlatStep : f.FlatLabel (J := J) → f.FlatLabel (J := J) → Prop
  | coordinate (w : External J f.Letters) (j : J) (x : A) :
      FlatStep (w * old J f.Letters j, x) (w, (a.iso j).toFun x)
  | tile (w : External J f.Letters) (r : R) (i j : Option (f.Child r)) (x y : A)
      (equal : (f.flatVertex r i).toFun x = (f.flatVertex r j).toFun y) :
      FlatStep (f.flatWord w r i, x) (f.flatWord w r j, y)
  | symm {x y} : FlatStep x y → FlatStep y x

def FlatPath : f.FlatLabel (J := J) → f.FlatLabel (J := J) → Prop := Relation.ReflTransGen (f.FlatStep a)

theorem FlatPath.symm {x y : f.FlatLabel (J := J)} (h : f.FlatPath a x y) : f.FlatPath a y x := by
  let : Std.Symm (f.FlatStep a) := ⟨fun _ _ step => FlatStep.symm step⟩
  exact (Relation.ReflTransGen.stdSymm (r := f.FlatStep a)).symm x y h

theorem FlatStep.copy_eq {x y : f.FlatLabel (J := J)} (h : f.FlatStep a x y) :
    (f.copy a x.1).toFun x.2 = (f.copy a y.1).toFun y.2 := by
  induction h with
  | coordinate w j x => exact f.copy_coordinate a w j x
  | tile w r i j x y equal =>
    rw [← f.flatVertex_copy a w r i x, ← f.flatVertex_copy a w r j y, equal]
  | symm h ih => exact ih.symm

theorem FlatPath.copy_eq {x y : f.FlatLabel (J := J)} (h : f.FlatPath a x y) :
    (f.copy a x.1).toFun x.2 = (f.copy a y.1).toFun y.2 := by
  induction h with
  | refl => rfl
  | tail path step ih => exact ih.trans (FlatStep.copy_eq f a step)

def flatSetoid : Setoid (f.FlatLabel (J := J)) where
  r := f.FlatPath a
  iseqv := ⟨fun _ => Relation.ReflTransGen.refl,
    fun h => FlatPath.symm f a h, fun h k => h.trans k⟩

def FlatQuotient := Quotient (f.flatSetoid a)

def flatClass (w : External J f.Letters) (x : A) : f.FlatQuotient a :=
  Quotient.mk (f.flatSetoid a) (w, x)

theorem flatClass_coordinate (w : External J f.Letters) (j : J) (x : A) :
    f.flatClass a (w * old J f.Letters j) x = f.flatClass a w ((a.iso j).toFun x) :=
  Quotient.sound (Relation.ReflTransGen.single (FlatStep.coordinate w j x))

theorem flatClass_tile (w : External J f.Letters) (r : R) (i j : Option (f.Child r)) (x y : A)
    (equal : (f.flatVertex r i).toFun x = (f.flatVertex r j).toFun y) :
    f.flatClass a (f.flatWord w r i) x = f.flatClass a (f.flatWord w r j) y :=
  Quotient.sound (Relation.ReflTransGen.single (FlatStep.tile w r i j x y equal))

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_ExternalCopyDescent
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

noncomputable def flatTileValue (w : External J f.Letters) (r : R)
    (z : (f.tile r).Space) : f.FlatQuotient a :=
  f.flatClass a (f.flatWord w r (Classical.choose (f.flatVertex_cover r z)))
    (Classical.choose (Classical.choose_spec (f.flatVertex_cover r z)))

theorem flatTileValue_vertex (w : External J f.Letters) (r : R)
    (i : Option (f.Child r)) (x : A) :
    f.flatTileValue a w r ((f.flatVertex r i).toFun x) =
      f.flatClass a (f.flatWord w r i) x := by
  unfold flatTileValue
  apply f.flatClass_tile a
  exact Classical.choose_spec (Classical.choose_spec (f.flatVertex_cover r _))

noncomputable def flatIncidenceValue :
    (v : TileStars.Vertex J f.Letters R) → f.Space v → f.FlatQuotient a
  | .inl v, x => f.flatClass a (representative J f.Letters v) x
  | .inr c, x => f.flatTileValue a c.1 c.2 x

theorem flatIncidenceValue_copy (w : External J f.Letters) (x : A) :
    f.flatIncidenceValue a (.inl (point J f.Letters w)) ((a.chart w).toFun x) =
      f.flatClass a w x := by
  change f.flatClass a (representative J f.Letters (point J f.Letters w))
    ((a.iso (coordinate J f.Letters w)).toFun x) = _
  rw [← f.flatClass_coordinate, coordinate_spec]

theorem flatIncidence_stem (w : External J f.Letters) (r : R) :
    (f.diagram a).Equation (f.flatIncidenceValue a) (.inl (w, r), true) := by
  intro x
  change f.flatIncidenceValue a (.inl (point J f.Letters w)) x.val =
    f.flatTileValue a w r ((f.tile r).root.toFun ((a.chart w).inverse x.val))
  have vertex := f.flatTileValue_vertex a w r none ((a.chart w).inverse x.val)
  change f.flatTileValue a w r ((f.tile r).root.toFun ((a.chart w).inverse x.val)) =
    f.flatClass a w ((a.chart w).inverse x.val) at vertex
  rw [vertex]
  have eq := f.flatIncidenceValue_copy a w ((a.chart w).inverse x.val)
  erw [(a.chart w).right_inverse] at eq
  exact eq

theorem flatIncidence_branch (w : External J f.Letters) (r : R) (j : f.Child r) :
    (f.diagram a).Equation (f.flatIncidenceValue a) (.inr (w, ⟨r, j⟩), true) := by
  intro x
  let i := f.vertexIdealIso ((f.tile r).child j)
  obtain ⟨y, rfl⟩ : ∃ y, i.toFun y = x := ⟨i.inverse x, i.right_inverse x⟩
  change f.flatTileValue a w r (((f.tile r).child j).toFun y) =
    f.flatIncidenceValue a (.inl (point J f.Letters (w * generator J f.Letters ⟨r, j⟩)))
      ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val
  have formula : ((f.edgeOverlap a (.inr (w, ⟨r, j⟩))).toFun (i.toFun y)).val =
      (a.chart (w * generator J f.Letters ⟨r, j⟩)).toFun y := f.branch_formula a w r j y
  rw [formula, f.flatIncidenceValue_copy]
  exact f.flatTileValue_vertex a w r (some j) y

theorem flatIncidence_edges (d : TileStars.Dart J f.Letters R) :
    (f.diagram a).Equation (f.flatIncidenceValue a) d := by
  rcases d with ⟨e, b⟩
  have forward : (f.diagram a).Equation (f.flatIncidenceValue a) (e, true) := by
    cases e with
    | inl c => exact f.flatIncidence_stem a c.1 c.2
    | inr c => exact f.flatIncidence_branch a c.1 c.2.1 c.2.2
  cases b
  · exact (f.diagram a).equation_of_reverse (f.flatIncidenceValue a) (e, false) forward
  · exact forward

noncomputable def toFlatQuotient (z : f.Node a) : f.FlatQuotient a :=
  (f.diagram a).descend (f.flatIncidenceValue a) (f.flatIncidence_edges a) z

theorem toFlatQuotient_copy (w : External J f.Letters) (x : A) :
    f.toFlatQuotient a ((f.copy a w).toFun x) = f.flatClass a w x := by
  change (f.diagram a).descend (f.flatIncidenceValue a) (f.flatIncidence_edges a)
    (((f.diagram a).vertex (.inl (point J f.Letters w))).toFun ((a.chart w).toFun x)) = _
  erw [(f.diagram a).descend_vertex, f.flatIncidenceValue_copy]

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_ExternalCopyQuotient
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

noncomputable def fromFlatQuotient : f.FlatQuotient a → f.Node a :=
  Quotient.lift (fun x => (f.copy a x.1).toFun x.2)
    (fun _ _ path => FlatPath.copy_eq f a path)

theorem fromFlatQuotient_class (w : External J f.Letters) (x : A) :
    f.fromFlatQuotient a (f.flatClass a w x) = (f.copy a w).toFun x := rfl

noncomputable def flatQuotientEquiv : f.FlatQuotient a ≃ f.Node a where
  toFun := f.fromFlatQuotient a
  invFun := f.toFlatQuotient a
  left_inv q := by
    induction q using Quotient.ind with
    | _ x => exact f.toFlatQuotient_copy a x.1 x.2
  right_inv z := by
    obtain ⟨w, x, rfl⟩ := f.copy_cover a z
    rw [f.toFlatQuotient_copy, f.fromFlatQuotient_class]

theorem flatQuotientEquiv_class (w : External J f.Letters) (x : A) :
    f.flatQuotientEquiv a (f.flatClass a w x) = (f.copy a w).toFun x := rfl

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GrowthLayerSourceCongruence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

inductive CodedGrowthLayer (M : TransitiveGround.{u})
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (L r μ birth t : ZFSet.{u}) : Type (u + 1) where
  | countablePoints (D : ZFSet.{u}) (ground : D ∈ M.sets)
      (small : M.groundEmbeddable D ZFSet.omega)
      (cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → x ∈ D)
  | copies (I parts : ZFSet.{u}) (groundI : I ∈ M.sets)
      (small : M.groundEmbeddable I ZFSet.omega) (groundParts : parts ∈ M.sets)
      (index e : ZFSet.{u} → ZFSet.{u}) (earlier : ∀ i ∈ I, index i ∈ t)
      (groundCopy : ∀ i ∈ I, e i ∈ M.sets)
      (embedding : ∀ i ∈ I, MeetEmbeddingCode (Space (index i)) L
        (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i))
      (cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → ∃ i ∈ I, ZFSet.pair i x ∈ parts)
      (inCopy : ∀ i ∈ I, ∀ x ∈ L, ZFSet.pair i x ∈ parts →
        x ∈ relationImage (Space (index i)) L (e i))
  | separated (I : Type u) (index e : I → ZFSet.{u}) (earlier : ∀ i, index i ∈ t)
      (groundCopy : ∀ i, e i ∈ M.sets)
      (embedding : ∀ i, MeetEmbeddingCode (Space (index i)) L
        (sourceOrder (index i)) r (sourceMeet (index i)) μ (e i))
      (component : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} → I)
      (cover : ∀ x : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth},
        x.val ∈ relationImage (Space (index (component x))) L (e (component x)))
      (separation : ∀ x y : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth},
        component x ≠ component y → OldBridgeCode L r μ birth t x.val y.val)

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableLayerCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def countableLayerFormula {n} (L birth t D N injection : Fin n) : BoundedFormula n :=
  .conj (injectionFormula D N injection)
    (.allMem L (imp (pairMembershipFormula 0 t.succ birth.succ) (.mem 0 D.succ)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedGrowthLayerFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def oldBridgeFormula {n} (L r μ birth t x y : Fin n) : BoundedFormula n :=
  disj
    (exMem L (exMem t.succ (.conj
      (tripleMembershipFormula x.succ.succ y.succ.succ 1 μ.succ.succ)
      (pairMembershipFormula 1 0 birth.succ.succ))))
    (exMem L (exMem t.succ (.conj (pairMembershipFormula 1 0 birth.succ.succ)
      (disj
        (.conj (pairMembershipFormula x.succ.succ 1 r.succ.succ)
          (pairMembershipFormula 1 y.succ.succ r.succ.succ))
        (.conj (pairMembershipFormula y.succ.succ 1 r.succ.succ)
          (pairMembershipFormula 1 x.succ.succ r.succ.succ))))))





def meetEmbeddingFormula {n} (P L rP rL μP μL e : Fin n) : BoundedFormula n :=
  let lift4 (i : Fin n) := i.succ.succ.succ.succ
  let lift6 (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .conj (injectionFormula P L e)
    (.conj
      (.allMem P (.allMem P.succ (.allMem L.succ.succ (.allMem L.succ.succ.succ
        (imp (.conj (pairMembershipFormula 3 2 (lift4 rP))
          (.conj (pairMembershipFormula 3 1 (lift4 e))
            (pairMembershipFormula 2 0 (lift4 e))))
          (pairMembershipFormula 1 0 (lift4 rL)))))))
      (.allMem P (.allMem P.succ (.allMem P.succ.succ
        (.allMem L.succ.succ.succ (.allMem L.succ.succ.succ.succ
          (.allMem L.succ.succ.succ.succ.succ
            (imp (.conj (tripleMembershipFormula 5 4 3 (lift6 μP))
              (.conj (pairMembershipFormula 5 2 (lift6 e))
                (.conj (pairMembershipFormula 4 1 (lift6 e))
                  (pairMembershipFormula 3 0 (lift6 e)))))
              (tripleMembershipFormula 2 1 0 (lift6 μL))))))))))





def groupEmbeddingFormula {n} (G H mG mH oneG oneH e : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .conj (injectionFormula G H e) (.conj (pairMembershipFormula oneG oneH e)
    (.allMem G (.allMem G.succ (.allMem G.succ.succ
      (.allMem H.succ.succ.succ (.allMem H.succ.succ.succ.succ
        (.allMem H.succ.succ.succ.succ.succ
          (imp (.conj (tripleMembershipFormula 5 4 3 (lift mG))
            (.conj (pairMembershipFormula 5 2 (lift e))
              (.conj (pairMembershipFormula 4 1 (lift e))
                (pairMembershipFormula 3 0 (lift e)))))
            (tripleMembershipFormula 2 1 0 (lift mH))))))))))

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def doubleUnionMemberFormula {n} (x f : Fin n) : BoundedFormula n :=
  exMem f (exMem 0 (.mem x.succ.succ 0))

def doubleUnionEquationFormula {n} (B f : Fin n) : BoundedFormula n :=
  .conj (.allMem B (doubleUnionMemberFormula 0 f.succ))
    (.allMem f (.allMem 0 (.allMem 0 (.mem 0 B.succ.succ.succ))))

def copyEmbeddingFamilyFormula {n}
    (Qs rs μs L r μ t I Indices Maps W QB RB MB : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem I (.allMem t.succ (.allMem W.succ.succ (.allMem QB.succ.succ.succ
    (.allMem RB.succ.succ.succ.succ (.allMem MB.succ.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 5 4 (lift Indices))
        (.conj (pairMembershipFormula 5 3 (lift Maps))
          (.conj (pairMembershipFormula 4 2 (lift Qs))
            (.conj (pairMembershipFormula 4 1 (lift rs))
              (pairMembershipFormula 4 0 (lift μs))))))
        (meetEmbeddingFormula 2 (lift L) 1 (lift r) 0 (lift μ) 3)))))))

def copyImageCoverFormula {n} (Qs L t I parts Indices Maps W QB : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  .allMem I (.allMem t.succ (.allMem W.succ.succ (.allMem QB.succ.succ.succ
    (.allMem L.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 4 3 (lift Indices))
        (.conj (pairMembershipFormula 4 2 (lift Maps))
          (.conj (pairMembershipFormula 3 1 (lift Qs))
            (pairMembershipFormula 4 0 (lift parts)))))
        (imageMemberFormula 0 1 2))))))

end BoundedFormula





namespace BoundedFormula

def copyLayerFormula {n}
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB : Fin n) : BoundedFormula n :=
  .conj (doubleUnionEquationFormula QB Qs)
    (.conj (doubleUnionEquationFormula RB rs)
      (.conj (doubleUnionEquationFormula MB μs)
        (.conj (injectionFormula I N injection)
          (.conj (functionFormula I t Indices)
            (.conj (functionFormula I W Maps)
              (.conj (copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB)
                (.conj (.allMem L (imp (pairMembershipFormula 0 t.succ birth.succ)
                  (exMem I.succ (pairMembershipFormula 0 1 parts.succ.succ))))
                  (copyImageCoverFormula Qs L t I parts Indices Maps W QB))))))))

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def componentImageCoverFormula {n} (Qs L t I Components Indices Maps W QB : Fin n) :
    BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  .allMem I (.allMem t.succ (.allMem W.succ.succ (.allMem QB.succ.succ.succ
    (.allMem L.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 4 3 (lift Indices))
        (.conj (pairMembershipFormula 4 2 (lift Maps))
          (.conj (pairMembershipFormula 3 1 (lift Qs))
            (pairMembershipFormula 0 4 (lift Components)))))
        (imageMemberFormula 0 1 2))))))

def componentSeparationFormula {n} (L r μ birth t F I Components : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  .allMem F (.allMem F.succ (.allMem I.succ.succ (.allMem I.succ.succ.succ
    (imp (.conj (pairMembershipFormula 3 1 (lift Components))
      (.conj (pairMembershipFormula 2 0 (lift Components)) (.neg (.equal 1 0))))
      (oldBridgeFormula (lift L) (lift r) (lift μ) (lift birth) (lift t) 3 2)))))

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def separatedLayerWitness (I Indices Maps W Components F : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 6 (Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
    (Fin.cases Maps (Fin.cases W (Fin.cases Components (fun _ => F)))))))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def growthTagFormula : (k : Nat) → {n : Nat} → Fin n → BoundedFormula n
  | 0, _, z => emptyFormula z
  | k + 1, _, z => exMem z (.conj (successorFormula z.succ 0) (growthTagFormula k 0))

def countableTaggedLayerFormula {n} (z tag D injection L birth t N : Fin n) : BoundedFormula n :=
  .conj (growthTagFormula 0 tag)
    (.conj (nonemptyTupleFormula 2 z (Fin.cases tag (Fin.cases D (fun _ => injection))))
      (countableLayerFormula L birth t D N injection))

def copyTaggedLayerFormula {n}
    (z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB : Fin n) :
    BoundedFormula n :=
  .conj (growthTagFormula 1 tag)
    (.conj (nonemptyTupleFormula 6 z (Fin.cases tag (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (fun _ => injection))))))))
      (copyLayerFormula Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB))

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveLiftAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem AttachmentBatchInputs.separator_function
    {D rD μD J Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss) : ZFSet.IsFunc J D Ss := by
  refine ⟨?_, d.separators.to_isFunc.2⟩
  intro z hz
  obtain ⟨j, hj, e, rfl⟩ := d.separators.shape z hz
  have equal := d.separators.value_eq_of_entry ⟨j, hj⟩ hz
  exact ZFSet.pair_mem_prod.2 ⟨hj, equal ▸ (d.fiber ⟨j, hj⟩).separator_mem⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundChoiceEnumerationSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def enumerationRemainderFormula {n} (R A a p : Fin n) : BoundedFormula n :=
  .conj (.allMem R (.mem 0 A.succ)) (.allMem A
    (.conj (imp (.mem 0 R.succ)
      (.neg (exMem a.succ (pairMembershipFormula 0 1 p.succ.succ))))
      (imp (.neg (exMem a.succ (pairMembershipFormula 0 1 p.succ.succ)))
        (.mem 0 R.succ))))

def choiceEnumerationStepFormula {n} (A F c a p y : Fin n) : BoundedFormula n :=
  disj (exMem F (.conj (enumerationRemainderFormula 0 A.succ a.succ p.succ)
    (pairMembershipFormula 0 y.succ c.succ)))
    (.conj (.neg (exMem A (.neg (exMem a.succ
      (pairMembershipFormula 0 1 p.succ.succ))))) (.equal y A))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def decisionStepEntryFormula : BoundedFormula 6 :=
  exMem 1 (exMem 3 (exMem 3 (exMem 5 (exMem 8
    (.conj (pairOfPairsFormula 5 4 3 2 1)
      (.conj (successorFormula 2 4)
        (.conj (pairMembershipFormula 1 3 8) (tripleMembershipFormula 1 4 0 10))))))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementCoarseImageNames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u v

namespace BoundedFormula

def coarseClassImageFormula : BoundedFormula 4 :=
  .conj (.mem 0 1) (exMem 2 (.conj (.mem 0 2) (pairMembershipFormula 1 0 4)))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FlatLimitConditionFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

def assignmentCutFormula {n : Nat} (cut levels alpha A : Fin n) : BoundedFormula n :=
  .conj
    (.allMem cut (.conj (.mem 0 A.succ)
      (exMem alpha.succ (pairMembershipFormula 1 0 levels.succ.succ))))
    (.allMem A (imp (exMem alpha.succ (pairMembershipFormula 1 0 levels.succ.succ))
      (.mem 0 cut.succ)))

end BoundedFormula

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing

universe u






def ActionAgreementBelow (P r A g h v : ZFSet.{u}) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x v ∈ r →
    (ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair h x) y ∈ A)

namespace ActionAgreementBelow

variable {P r A g h v : ZFSet.{u}}
variable (agree : ActionAgreementBelow P r A g h v)
include agree

theorem entry_eq {G m e x y z : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hh : h ∈ G) (hx : x ∈ P)
    (lower : ZFSet.pair x v ∈ r)
    (first : ZFSet.pair (ZFSet.pair g x) y ∈ A)
    (second : ZFSet.pair (ZFSet.pair h x) z ∈ A) : y = z := by
  have hy := (ZFSet.pair_mem_prod.1 (action.function.1 first)).2
  have shared := (agree x hx y hy lower).1 first
  obtain ⟨w, _, unique⟩ := action.function.2 (ZFSet.pair h x) (ZFSet.pair_mem_prod.2 ⟨hh, hx⟩)
  exact (unique y shared).trans (unique z second).symm

end ActionAgreementBelow

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInvariantSuccessors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u

namespace AttachmentBatchInputs

variable {P0 r0 μ0 D rD μD J Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss)

theorem original_carrier_subset (original : P0 ⊆ D) : P0 ⊆ d.batchCarrier :=
  fun _ hx => old_mem_taggedExtension (original hx)

theorem original_order_iff (original : P0 ⊆ D)
    (restriction : ∀ x ∈ P0, ∀ y ∈ P0, ZFSet.pair x y ∈ rD ↔ ZFSet.pair x y ∈ r0)
    {x y : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair x y ∈ d.batchOrder ↔ ZFSet.pair x y ∈ r0 :=
  (d.old_order_iff (original hx) (original hy)).trans (restriction x hx y hy)

theorem original_meet_iff (original : P0 ⊆ D)
    (restriction : ∀ x ∈ P0, ∀ y ∈ P0, ∀ z,
      ZFSet.pair (ZFSet.pair x y) z ∈ μD ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ0)
    {x y z : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair (ZFSet.pair x y) z ∈ d.batchMeetGraph ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ μ0 :=
  (d.old_meet_iff (original hx) (original hy)).trans (restriction x hx y hy z)

end AttachmentBatchInputs

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u





def AssignmentQueryWithin (X T q : ZFSet.{u}) : Prop :=
  ∃ row L, q = ZFSet.pair row L ∧ L ⊆ stageOneAssignments X T

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def AssignmentIndexAgreement (A B : ZFSet.{u}) : Prop :=
  ∀ t, (∃ u w, stageOneAssignment t u w ∈ A) →
    (∃ u w, stageOneAssignment t u w ∈ B) →
    ∀ u w, stageOneAssignment t u w ∈ A ↔ stageOneAssignment t u w ∈ B

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_AssignmentQueryFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def assignmentQueryOverlapFormula {n} (z I L f : Fin n) : BoundedFormula n :=
  exMem I (exMem L.succ (.conj (pairMembershipFormula z.succ.succ 1 f.succ.succ)
    (pairMembershipFormula 0 1 f.succ.succ)))

def assignmentQueryMatchFormula {n} (I L A f : Fin n) : BoundedFormula n :=
  .conj (.allMem L (.conj (.mem 0 A.succ)
    (assignmentQueryOverlapFormula 0 I.succ L.succ f.succ)))
    (.allMem A (.imp (assignmentQueryOverlapFormula 0 I.succ L.succ f.succ) (.mem 0 L.succ)))

def assignmentQueryRelationFormula {n} (z I f : Fin n) : BoundedFormula n :=
  exPairFields z (exPairFields 1 (exPairFields 2
    (.conj (.equal 3 1) (assignmentQueryMatchFormula I.succ.succ.succ.succ.succ.succ
      2 0 f.succ.succ.succ.succ.succ.succ))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedChronologyCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def oldMeetFormula {n} (L T r μ birth : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem L (.allMem L.succ (.allMem L.succ.succ
    (.allMem T.succ.succ.succ (.allMem T.succ.succ.succ.succ
      (.allMem T.succ.succ.succ.succ.succ (imp
        (.conj (pairMembershipFormula 4 2 (lift birth))
          (.conj (pairMembershipFormula 5 1 (lift birth))
            (.conj (.mem 2 1) (.conj (.neg (pairMembershipFormula 5 4 (lift r)))
              (.conj (tripleMembershipFormula 5 4 3 (lift μ))
                (pairMembershipFormula 3 0 (lift birth)))))))
        (.mem 0 1)))))))

def birthBoundFormula {n} (L T birth s : Fin n) : BoundedFormula n :=
  .allMem L (.allMem T.succ (imp (pairMembershipFormula 1 0 birth.succ.succ)
    (disj (.equal 0 s.succ.succ) (.mem 0 s.succ.succ))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedMeetOrderCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def meetOrderFormula {n} (P r μ : Fin n) : BoundedFormula n :=
  .conj (partialOrderFormula P r) (.conj (binaryFunctionFormula P μ)
    (.allMem P (.allMem P.succ (.allMem P.succ.succ
      (imp (tripleMembershipFormula 2 1 0 μ.succ.succ.succ)
        (.conj (pairMembershipFormula 0 2 r.succ.succ.succ)
          (.conj (pairMembershipFormula 0 1 r.succ.succ.succ)
            (.allMem P.succ.succ.succ (imp
              (.conj (pairMembershipFormula 0 3 r.succ.succ.succ.succ)
                (pairMembershipFormula 0 2 r.succ.succ.succ.succ))
              (pairMembershipFormula 0 1 r.succ.succ.succ.succ))))))))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ForcingHistoryOutputFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

def stageOneAssignmentsMemberFormula {n : Nat} (z I T : Fin n) : BoundedFormula n :=
  exMem I (exMem T.succ (exMem T.succ.succ
    (stageOneAssignmentFormula z.succ.succ.succ 2 1 0)))

def stageOneAssignmentsSubsetFormula {n : Nat} (A I T : Fin n) : BoundedFormula n :=
  .allMem A (stageOneAssignmentsMemberFormula 0 I.succ T.succ)

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GreedyAntichainStepFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def antichainBlockedFormula {n} (q Q order D alpha prior : Fin n) : BoundedFormula n :=
  exMem alpha (exMem D.succ (.conj (pairMembershipFormula 1 0 prior.succ.succ)
    (exMem Q.succ.succ (.conj (pairMembershipFormula 0 q.succ.succ.succ order.succ.succ.succ)
      (pairMembershipFormula 0 1 order.succ.succ.succ)))))

def antichainEligibleFormula {n} (E Q order D alpha prior : Fin n) : BoundedFormula n :=
  .conj (.allMem E (.mem 0 D.succ)) (.allMem D
    (.conj (imp (.mem 0 E.succ)
      (.neg (antichainBlockedFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ)))
      (imp (.neg (antichainBlockedFormula 0 Q.succ order.succ D.succ alpha.succ prior.succ))
        (.mem 0 E.succ))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundDepthSlotCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def depthSlotEntryFormula : BoundedFormula 5 :=
  exMem 1 (exMem 3 (exMem 3 (exMem 4
    (.conj (orderedTripleFormula 4 3 2 1)
      (.conj (tripleMembershipFormula 6 3 0 7) (tripleMembershipFormula 0 2 1 8))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleFulfillmentAtBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def actionAgreementBelowFormula {n} (P r A g h w : Fin n) : BoundedFormula n :=
  .allMem P (.allMem P.succ (imp (pairMembershipFormula 1 w.succ.succ r.succ.succ)
    (.conj (imp (tripleMembershipFormula g.succ.succ 1 0 A.succ.succ)
      (tripleMembershipFormula h.succ.succ 1 0 A.succ.succ))
      (imp (tripleMembershipFormula h.succ.succ 1 0 A.succ.succ)
        (tripleMembershipFormula g.succ.succ 1 0 A.succ.succ)))))

end BoundedFormula





namespace BoundedFormula

def compressionActorFormula {n}
    (P G Q H R B e a Sources Reps top Caps i k : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ
  .conj
    (.allMem P (.allMem G.succ (.allMem H.succ.succ (.allMem Q.succ.succ.succ
      (imp (pairMembershipFormula (lift i) 3 (lift Sources))
        (imp (pairMembershipFormula (lift i) 2 (lift Reps))
          (imp (pairMembershipFormula 2 1 (lift a))
            (imp (pairMembershipFormula 3 0 (lift e))
              (actionAgreementBelowFormula (lift Q) (lift R) (lift B) (lift k) 1 0)))))))))
    (.allMem Q (.allMem Q.succ
      (imp (pairMembershipFormula top.succ.succ 1 e.succ.succ)
        (.conj
          (imp (tripleMembershipFormula k.succ.succ 1 0 B.succ.succ)
            (pairMembershipFormula i.succ.succ 0 Caps.succ.succ))
          (imp (pairMembershipFormula i.succ.succ 0 Caps.succ.succ)
            (tripleMembershipFormula k.succ.succ 1 0 B.succ.succ))))))

def compressionActorFulfillmentFormula {n}
    (I P G Q H R B e a Sources Reps top Caps : Fin n) : BoundedFormula n :=
  .allMem I (.exMem H.succ
    (compressionActorFormula P.succ.succ G.succ.succ Q.succ.succ H.succ.succ
      R.succ.succ B.succ.succ e.succ.succ a.succ.succ Sources.succ.succ
      Reps.succ.succ top.succ.succ Caps.succ.succ 1 0))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundExternalRequestSetRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

namespace BoundedFormula
open SetFormula

def compressionOverlapFormula {n} (Maps F zero first q i x j y : Fin n) : BoundedFormula n :=
  .conj (.equal i zero) (.conj (.equal j first)
    (exMem F (.conj (pairMembershipFormula q.succ 0 Maps.succ)
      (pairMembershipFormula y.succ x.succ 0))))

end BoundedFormula

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundTaggedComponentGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def taggedComponentGraph (P I B N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ ZFSet.prod {P} N, ∃ i ∈ I, ∃ n ∈ N, ∃ q ∈ B,
    z = ZFSet.pair x i ∧ x = ZFSet.pair P n ∧ n = ZFSet.pair i q)
    (ZFSet.prod (ZFSet.prod {P} N) I)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_StrictLexHeightFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def strictLexHeightFormula {n} (P C D r height rD : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .conj (functionToProductFormula P C D height)
    (.allMem P (.allMem P.succ (.allMem C.succ.succ (.allMem D.succ.succ.succ
      (.allMem C.succ.succ.succ.succ (.allMem D.succ.succ.succ.succ.succ
        (imp (.conj (pairMembershipFormula 5 4 (lift r))
          (.conj (.neg (.equal 5 4))
            (.conj (rightTripleMembershipFormula 5 3 2 (lift height))
              (rightTripleMembershipFormula 4 1 0 (lift height)))))
          (disj (.mem 3 1) (.conj (.equal 3 1) (pairMembershipFormula 2 0 (lift rD)))))))))))

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def chronologyPointFormula {n} (T C D rD s L r μ birth height : Fin n) : BoundedFormula n :=
  .conj (meetOrderFormula L r μ) (.conj (functionFormula L T birth)
    (.conj (birthBoundFormula L T birth s) (.conj (oldMeetFormula L T r μ birth)
      (strictLexHeightFormula L C D r height rD))))

end BoundedFormula





namespace BoundedFormula

def chronologyFunctionsFormula {n} (T V : Fin n) (graphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (functionFormula T V (graphs 0)) (.conj (functionFormula T V (graphs 1))
    (.conj (functionFormula T V (graphs 2)) (.conj (functionFormula T V (graphs 3))
      (functionFormula T V (graphs 4)))))

def chronologyPointsFormula {n} (T V C D rD : Fin n) (graphs : Fin 5 → Fin n) :
    BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem T (.allMem V.succ (.allMem V.succ.succ
    (.allMem V.succ.succ.succ (.allMem V.succ.succ.succ.succ
      (.allMem V.succ.succ.succ.succ.succ (imp
        (.conj (pairMembershipFormula 5 4 (lift (graphs 0)))
          (.conj (pairMembershipFormula 5 3 (lift (graphs 1)))
            (.conj (pairMembershipFormula 5 2 (lift (graphs 2)))
              (.conj (pairMembershipFormula 5 1 (lift (graphs 3)))
                (pairMembershipFormula 5 0 (lift (graphs 4)))))))
        (chronologyPointFormula (lift T) (lift C) (lift D) (lift rD) 5 4 3 2 1 0)))))))

def chronologyCoreFormula {n} (T V C D rD : Fin n) (graphs : Fin 5 → Fin n) :
    BoundedFormula n :=
  .conj (chronologyFunctionsFormula T V graphs) (chronologyPointsFormula T V C D rD graphs)

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SerializedChronologyFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula
def chronologyLayerLookupFormula {n} (T : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) : BoundedFormula n :=
  .conj (.mem s T) (.conj (.mem t T) (.conj (disj (.equal t s) (.mem t s))
    (.conj (pairMembershipFormula s L (graphs 0)) (.conj (pairMembershipFormula s r (graphs 1))
      (.conj (pairMembershipFormula s μ (graphs 2)) (.conj (pairMembershipFormula s birth (graphs 3))
        (tripleMembershipFormula s t z layers)))))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundBatchBirths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace AttachmentBatchInputs
universe u
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

noncomputable abbrev batchBirth (_d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss) (birth stamp : ZFSet.{u}) : ZFSet.{u} :=
  taggedBirth P (indexedAttachmentFresh I Qs rs As) birth stamp

theorem batchBirth_fresh_cases {birth stamp x : ZFSet.{u}}
    (earlier : ∀ y t, ZFSet.pair y t ∈ birth → t ∈ stamp)
    (entry : ZFSet.pair x stamp ∈ d.batchBirth birth stamp) :
    ∃ q : d.templates.Fresh, d.coding.encode (.inr q) = x := by
  have fresh := (taggedBirth_stamp_iff earlier).1 entry
  obtain ⟨p, hp, q, hq, equal⟩ := ZFSet.mem_prod.1 fresh
  obtain rfl := ZFSet.mem_singleton.1 hp
  obtain ⟨q', rfl⟩ := d.freshCode_surjective q hq
  exact ⟨q', equal.symm⟩

theorem batchBirth_different_components_bridge {T birth stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (q t : d.templates.Fresh) (different : q.1 ≠ t.1) :
    OldBridgeCode d.batchCarrier d.batchOrder d.batchMeetGraph (d.batchBirth birth stamp) stamp
      (d.coding.encode (.inr q)) (d.coding.encode (.inr t)) := by
  classical
  by_cases qt : ZFSet.pair (d.coding.encode (.inr q)) (d.coding.encode (.inr t)) ∈ d.batchOrder
  · let z := d.templates.shadow t
    obtain ⟨a, entry, _⟩ := born.2 z.val z.property
    exact Or.inr ⟨z.val, old_mem_taggedExtension z.property, a, taggedBirth_subset _ _ _ _ entry,
      earlier z.val a entry, Or.inl
        ⟨(d.coding.old_upper_iff q z).2 ((d.coding.cross_lower_iff q t different).1 qt),
          (d.coding.old_lower_iff z t).2 (d.oldOrder.order.refl z.val z.property)⟩⟩
  · by_cases tq : ZFSet.pair (d.coding.encode (.inr t)) (d.coding.encode (.inr q)) ∈ d.batchOrder
    · let z := d.templates.shadow q
      obtain ⟨a, entry, _⟩ := born.2 z.val z.property
      exact Or.inr ⟨z.val, old_mem_taggedExtension z.property, a, taggedBirth_subset _ _ _ _ entry,
        earlier z.val a entry, Or.inr
          ⟨(d.coding.old_upper_iff t z).2 ((d.coding.cross_lower_iff t q different.symm).1 tq),
            (d.coding.old_lower_iff z q).2 (d.oldOrder.order.refl z.val z.property)⟩⟩
    · let z := d.oldOrder.toMeetOrder.meet (d.templates.shadow q) (d.templates.shadow t)
      obtain ⟨a, entry, _⟩ := born.2 z.val z.property
      exact Or.inl ⟨z.val, a, d.coding.encoded_cross_meet q t different qt tq,
        taggedBirth_subset _ _ _ _ entry, earlier z.val a entry⟩

end AttachmentBatchInputs

open SetRealization SetFormula
universe u

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

noncomputable def batchBirth_incoming_layer
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {T birth stamp : ZFSet.{u}}
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)
    (born : ZFSet.IsFunc P T birth)
    (old : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (index : SetMembers I → ZFSet.{u}) (earlier : ∀ i, index i ∈ stamp)
    (spaces : ∀ i, Space (index i) = d.space ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)
    (orders : ∀ i, sourceOrder (index i) = d.rel ⟨SetMembers.raw i, SetMembers.raw_mem i⟩)
    (meets : ∀ i, sourceMeet (index i) = d.meet ⟨SetMembers.raw i, SetMembers.raw_mem i⟩) :
    CodedGrowthLayer M Space sourceOrder sourceMeet d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.batchBirth birth stamp) stamp := by
  classical
  let fresh (x : {x : ZFSet.{u} // x ∈ d.batchCarrier ∧
      ZFSet.pair x stamp ∈ d.batchBirth birth stamp}) : d.templates.Fresh :=
    (d.batchBirth_fresh_cases old x.property.2).choose
  have freshEq (x : {x : ZFSet.{u} // x ∈ d.batchCarrier ∧
      ZFSet.pair x stamp ∈ d.batchBirth birth stamp}) : d.coding.encode (.inr (fresh x)) = x.val :=
    (d.batchBirth_fresh_cases old x.property.2).choose_spec
  let component (x : {x : ZFSet.{u} // x ∈ d.batchCarrier ∧
      ZFSet.pair x stamp ∈ d.batchBirth birth stamp}) : SetMembers I :=
    SetMembers.ofMem (fresh x).1.val (fresh x).1.property
  refine .separated (SetMembers I) index
    (fun i => batchTemplateGraph I P Qs rs As Es (SetMembers.raw i)) earlier
    (fun i => M.batchTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs
      (M.transitive hI (SetMembers.raw_mem i))) ?_ component ?_ ?_
  · intro i
    simpa only [spaces i, orders i, meets i] using
      d.batch_template_embedding_code ⟨SetMembers.raw i, SetMembers.raw_mem i⟩
  · intro x
    let q := fresh x
    have sameIndex : (⟨SetMembers.raw (component x), SetMembers.raw_mem (component x)⟩ :
        {i : ZFSet.{u} // i ∈ I}) = q.1 := by
      apply Subtype.ext
      exact SetMembers.raw_ofMem q.1.val q.1.property
    have rawSame : SetMembers.raw (component x) = q.1.val := congrArg Subtype.val sameIndex
    have point : q.2.val.val ∈ Space (index (component x)) := by
      rw [spaces, sameIndex]
      exact q.2.val.property
    apply (mem_relationImage _ _ _ x.val).2
    refine ⟨x.property.1, q.2.val.val, point, ?_⟩
    rw [rawSame, ← freshEq x]
    apply (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
    apply (d.batch_template_entry_iff q.1 _ _).2
    exact Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨q.2.val.property, q.2.property⟩, rfl⟩
  · intro x y different
    have separate : (fresh x).1 ≠ (fresh y).1 := by
      intro equal
      apply different
      exact congrArg (fun i : {i : ZFSet.{u} // i ∈ I} => SetMembers.ofMem i.val i.property) equal
    have bridge := d.batchBirth_different_components_bridge born old (fresh x) (fresh y) separate
    rw [freshEq x, freshEq y] at bridge
    exact bridge

end AttachmentBatchInputs

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RootedSupportOwners
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

open Attachment
universe u
variable {V : Type u} (d : Scheme V)

def Supports (v : V) (x : d.Node) : Prop := ∃ a, (d.vertex v).toFun a = x

def LeastSupport (v : V) (x : d.Node) : Prop :=
  d.Supports v x ∧ ∀ w, d.Supports w x → d.depth v ≤ d.depth w

theorem fresh_stage_vertex (n : Nat) (x : (d.stages n).batch.Fresh)
    (w : V) (hw : d.depth w ≤ n + 1) (a : d.Space w)
    (eq : ((d.stages (n + 1)).vertex w hw).toFun a = Sum.inr x) :
    w = x.1.val := by
  classical
  let s := d.stages n
  change (s.successor.vertex w hw).toFun a = Sum.inr x at eq
  by_cases old : d.depth w ≤ n
  · rw [s.successor_old w old a] at eq
    exact False.elim (Sum.inl_ne_inr eq)
  · let i : s.Layer := ⟨w, by omega⟩
    rw [s.successor_new i a] at eq
    change s.batch.componentMap i ((s.batch.glue i).represent a) = Sum.inr x at eq
    by_cases base : (d.order w).le a (d.childAnchor w (s.layer_nonzero i))
    · rw [(s.batch.glue i).represent_old a base] at eq
      exact False.elim (Sum.inl_ne_inr eq)
    · rw [(s.batch.glue i).represent_new a base] at eq
      exact congrArg (fun z : s.batch.Fresh => z.1.val) (Sum.inr.inj eq)

theorem fresh_vertex_eq (v : V) (h : d.depth v ≠ 0) (a : d.Space v)
    (fresh : ¬ (d.order v).le a (d.childAnchor v h))
    (w : V) (hw : d.depth w ≤ d.depth v) (b : d.Space w)
    (eq : (d.vertex w).toFun b = (d.vertex v).toFun a) : w = v := by
  let n := d.depth (d.parent v)
  let s := d.stages n
  let i : s.Layer := ⟨v, (d.parent_depth v h).symm⟩
  let x : s.batch.Fresh := ⟨i, ⟨a, fresh⟩⟩
  have hv : (d.vertex v).toFun a = d.chain.point (n + 1) (Sum.inr x) := by
    rw [d.vertex_at v (n + 1) i.property.le a]
    change d.chain.point (n + 1) ((s.successor.vertex v i.property.le).toFun a) = _
    rw [s.successor_new i a]
    change d.chain.point (n + 1) (s.batch.componentMap i ((s.batch.glue i).represent a)) = _
    rw [(s.batch.glue i).represent_new a fresh]
    rfl
  have hw' : d.depth w ≤ n + 1 := hw.trans i.property.le
  have stageEq : ((d.stages (n + 1)).vertex w hw').toFun b = Sum.inr x := by
    apply d.chain.include_injective (n + 1)
    rw [← d.vertex_at w (n + 1) hw' b]
    exact eq.trans hv
  exact d.fresh_stage_vertex n x w hw' b stageEq

theorem supports_parent_iff (v : V) (h : d.depth v ≠ 0) (a : d.Space v) :
    d.Supports (d.parent v) ((d.vertex v).toFun a) ↔
      (d.order v).le a (d.childAnchor v h) := by
  constructor
  · rintro ⟨b, eq⟩
    by_contra fresh
    have smaller := d.parent_depth v h
    have same := d.fresh_vertex_eq v h a fresh (d.parent v) (by omega) b eq
    rw [same] at smaller
    omega
  · intro base
    exact ⟨((d.link v h).toFun ⟨a, base⟩).val,
      (d.parent_identification v h ⟨a, base⟩).symm⟩

theorem leastSupport_vertex_iff (v : V) (h : d.depth v ≠ 0) (a : d.Space v) :
    d.LeastSupport v ((d.vertex v).toFun a) ↔
      ¬ (d.order v).le a (d.childAnchor v h) := by
  constructor
  · intro least base
    have parent := least.2 (d.parent v) ((d.supports_parent_iff v h a).mpr base)
    have smaller := d.parent_depth v h
    omega
  · intro fresh
    refine ⟨⟨a, rfl⟩, ?_⟩
    rintro w ⟨b, eq⟩
    by_contra notle
    have same := d.fresh_vertex_eq v h a fresh w (by omega) b eq
    subst w
    exact notle (Nat.le_refl _)

theorem leastSupport_root_iff (x : d.Node) :
    d.LeastSupport d.root x ↔ d.Supports d.root x := by
  exact ⟨And.left, fun hx => ⟨hx, fun _ _ => by rw [d.depth_root]; exact Nat.zero_le _⟩⟩

theorem leastSupport_unique {v w : V} {x : d.Node}
    (first : d.LeastSupport v x) (second : d.LeastSupport w x) : v = w := by
  have sameDepth := Nat.le_antisymm (first.2 w second.1) (second.2 v first.1)
  by_cases zero : d.depth v = 0
  · exact (d.zero_eq_root v zero).trans (d.zero_eq_root w (sameDepth.symm.trans zero)).symm
  · rcases first.1 with ⟨a, rfl⟩
    rcases second.1 with ⟨b, eq⟩
    exact (d.fresh_vertex_eq v zero a ((d.leastSupport_vertex_iff v zero a).mp first)
      w sameDepth.symm.le b eq).symm

theorem existsUnique_leastSupport (x : d.Node) : ∃! v, d.LeastSupport v x := by
  classical
  have present : ∃ n, ∃ v, d.depth v = n ∧ d.Supports v x := by
    rcases d.cover x with ⟨v, a, eq⟩
    exact ⟨d.depth v, v, rfl, a, eq⟩
  rcases Nat.find_spec present with ⟨v, hv, support⟩
  have least : d.LeastSupport v x := by
    refine ⟨support, ?_⟩
    intro w hw
    rw [hv]
    exact Nat.find_min' present ⟨w, rfl, hw⟩
  exact ⟨v, least, fun w hw => d.leastSupport_unique hw least⟩

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RootedSupportOrder
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

universe u
variable {V : Type u} (d : Scheme V)

theorem supports_lower {v : V} {x y : d.Node}
    (supported : d.Supports v y) (lower : d.gluedOrder.le x y) : d.Supports v x := by
  rcases supported with ⟨b, rfl⟩
  exact (d.vertex v).ideal b x lower

theorem leastSupport_depth_mono {v w : V} {x y : d.Node}
    (first : d.LeastSupport v x) (second : d.LeastSupport w y)
    (lower : d.gluedOrder.le x y) : d.depth v ≤ d.depth w :=
  first.2 w (d.supports_lower second.1 lower)

theorem leastSupport_eq_of_depth_eq {v w : V} {x y : d.Node}
    (first : d.LeastSupport v x) (second : d.LeastSupport w y)
    (lower : d.gluedOrder.le x y) (same : d.depth v = d.depth w) : v = w := by
  apply d.leastSupport_unique first
  refine ⟨d.supports_lower second.1 lower, ?_⟩
  intro z hz
  rw [← same]
  exact first.2 z hz

end PartitionPilot.Compression.RecursiveMaps.RootedGluing.Scheme

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RequestedSupportOwners
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem leastSupport_root_copy_iff (x : f.Node a) :
    (f.diagram a).scheme.LeastSupport (TileStars.root J f.Letters R) x ↔
      ∃ y, (f.copy a 1).toFun y = x := by
  refine ((f.diagram a).scheme.leastSupport_root_iff x).trans ?_
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (f.copy_one a y).trans hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (f.copy_one a y).symm.trans hy⟩

theorem leastSupport_coset_iff (c : CosetGeometry.Vertex J f.Letters) (x : f.Node a) :
    (f.diagram a).scheme.LeastSupport (.inl c) x ↔
      c = CosetGeometry.root J f.Letters ∧ ∃ y, (f.copy a 1).toFun y = x := by
  constructor
  · intro least
    by_cases zero : (f.diagram a).scheme.depth (.inl c) = 0
    · have root := (f.diagram a).scheme.zero_eq_root (.inl c) zero
      have hc : c = CosetGeometry.root J f.Letters := Sum.inl.inj root
      subst c
      exact ⟨rfl, (f.leastSupport_root_copy_iff a x).mp least⟩
    · rcases least.1 with ⟨y, rfl⟩
      exact False.elim (((f.diagram a).scheme.leastSupport_vertex_iff (.inl c) zero y).mp least
        (f.old_local_full a c zero y))
  · rintro ⟨rfl, old⟩
    exact (f.leastSupport_root_copy_iff a x).mpr old

theorem tile_depth_ne_zero (w : External J f.Letters) (r : R) :
    (f.diagram a).scheme.depth (.inr (w, r)) ≠ 0 := by
  intro zero
  exact Sum.inr_ne_inl ((f.diagram a).scheme.zero_eq_root (.inr (w, r)) zero)

theorem leastSupport_tile_iff (w : External J f.Letters) (r : R)
    (y : (f.tile r).Space) :
    (f.diagram a).scheme.LeastSupport (.inr (w, r)) ((f.placedTile a w r).toFun y) ↔
      ¬ (f.tile r).order.le y
        ((f.diagram a).localGlue (.inr (w, r)) (f.tile_depth_ne_zero a w r)).rightAnchor :=
  (f.diagram a).scheme.leastSupport_vertex_iff (.inr (w, r)) (f.tile_depth_ne_zero a w r) y

theorem leastSupport_cases (v : TileStars.Vertex J f.Letters R) (x : f.Node a)
    (least : (f.diagram a).scheme.LeastSupport v x) :
    (v = TileStars.root J f.Letters R ∧ ∃ y, (f.copy a 1).toFun y = x) ∨
      ∃ w r, ∃ y : (f.tile r).Space, v = .inr (w, r) ∧
        (f.placedTile a w r).toFun y = x ∧
        ¬ (f.tile r).order.le y
          ((f.diagram a).localGlue (.inr (w, r)) (f.tile_depth_ne_zero a w r)).rightAnchor := by
  cases v with
  | inl c =>
    rcases (f.leastSupport_coset_iff a c x).mp least with ⟨rfl, old⟩
    exact Or.inl ⟨rfl, old⟩
  | inr c =>
    rcases least.1 with ⟨y, rfl⟩
    exact Or.inr ⟨c.1, c.2, y, rfl, rfl, (f.leastSupport_tile_iff a c.1 c.2 y).mp least⟩

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RequestedOwnerSlotLaws
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.TileRequests
open Attachment CosetGeometry
universe u
variable {A : Type u} {P : MeetOrder A}

namespace Request

def vertexSlot : (r : Request P) → Option r.Child → Nat
  | _, none => 0
  | .separation _, some _ => 1
  | .compression _ _, some _ => 1
  | .rectangle _, some j => if j.down then 2 else 1

theorem vertexSlot_injective (r : Request P) : Function.Injective r.vertexSlot := by
  cases r with
  | separation W =>
    intro i j equal
    cases i <;> cases j <;> simp_all [vertexSlot, Child]
    exact congrArg some (Subsingleton.elim _ _)
  | compression K copy =>
    intro i j equal
    cases i <;> cases j <;> simp_all [vertexSlot, Child]
    exact congrArg some (Subsingleton.elim _ _)
  | rectangle rect =>
    intro i j equal
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => cases j with | up b => cases b <;> simp_all [vertexSlot]
    | some i =>
      cases j with
      | none => cases i with | up b => cases b <;> simp_all [vertexSlot]
      | some j =>
        cases i with | up b =>
          cases j with | up c =>
            cases b <;> cases c <;> simp_all [vertexSlot]

end Request

end PartitionPilot.Compression.RecursiveMaps.TileRequests



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchHeightGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def componentHeightEntryFormula {n}
    (w I Qs B Hs Cs E C D boundQs boundHs boundE : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) : Fin (n + 8) := i.succ.succ.succ.succ.succ.succ.succ.succ
  let body : BoundedFormula (n + 8) :=
    .conj (pairOfPairsFormula (lift w) 7 3 1 0)
      (.conj (pairMembershipFormula 7 6 (lift Qs))
        (.conj (pairMembershipFormula 7 5 (lift Hs))
          (.conj (pairMembershipFormula 7 4 (lift E))
            (.conj (pairMembershipFormula 7 1 (lift Cs))
              (.conj (pairMembershipFormula 3 2 5) (pairMembershipFormula 2 0 4))))))
  exMem I (exMem boundQs.succ (exMem boundHs.succ.succ
    (exMem boundE.succ.succ.succ (exMem 2
      (exMem B.succ.succ.succ.succ.succ
        (exMem C.succ.succ.succ.succ.succ.succ
          (exMem D.succ.succ.succ.succ.succ.succ.succ body)))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionHeightSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u






namespace BatchHeightEndpointCode

variable {P rP μP I Qs rs μs As Es Fs Ss C D old rD Cs los his : ZFSet.{u}}
  {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
  (e : BatchHeightEndpointCode d C D old rD Cs los his)

noncomputable abbrev low (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} :=
  (show FunctionGraphOn I los from ⟨D, e.lows⟩).value i
noncomputable abbrev high (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.{u} :=
  (show FunctionGraphOn I his from ⟨D, e.highs⟩).value i

theorem low_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (e.low i) ∈ los :=
  (show FunctionGraphOn I los from ⟨D, e.lows⟩).value_entry i
theorem high_entry (i : {i : ZFSet.{u} // i ∈ I}) : ZFSet.pair i.val (e.high i) ∈ his :=
  (show FunctionGraphOn I his from ⟨D, e.highs⟩).value_entry i

end BatchHeightEndpointCode

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionBirths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def birthRestrictionFamilyEntryFormula {k} (z omega domainsBound relations t domains birth : Fin k) :
    BoundedFormula k :=
  exMem omega (exMem domainsBound.succ (exMem relations.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 0)
      (.conj (pairMembershipFormula 2 1 domains.succ.succ.succ)
        (graphRestrictionFormula 0 1 t.succ.succ.succ birth.succ.succ.succ)))))

end BoundedFormula

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalChronologyStageLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def chronologyRestrictionMemberFormula (kind : Fin 3) {n} (z P R : Fin n) : BoundedFormula n :=
  Fin.cases (productElementFormula z P R) (Fin.cases (productElementFormula z P P)
    (fun _ => exMem R (exMem R.succ (.conj (orderedPairFormula z.succ.succ 1 0)
      (productElementFormula 1 P.succ.succ P.succ.succ))))) kind

def chronologyRestrictionFormula (kind : Fin 3) {n} (q P R f : Fin n) : BoundedFormula n :=
  .conj (.allMem q (.conj (.mem 0 f.succ) (chronologyRestrictionMemberFormula kind 0 P.succ R.succ)))
    (.allMem f (imp (chronologyRestrictionMemberFormula kind 0 P.succ R.succ) (.mem 0 q.succ)))

def chronologyRestrictionFamilyFormula (kind : Fin 3) {n}
    (z I Ps Q R W f : Fin n) : BoundedFormula n :=
  exMem I (exMem Q.succ (exMem W.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 0)
      (.conj (pairMembershipFormula 2 1 Ps.succ.succ.succ)
        (chronologyRestrictionFormula kind 0 1 R.succ.succ.succ f.succ.succ.succ)))))

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainTransitionValidityCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def transitionOrderFormula {n} (P Q rP rQ points : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  .allMem P (.allMem P.succ (.allMem Q.succ.succ (.allMem Q.succ.succ.succ
    (imp (.conj (pairMembershipFormula 3 1 (lift points)) (pairMembershipFormula 2 0 (lift points)))
      (.conj (imp (pairMembershipFormula 1 0 (lift rQ)) (pairMembershipFormula 3 2 (lift rP)))
        (imp (pairMembershipFormula 3 2 (lift rP)) (pairMembershipFormula 1 0 (lift rQ))))))))

def transitionEquivarianceFormula {n} (P Q G H AP AQ points actors : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem G (.allMem H.succ (.allMem P.succ.succ (.allMem P.succ.succ.succ
    (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 5 4 (lift actors))
        (.conj (pairMembershipFormula 3 1 (lift points))
          (.conj (pairMembershipFormula 2 0 (lift points))
            (tripleMembershipFormula 5 3 2 (lift AP)))))
        (tripleMembershipFormula 4 1 0 (lift AQ))))))))

def transitionHeightFormula {n} (P Q heightP heightQ points : Fin n) : BoundedFormula n :=
  .allMem P (.allMem Q.succ (imp (pairMembershipFormula 1 0 points.succ.succ)
    (graphFiberEqualityFormula 0 1 heightQ.succ.succ heightP.succ.succ)))

def transitionAgreementFormula {n} (P Q rP rQ G H AP AQ points actors : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem G (.allMem G.succ (.allMem H.succ.succ (.allMem H.succ.succ.succ
    (.allMem P.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 5 3 (lift actors))
        (.conj (pairMembershipFormula 4 2 (lift actors))
          (.conj (pairMembershipFormula 1 0 (lift points))
            (actionAgreementBelowFormula (lift P) (lift rP) (lift AP) 5 4 1))))
        (actionAgreementBelowFormula (lift Q) (lift rQ) (lift AQ) 3 2 0)))))))

def mainTransitionLawsFormula {n}
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n) :
    BoundedFormula n :=
  .conj (meetEmbeddingFormula P Q rP rQ μP μQ points)
    (.conj (transitionOrderFormula P Q rP rQ points)
      (.conj (groupEmbeddingFormula G H mG mH oneG oneH actors)
        (.conj (transitionEquivarianceFormula P Q G H AP AQ points actors)
          (.conj (pairMembershipFormula bP bQ points)
            (.conj (transitionHeightFormula P Q heightP heightQ points)
              (transitionAgreementFormula P Q rP rQ G H AP AQ points actors))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTransitionValidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def validMainTransitionCodeFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n) :
    BoundedFormula n :=
  .conj (orderedPairFormula z points actors)
    (mainTransitionLawsFormula P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors)

end BoundedFormula
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace BoundedFormula

def graphCutoffEqualityFormula {n} (cutoff source target : Fin n) : BoundedFormula n :=
  .conj (graphFiberEqualityFormula cutoff cutoff source target)
    (.allMem cutoff (graphFiberEqualityFormula 0 0 source.succ target.succ))

def chronologyGraphPrefixFormula {n} (cutoff : Fin n) (source target : Fin 5 → Fin n) :
    BoundedFormula n :=
  .conj (graphCutoffEqualityFormula cutoff (source 0) (target 0))
    (.conj (graphCutoffEqualityFormula cutoff (source 1) (target 1))
      (.conj (graphCutoffEqualityFormula cutoff (source 2) (target 2))
        (.conj (graphCutoffEqualityFormula cutoff (source 3) (target 3))
          (graphCutoffEqualityFormula cutoff (source 4) (target 4)))))

def chronologicalTransitionExtraFormula {n}
    (P Q points sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (disj (.equal sourceCutoff targetCutoff) (.mem sourceCutoff targetCutoff))
    (.conj (transitionHeightFormula P Q sourceBirth targetBirth points)
      (chronologyGraphPrefixFormula sourceCutoff sourceGraphs targetGraphs))

def oldBirthFiberCoverageFormula {n} (P points birth cutoff : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ
  .allMem birth (.allMem 0 (.allMem 0 (.allMem 2 (.allMem 0
    (imp (.conj (orderedPairFormula 4 2 0)
      (disj (.equal 0 (lift cutoff)) (.mem 0 (lift cutoff))))
      (exMem (lift P) (pairMembershipFormula 0 3 (lift points).succ)))))))

end BoundedFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedTopStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

noncomputable def fixedTopAction (G P A : ZFSet.{u}) : ZFSet.{u} :=
  A ∪ ZFSet.sep (fun z => ∃ g ∈ G, z = ZFSet.pair (ZFSet.pair g P) P)
    (ZFSet.prod (ZFSet.prod G {P}) {P})

theorem pair_mem_fixedTopAction (G P A g p q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g p) q ∈ fixedTopAction G P A ↔
      ZFSet.pair (ZFSet.pair g p) q ∈ A ∨ (g ∈ G ∧ p = P ∧ q = P) := by
  constructor
  · intro member
    rcases ZFSet.mem_union.1 member with old | fresh
    · exact Or.inl old
    · obtain ⟨h, hh, equal⟩ := (ZFSet.mem_sep.1 fresh).2
      obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
      exact Or.inr ⟨hh, rfl, rfl⟩
  · rintro (old | ⟨hg, rfl, rfl⟩)
    · exact ZFSet.mem_union.2 (Or.inl old)
    · exact ZFSet.mem_union.2 (Or.inr (ZFSet.mem_sep.2
        ⟨ZFSet.pair_mem_prod.2
          ⟨ZFSet.pair_mem_prod.2 ⟨hg, ZFSet.mem_singleton.2 rfl⟩, ZFSet.mem_singleton.2 rfl⟩,
          g, hg, rfl⟩))

theorem fixedTopAction_old_iff {G P A g p q : ZFSet.{u}} (hp : p ∈ P) :
    ZFSet.pair (ZFSet.pair g p) q ∈ fixedTopAction G P A ↔
      ZFSet.pair (ZFSet.pair g p) q ∈ A := by
  rw [pair_mem_fixedTopAction]
  exact ⟨fun h => h.elim id (fun h => False.elim (ZFSet.mem_irrefl P (h.2.1 ▸ hp))), Or.inl⟩

namespace BoundedFormula

open SetFormula

def fixedTopActionEntryFormula {n} (z G P : Fin n) : BoundedFormula n :=
  exMem G (orderedTripleFormula z.succ 0 P.succ P.succ)

end BoundedFormula

end

section
universe u

namespace ActionAgreementBelow
variable {G P m one r A g h v : ZFSet.{u}}
variable (agree : ActionAgreementBelow P r A g h v)
include agree

theorem fixedTop (order : PartialOrderCode P r) (action : PosetActionCode G P m one r A)
    (hv : v ∈ P) :
    ActionAgreementBelow (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopAction G P A) g h v := by
  intro x _ y _ lower
  have hx := fixedTopOrder_no_new_below order hv lower
  rw [fixedTopAction_old_iff hx, fixedTopAction_old_iff hx]
  by_cases hy : y ∈ P
  · exact agree x hx y hy ((fixedTopOrder_old_iff hv).1 lower)
  · exact ⟨fun entry => False.elim (hy (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2),
      fun entry => False.elim (hy (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2)⟩

end ActionAgreementBelow

end

open SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundUnionSizeWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

namespace BoundedFormula

def belowWitnessEntryFormula {n} (z r k w : Fin n) : BoundedFormula n :=
  exMem r (exMem k.succ (exMem w.succ.succ
    (.conj (orderedRightTripleFormula z.succ.succ.succ 2 1 0) (injectionFormula 2 1 0))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalProfilePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace AttachmentBatchInputs
variable {P r μ J Qs rs μs As Es Fs Ss : ZFSet.{u}}

theorem batch_bottom (d : AttachmentBatchInputs P r μ J Qs rs μs As Es Fs Ss)
    {b : ZFSet.{u}} (hb : b ∈ P) (least : ∀ x ∈ P, ZFSet.pair b x ∈ r) :
    b ∈ d.batchCarrier ∧ ∀ x ∈ d.batchCarrier, ZFSet.pair b x ∈ d.batchOrder :=
  ⟨old_mem_taggedExtension hb, d.coding.least_preserved hb least⟩

end AttachmentBatchInputs

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageCandidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def bottomFormula {n} (P r b : Fin n) : BoundedFormula n :=
  .conj (.mem b P) (.allMem P (pairMembershipFormula b.succ 0 r.succ))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainTransitionRawCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def chronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors)
    (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff sourceBirth targetBirth
      sourceGraphs targetGraphs)

def coveredChronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (chronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs)
    (oldBirthFiberCoverageFormula P points targetBirth sourceCutoff)

end PartitionPilot.Forcing.BoundedFormula



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainLimitCoverageFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u





def exGraphFields {n} (f : Fin n) (body : BoundedFormula (n + 2)) : BoundedFormula n :=
  exMem f (exPairFields 0
    (reindex (Fin.cases 0 (Fin.cases 1 (fun i => i.succ.succ.succ))) body))





def certificateGraphEntryAt {n} (j F B f k : Fin n) : BoundedFormula n :=
  exGraphFields k (.conj (.equal 1 j.succ.succ)
    (exPairFields 0 (.conj (.equal 1 F.succ.succ.succ.succ)
      (orderedPairFormula 0 B.succ.succ.succ.succ f.succ.succ.succ.succ))))





def assignmentQueryWithinFormula {n} (X T q : Fin n) : BoundedFormula n :=
  exPairFields q (stageOneAssignmentsSubsetFormula 0 X.succ.succ T.succ.succ)

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PreparedCertificateCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def synchronizedEnumerationFormula {n} (omega N B f e names : Fin n) : BoundedFormula n :=
  .conj (functionFormula B N f)
    (.conj (functionFormula omega B e)
      (.conj (functionFormula omega N names)
        (.conj (.allMem B (exMem omega.succ (pairMembershipFormula 0 1 e.succ.succ)))
          (.conj
            (.allMem omega (.allMem B.succ (.allMem N.succ.succ
              (imp (pairMembershipFormula 2 1 e.succ.succ.succ)
                (imp (pairMembershipFormula 2 0 names.succ.succ.succ)
                  (pairMembershipFormula 1 0 f.succ.succ.succ))))))
            (.allMem omega (.allMem B.succ (.allMem N.succ.succ
              (imp (pairMembershipFormula 2 1 e.succ.succ.succ)
                (imp (pairMembershipFormula 1 0 f.succ.succ.succ)
                  (pairMembershipFormula 2 0 names.succ.succ.succ))))))))))

def certificateEnumerationEntryFormula {n} (entry J E Names omega N k : Fin n) :
    BoundedFormula n :=
  exPairFields entry (exPairFields 0
    (exGraphFields k.succ.succ.succ.succ (exPairFields 0 (exPairFields 0
      (.conj (.equal 5 9)
        (.conj (.mem 9 J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
          (.conj (.mem 7 E.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
            (.conj (.mem 6 Names.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)
              (synchronizedEnumerationFormula
                omega.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
                N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 0 7 6)))))))))

end BoundedFormula

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskCapFamilyCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def codedInsertionProfileFormula {n} (L r μ c E K F : Fin n) : BoundedFormula n :=
  .allMem L (imp (pairMembershipFormula E.succ 0 r.succ)
    (.conj
      (imp (.exMem F.succ (pairMembershipFormula 0 1 r.succ.succ))
        (pairMembershipFormula K.succ 0 r.succ))
      (imp (.neg (.exMem F.succ (pairMembershipFormula 0 1 r.succ.succ)))
        (tripleMembershipFormula K.succ 0 c.succ μ.succ))))

def codedCapProfileFormula {n} (L r μ c E K F : Fin n) : BoundedFormula n :=
  .conj (.mem c L) (.conj (.mem E L) (.conj (.mem K L)
    (.conj (subsetFormula F L) (.conj (.exMem F (.equal 0 0))
      (.conj (codedInsertionProfileFormula L r μ c E K F)
        (.conj (pairMembershipFormula c K r)
          (.conj (.neg (pairMembershipFormula K c r)) (.neg (pairMembershipFormula E K r)))))))))

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula

def commonTargetCapMeetFormula {n} (I P Q ν e Targets Caps : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ.succ.succ
  .allMem I (.allMem I.succ (.allMem P.succ.succ (.allMem Q.succ.succ.succ
    (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (imp (.neg (.equal 5 4))
        (imp (pairMembershipFormula 5 3 (lift Targets))
          (imp (pairMembershipFormula 4 3 (lift Targets))
            (imp (pairMembershipFormula 5 2 (lift Caps))
              (imp (pairMembershipFormula 4 1 (lift Caps))
                (imp (pairMembershipFormula 3 0 (lift e))
                  (tripleMembershipFormula 2 1 0 (lift ν)))))))))))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

def BirthLevelEnumerationCode (omega stages A levels e : ZFSet.{u}) : Prop :=
  (relationImage A stages levels = ∅ ∧ e = ∅) ∨
    (ZFSet.IsFunc omega stages e ∧ ∀ alpha ∈ stages,
      (∃ n ∈ omega, ZFSet.pair n alpha ∈ e) ↔
        ∃ x ∈ A, ZFSet.pair x alpha ∈ levels)

namespace BoundedFormula
open SetFormula

def birthLevelEnumerationFormula {n} (omega stages A levels e : Fin n) : BoundedFormula n :=
  disj (.conj (.allMem A (.allMem stages.succ
      (.neg (pairMembershipFormula 1 0 levels.succ.succ)))) (emptyFormula e))
    (.conj (functionFormula omega stages e)
      (.allMem stages (.conj
        (imp (exMem omega.succ (pairMembershipFormula 0 1 e.succ.succ))
          (exMem A.succ (pairMembershipFormula 0 1 levels.succ.succ)))
        (imp (exMem A.succ (pairMembershipFormula 0 1 levels.succ.succ))
          (exMem omega.succ (pairMembershipFormula 0 1 e.succ.succ))))))

def birthLevelEnumerationEntryFormula {n} (entry omega stages levels : Fin n) : BoundedFormula n :=
  exPairFields entry (exPairFields 1
    (birthLevelEnumerationFormula omega.succ.succ.succ.succ
      stages.succ.succ.succ.succ 0 levels.succ.succ.succ.succ 2))

end BoundedFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitGroupLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

def directLimitRelationEntryFormula : BoundedFormula 5 :=
  exMem 1 (exMem 3 (exMem 3 (exMem 5 (exMem 5 (exMem 7 (exMem 9 (exMem 10
    (.conj (pairOfPairsFormula 8 7 6 5 4)
      (.conj (tripleMembershipFormula 3 7 1 12)
        (.conj (tripleMembershipFormula 3 5 0 12)
          (.conj (pairMembershipFormula 6 2 1) (pairMembershipFormula 4 2 0))))))))))))

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyLayerRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def chronologyLayerPairLookupFormula {n} (p T Qs rs μs births : Fin n)
    (v : Fin 6 → Fin n) : BoundedFormula n :=
  .conj (.mem (v 0) T) (.conj (.mem (v 1) T)
    (.conj (disj (.equal (v 1) (v 0)) (.mem (v 1) (v 0)))
      (.conj (orderedPairFormula p (v 0) (v 1))
        (.conj (pairMembershipFormula (v 0) (v 2) Qs)
          (.conj (pairMembershipFormula (v 0) (v 3) rs)
            (.conj (pairMembershipFormula (v 0) (v 4) μs)
              (pairMembershipFormula (v 0) (v 5) births)))))))

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundConstantBatchLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def batchTemplateFamily (I P Qs rs As Es : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections I (familyPointBound Qs)
    (taggedExtension P (indexedAttachmentFresh I Qs rs As))
    (batchAttachmentTemplateGraph I P Qs rs As Es)

noncomputable def batchTemplateFamilyBound (I P Qs rs As : ZFSet.{u}) : ZFSet.{u} :=
  M.groundRelations (familyPointBound Qs)
    (taggedExtension P (indexedAttachmentFresh I Qs rs As))

end TransitiveGround

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

noncomputable abbrev batchIncomingFiber (_d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss) := ZFSet.prod {P} (indexedAttachmentFresh I Qs rs As)
noncomputable abbrev batchIncomingComponents (_d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss) :=
  taggedComponentGraph P I (familyPointBound Qs) (indexedAttachmentFresh I Qs rs As)

end AttachmentBatchInputs

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

noncomputable def constantBatchLayerWitness (M : TransitiveGround.{u}) (τ : ZFSet.{u}) : ZFSet.{u} :=
  separatedLayerWitness I (constantFamilyGraph I τ) (M.batchTemplateFamily I P Qs rs As Es)
    (M.batchTemplateFamilyBound I P Qs rs As) d.batchIncomingComponents d.batchIncomingFiber

end AttachmentBatchInputs
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStoredPreparedFamilyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def certificateBasisMemberFormula {n} (v k : Fin n) : BoundedFormula n :=
  exGraphFields k (exPairFields 0 (exPairFields 0 (.mem v.succ.succ.succ.succ.succ.succ 1)))

end BoundedFormula






end PartitionPilot.Forcing



end OAI
end


