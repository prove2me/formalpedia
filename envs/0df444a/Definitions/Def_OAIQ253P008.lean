-- Prove2me | Definitions.Def_OAIQ253P008
-- name    : OAIQ253P008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T05:58:41.224232+00:00
-- url     : https://prove2.me/theorems/d4040425-5e92-4fb8-8d6d-3f4ee1c01fad
-- title:
--   Definitions bundle OAIQ253P008 of the split of OpenAI, The Partition Principle does not imply Choice
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice`, carved from OpenAI's openai/math development (OpenAI, *The Partition Principle does not imply Choice*, OpenAI Math Release, September 24, 2026, result family 244, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 42 declarations of OpenAI's Lean: 12 definitions and 30 theorems. The definitions and types are `OAI.PartitionPilot.Forcing.TransitiveGround.definable_representativeIndexStep`, `OAI.PartitionPilot.Forcing.TransitiveGround.fairPreparationConditionGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.fairPreparationStates`, `OAI.PartitionPilot.Forcing.TransitiveGround.fairPreparationTransition`, `OAI.PartitionPilot.Forcing.TransitiveGround.initialMainStage`, `OAI.PartitionPilot.Forcing.TransitiveGround.ordinaryMembershipDecisionFamily`, `OAI.PartitionPilot.Forcing.TransitiveGround.preparationEventSupportGraph`, `OAI.PartitionPilot.Forcing.TransitiveGround.preparationUsedSupportSequence`, `OAI.PartitionPilot.Forcing.TransitiveGround.preparationUsedSupportUnion`, `OAI.PartitionPilot.Forcing.TransitiveGround.profileRelationImageDefinition`, `OAI.PartitionPilot.Forcing.TransitiveGround.retainedPreparationSelections`, `OAI.PartitionPilot.Forcing.TransitiveGround.supportedCertificateFamilyRelation`.
--
--   **Sources.** They come from these modules of lean/OAI/SetTheory, in whole or in part: `PartitionPrinciple_Definability_ForcingHistoryConditionFormulas`, `PartitionPrinciple_Definability_GroundFlatCarrierSequences`, `PartitionPrinciple_Definability_GroundPackedRefinementFormulaData`, `PartitionPrinciple_Definability_GroundPreparationEventSupportGraphs`, `PartitionPrinciple_Definability_VisibilityProfileFormulas`, `PartitionPrinciple_Forcing_GroundFairPreparationConditionSequences`, `PartitionPrinciple_Forcing_GroundForcingHistorySuccessors`, `PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies`, `PartitionPrinciple_Forcing_GroundOrdinaryMembershipAntichainFamilies`, `PartitionPrinciple_Forcing_GroundRawRefinementStageWitnesses`, `PartitionPrinciple_Forcing_GroundRecordedPreparationSupportInclusions`, `PartitionPrinciple_Forcing_GroundRepresentedDomainConditions`, `PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies`, `PartitionPrinciple_Geometry_GroundFairPreparationMonotonicity`, `PartitionPrinciple_Geometry_GroundHartogs`, `PartitionPrinciple_Geometry_GroundNiceRefinementVisibility`, `PartitionPrinciple_Geometry_GroundRepresentativeIndexSteps`, `PartitionPrinciple_Geometry_GroundRetainedPreparationSelections`, `PartitionPrinciple_Geometry_GroundRowAssignmentProjections`, `PartitionPrinciple_Transfinite_GroundInitialMainStage`, `PartitionPrinciple_Transfinite_GroundStructuralRefinementHistories`.
--
--   **Imports.** It imports the published bundle `Def_PartitionPrinciple`; the bundles `OAIQ253P004` and `OAIQ253P005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ253P009` and `OAIQ253P010`.
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
import Definitions.Def_OAIQ253P004
import Definitions.Def_OAIQ253P005

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHartogs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem realize_representedOrdinalRelationFormula {r N : ZFSet.{u}}
    (hr : r ∈ M.sets) (hN : N ∈ M.sets) :
    Realize M.sets representedOrdinalRelationFormula (extend r (extend N Fin.elim0)) ↔
      ∃ A ∈ M.sets, ordinalSetProperty A ∧
        ∃ f ∈ M.sets, InjectionCode A N f ∧ r = ordinalImageOrder A N f := by
  have swapped (A : ZFSet.{u}) :
      (fun i => extend A (extend r (extend N Fin.elim0))
        (extend (1 : Fin 3) (extend 0 (extend 2 Fin.elim0)) i)) =
      extend r (extend A (extend N Fin.elim0)) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  rw [representedOrdinalRelationFormula, realize_ex]
  constructor
  · rintro ⟨A, hA, rel⟩
    have witness := (realize_reindex M.sets _ ordinalImageWitnessFormula _).1 rel
    rw [swapped A] at witness
    exact ⟨A, hA, (M.realize_ordinalImageWitnessFormula hr hA hN).1 witness⟩
  · rintro ⟨A, hA, witness⟩
    have rel := (M.realize_ordinalImageWitnessFormula hr hA hN).2 witness
    rw [← swapped A] at rel
    exact ⟨A, hA, (realize_reindex M.sets _ ordinalImageWitnessFormula _).2 rel⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentProjections
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem rowAssignmentRows_mem {Q C B : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets) :
    rowAssignmentRows Q C B ∈ M.sets :=
  M.graphRestriction_mem unions separation hQ (M.productFirst_mem pairing unions powers separation hC hB)

theorem rowAssignmentData_mem {Q C B : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets) :
    rowAssignmentData Q C B ∈ M.sets :=
  M.graphRestriction_mem unions separation hQ (M.productSecond_mem pairing unions powers separation hC hB)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceRefinementVisibility
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem realize_refinementIndexSelectionRawFormula {n}
    (z level r candidates relations T P order top : Fin n) (w : Fin 7 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexSelectionRawFormula z level r candidates relations T P order top w) env ↔
      env z = refinementIndexCode (env level) (env (w 0)) (env (w 1)) (env (w 2)) (env (w 3)) (env (w 4)) ∧
      ZFSet.pair (env (w 0)) (env (w 1)) ∈ env r ∧ env (w 0) ≠ env (w 1) ∧
      ZFSet.pair (env (w 0)) (env (w 5)) ∈ env candidates ∧ env (w 2) ∈ env (w 5) ∧
      ZFSet.pair (env (w 0)) (env (w 6)) ∈ env relations ∧
      env (w 3) ∈ env (w 6) ∧ env (w 4) ∈ env (w 6) ∧
      Realize M.sets (refinementValidityForcingFormula 0 1 2 3 4 5 6)
        ![env (w 2), env (w 3), env (w 4), env T, env P, env order, env top] := by
  have mapped : (fun j : Fin 7 => env (![w 2, w 3, w 4, T, P, order, top] j)) =
      ![env (w 2), env (w 3), env (w 4), env T, env P, env order, env top] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
  simp only [refinementIndexSelectionRawFormula, Realize,
    BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_refinementIndexFormula, BoundedFormula.truth_pairMembershipFormula,
    SetFormula.realize_reindex, mapped]

theorem realize_refinementIndexSelectionFormula {n}
    (z level r candidates relations T P order top : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementIndexSelectionFormula z level r candidates relations T P order top) env ↔
      RefinementIndexSelectionCode M (env level) (env r) (env candidates) (env relations)
        (env T) (env P) (env order) (env top) (env z) := by
  rw [refinementIndexSelectionFormula, realize_exBlock]
  have actual (w : Fin 7 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :=
    M.realize_refinementIndexSelectionRawFormula (suffixIndex n 7 z) (suffixIndex n 7 level)
      (suffixIndex n 7 r) (suffixIndex n 7 candidates) (suffixIndex n 7 relations)
      (suffixIndex n 7 T) (suffixIndex n 7 P) (suffixIndex n 7 order) (suffixIndex n 7 top)
      (prefixIndex n 7) (extendMany 7 w env) (extendMany_members 7 w env ground members)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨w, ground, selected⟩
    exact ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, (actual w ground).1 selected⟩
  · rintro ⟨C, E, U, Rf, Rc, N, V, equal, edge, strict, first, hU, second, hf, hc, forced⟩
    have fields := M.refinementIndexCode_fields_mem (equal ▸ members z)
    have hN := M.pair_right (M.transitive (members candidates) first)
    have hV := M.pair_right (M.transitive (members relations) second)
    let w : Fin 7 → ZFSet.{u} := ![C, E, U, Rf, Rc, N, V]
    have ground : ∀ j, w j ∈ M.sets :=
      Fin.cases fields.2.1 (Fin.cases fields.2.2.1 (Fin.cases fields.2.2.2.1
        (Fin.cases fields.2.2.2.2.1 (Fin.cases fields.2.2.2.2.2
          (Fin.cases hN (Fin.cases hV (fun j => Fin.elim0 j)))))))
    exact ⟨w, ground, (actual w ground).2 ⟨equal, edge, strict, first, hU, second, hf, hc, forced⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {level nodes r candidates relations T1 T2 T P order top : ZFSet.{u}}
    (hl : level ∈ M.sets) (hn : nodes ∈ M.sets) (hr : r ∈ M.sets)
    (hc : candidates ∈ M.sets) (hrel : relations ∈ M.sets)
    (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (ho : order ∈ M.sets) (ht : top ∈ M.sets) :
    M.refinementIndices level nodes r candidates relations T1 T2 T P order top ∈ M.sets := by
  let B := refinementIndexBound {level} nodes (M.groundRelations T1 P) (M.groundRelations T2 P)
  have hB := M.refinementIndexBound_mem pairing unions powers separation
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hl hl) hn
    (M.groundRelations_mem pairing unions powers separation hT1 hP)
    (M.groundRelations_mem pairing unions powers separation hT2 hP)
  let params : Fin 8 → ZFSet.{u} := ![level, r, candidates, relations, T, P, order, top]
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hl (Fin.cases hr (Fin.cases hc (Fin.cases hrel (Fin.cases hT
      (Fin.cases hP (Fin.cases ho (Fin.cases ht (fun j => Fin.elim0 j))))))))
  let φ : SetFormula 9 := refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8
  have ground := M.separation_mem separation φ params members hB
  have equal : ZFSet.sep (fun z => Realize M.sets φ (extend z params)) B =
      M.refinementIndices level nodes r candidates relations T1 T2 T P order top := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_refinementIndices]
    apply and_congr_right
    intro hz
    exact M.realize_refinementIndexSelectionFormula 0 1 2 3 4 5 6 7 8
      (extend z params) (Fin.cases (M.transitive hB hz) members)
  exact equal ▸ ground

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

theorem niceRefinementIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {level T1 T2 : ZFSet.{u}} (valid : ∀ z ∈ T1, IsName s z)
    (hl : level ∈ M.sets) (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (nodeOrder : b.conditionOrder ∈ M.sets)
    (first : M.niceNameCandidateGraph a s b T1 d.principalFix ∈ M.sets)
    (second : M.niceNameCandidateGraph a s b T2 d.principalFix ∈ M.sets) :
    M.niceRefinementIndices a s b d level T1 T2 valid ∈ M.sets := by
  have top := M.transitive carrier (s.encode_mem ⊤)
  exact M.refinementIndices_mem pairing unions powers separation hl nodes nodeOrder first second
    hT1 hT2 (M.familySet_mem s ⊤ pairing unions powers separation hT1 top valid) carrier order top

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (level nodes r candidates relations T1 T2 T P order top : ZFSet.{u})
local notation "I" => M.refinementIndices level nodes r candidates relations T1 T2 T P order top
local notation "bounds" => (![Singleton.singleton level, nodes, nodes, M.groundRelations T1 P,
  M.groundRelations T2 P, M.groundRelations T2 P])

theorem refinementIndices_fields_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hl : level ∈ M.sets) (hn : nodes ∈ M.sets) (hr : r ∈ M.sets)
    (hc : candidates ∈ M.sets) (hrel : relations ∈ M.sets)
    (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (ho : order ∈ M.sets) (ht : top ∈ M.sets) :
    ∀ j : Fin 6, refinementIndexFieldGraph I (bounds j) j ∈ M.sets := by
  have hI := M.refinementIndices_mem pairing unions powers separation
    hl hn hr hc hrel hT1 hT2 hT hP ho ht
  have hV := M.groundRelations_mem pairing unions powers separation hT1 hP
  have hW := M.groundRelations_mem pairing unions powers separation hT2 hP
  have hs : ({level} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hl hl
  have ground : ∀ j : Fin 6, bounds j ∈ M.sets :=
    Fin.cases hs (Fin.cases hn (Fin.cases hn (Fin.cases hV
      (Fin.cases hW (Fin.cases hW (fun j => Fin.elim0 j))))))
  exact fun j => M.refinementIndexFieldGraph_mem pairing unions powers separation hI (ground j) j

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentedDomainConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneForcingAt {n m : Nat} (phi : SetFormula m) (p P r : Fin n)
    (names : Fin m → Fin n) (env : Fin n → ZFSet.{u}) :
    Realize M.sets (stageOneForcingAt phi p P r names) env ↔
      stageOneRawForces M (env P) (env r) (env p) phi (fun j => env (names j)) := by
  rw [stageOneForcingAt, realize_reindex, map_extend, map_extend, map_extend]
  rfl

theorem realize_stageOneClassAt {n : Nat} (c T R w P r top : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Realize M.sets (stageOneClassAt c T R w P r top) env ↔
      stageOneRawClass M (env T) (env P) (env r) (env top) (env R) (env w) (env c) := by
  rw [stageOneClassAt, stageOneRawClass, realize_reindex]
  simp only [map_extend]
  have empty : (fun j : Fin 0 => env (Fin.elim0 j)) = Fin.elim0 := funext (fun j => Fin.elim0 j)
  rw [empty]

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_VisibilityProfileFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneProfileAt {n : Nat} (P r lower nodes nodeOrder visibility E bu aw : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneProfileAt P r lower nodes nodeOrder visibility E bu aw) env ↔
      stageOneRawProfile M (env P) (env r) (env lower) (env nodes) (env nodeOrder) (env visibility)
        (env E) (env bu) (env aw) := by
  rw [stageOneProfileAt]
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  constructor
  · intro h v hv below
    have hvM := M.transitive (members nodes) hv
    have first := (realize_imp M.sets _ _ _).1 (h v hvM) hv
    have selected := (realize_imp M.sets _ _ _).1 first
      ((M.realize_stageOnePairLookup E.succ 0 nodeOrder.succ _ (Fin.cases hvM members)).2 below)
    obtain ⟨V, hV, entry, forced⟩ := (realize_ex M.sets _ _).1 selected
    refine ⟨V, hV, (M.realize_stageOnePairLookup 1 0 visibility.succ.succ _
      (Fin.cases hV (Fin.cases hvM members))).1 entry, ?_⟩
    have value := (M.realize_stageOneForcingAt _ _ _ _ _ _).1 forced
    rw [map_three_p1] at value
    exact value
  · intro h v hvM
    apply (realize_imp M.sets _ _ _).2
    intro hv
    apply (realize_imp M.sets _ _ _).2
    intro below
    have relation := (M.realize_stageOnePairLookup E.succ 0 nodeOrder.succ _ (Fin.cases hvM members)).1 below
    obtain ⟨V, hV, entry, forced⟩ := h v hv relation
    apply (realize_ex M.sets _ _).2
    refine ⟨V, hV, (M.realize_stageOnePairLookup 1 0 visibility.succ.succ _
      (Fin.cases hV (Fin.cases hvM members))).2 entry, ?_⟩
    apply (M.realize_stageOneForcingAt _ _ _ _ _ _).2
    rw [map_three_p1]
    exact forced

theorem realize_stageOneCompatibilityAt {n : Nat} (P r lower visibility maps C idx bu aw : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCompatibilityAt P r lower visibility maps C idx bu aw) env ↔
      stageOneRawCompatibility M (env P) (env r) (env lower) (env visibility) (env maps)
        (env C) (env idx) (env bu) (env aw) := by
  rw [stageOneCompatibilityAt, realize_ex]
  constructor
  · rintro ⟨V, hV, body⟩
    obtain ⟨D, hD, visible, mapped, forced⟩ := (realize_ex M.sets _ _).1 body
    refine ⟨V, hV, D, hD,
      (M.realize_stageOnePairLookup C.succ.succ 1 visibility.succ.succ _ (Fin.cases hD (Fin.cases hV members))).1 visible,
      (M.realize_stageOnePairLookup idx.succ.succ 0 maps.succ.succ _ (Fin.cases hD (Fin.cases hV members))).1 mapped, ?_⟩
    have value := (M.realize_stageOneForcingAt _ _ _ _ _ _).1 forced
    rw [map_four_p1] at value
    exact value
  · rintro ⟨V, hV, D, hD, visible, mapped, forced⟩
    refine ⟨V, hV, ?_⟩
    apply (realize_ex M.sets _ _).2
    refine ⟨D, hD,
      (M.realize_stageOnePairLookup C.succ.succ 1 visibility.succ.succ _ (Fin.cases hD (Fin.cases hV members))).2 visible,
      (M.realize_stageOnePairLookup idx.succ.succ 0 maps.succ.succ _ (Fin.cases hD (Fin.cases hV members))).2 mapped, ?_⟩
    apply (M.realize_stageOneForcingAt _ _ _ _ _ _).2
    rw [map_four_p1]
    exact forced

end TransitiveGround

end

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPackedRefinementFormulaData
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneSingleBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 7 → Fin n)
    (t u w lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneSingleBodyAt d f t u w lower) env ↔
      stageOneRawSingleBody M (fun j => env (d j)) (fun j => env (f j))
        (env t) (env u) (env w) (env lower) := by
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · rw [M.realize_stageOneForcingAt, map_three_p0]
  apply and_congr
  · exact M.realize_stageOneProfileAt _ _ _ _ _ _ _ _ _ env members
  exact M.realize_stageOneCompatibilityAt _ _ _ _ _ _ _ _ _ env members

theorem realize_stageOneSingleAt {n : Nat} (d : Fin 15 → Fin n)
    (t u w lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneSingleAt d t u w lower) env ↔
      stageOneRawSingle M (fun j => env (d j)) (env t) (env u) (env w) (env lower) := by
  rw [stageOneSingleAt, realize_exBlock]
  unfold stageOneRawSingle
  apply exists_congr
  intro fields
  apply and_congr_right
  intro fieldMembers
  rw [M.realize_stageOneSingleBodyAt _ _ _ _ _ _ _ (extendMany_members 7 fields env fieldMembers members)]
  simp only [extendMany_prefix, extendMany_suffix]

end TransitiveGround





namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneCollisionBodyAt {n : Nat} (d : Fin 15 → Fin n) (f : Fin 6 → Fin n)
    (t u u' w w' lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCollisionBodyAt d f t u u' w w' lower) env ↔
      stageOneRawCollisionBody M (fun j => env (d j)) (fun j => env (f j))
        (env t) (env u) (env u') (env w) (env w') (env lower) := by
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOnePairLookup _ _ _ env members
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  apply and_congr
  · exact M.realize_stageOneClassAt _ _ _ _ _ _ _ env
  rw [M.realize_stageOneForcingAt, map_four_p0]

theorem realize_stageOneCollisionAt {n : Nat} (d : Fin 15 → Fin n)
    (t u u' w w' lower : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCollisionAt d t u u' w w' lower) env ↔
      stageOneRawCollision M (fun j => env (d j)) (env t) (env u) (env u') (env w) (env w') (env lower) := by
  rw [stageOneCollisionAt, realize_exBlock]
  unfold stageOneRawCollision
  apply exists_congr
  intro fields
  apply and_congr_right
  intro fieldMembers
  rw [M.realize_stageOneCollisionBodyAt _ _ _ _ _ _ _ _ _ (extendMany_members 6 fields env fieldMembers members)]
  simp only [extendMany_prefix, extendMany_suffix]

end TransitiveGround





namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneSinglesFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneSinglesFormula d A lower) env ↔
      ∀ t ∈ env (d 0), ∀ u ∈ env (d 6), ∀ w ∈ env (d 6), stageOneAssignment t u w ∈ env A →
        stageOneRawSingle M (fun j => env (d j)) t u w (env lower) := by
  rw [stageOneSinglesFormula, realize_allBlock]
  have actual (v : Fin 3 → ZFSet.{u}) (ground : ∀ j, v j ∈ M.sets) :
      Realize M.sets (imp (BoundedFormula.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 (d 0)))
    (.conj (.mem (prefixIndex n 3 1) (suffixIndex n 3 (d 6))) (.conj (.mem (prefixIndex n 3 2) (suffixIndex n 3 (d 6)))
      (BoundedFormula.rightTripleMembershipFormula (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2) (suffixIndex n 3 A))))).toFormula
    (stageOneSingleAt (fun j => suffixIndex n 3 (d j)) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2) (suffixIndex n 3 lower))) (extendMany 3 v env) ↔
        (v 0 ∈ env (d 0) ∧ v 1 ∈ env (d 6) ∧ v 2 ∈ env (d 6) ∧ stageOneAssignment (v 0) (v 1) (v 2) ∈ env A) →
          stageOneRawSingle M (fun j => env (d j)) (v 0) (v 1) (v 2) (env lower) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ (extendMany_members 3 v env ground members),
      M.realize_stageOneSingleAt _ _ _ _ _ _ (extendMany_members 3 v env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_rightTripleMembershipFormula,
      extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · intro h t ht u hu w hw entry
    have ground : ∀ j : Fin 3, (![t,u,w] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members (d 0)) ht)
        (Fin.cases (M.transitive (members (d 6)) hu)
          (Fin.cases (M.transitive (members (d 6)) hw) (fun j => Fin.elim0 j)))
    exact (actual ![t,u,w] ground).1 (h _ ground) ⟨ht,hu,hw,entry⟩
  · intro h v ground
    apply (actual v ground).2
    rintro ⟨ht,hu,hw,entry⟩
    exact h (v 0) ht (v 1) hu (v 2) hw entry

theorem realize_stageOneCollisionsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCollisionsFormula d A lower) env ↔
      ∀ t ∈ env (d 0), ∀ u ∈ env (d 6), ∀ u' ∈ env (d 6), ∀ w ∈ env (d 6), ∀ w' ∈ env (d 6),
        stageOneAssignment t u w ∈ env A → stageOneAssignment t u' w' ∈ env A →
          stageOneRawCollision M (fun j => env (d j)) t u u' w w' (env lower) := by
  rw [stageOneCollisionsFormula, realize_allBlock]
  have actual (v : Fin 5 → ZFSet.{u}) (ground : ∀ j, v j ∈ M.sets) :
      Realize M.sets (imp (BoundedFormula.conj (.mem (prefixIndex n 5 0) (suffixIndex n 5 (d 0)))
    (.conj (.mem (prefixIndex n 5 1) (suffixIndex n 5 (d 6))) (.conj (.mem (prefixIndex n 5 2) (suffixIndex n 5 (d 6)))
      (.conj (.mem (prefixIndex n 5 3) (suffixIndex n 5 (d 6))) (.conj (.mem (prefixIndex n 5 4) (suffixIndex n 5 (d 6)))
        (.conj (BoundedFormula.rightTripleMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 A))
          (BoundedFormula.rightTripleMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (prefixIndex n 5 4) (suffixIndex n 5 A)))))))).toFormula
    (stageOneCollisionAt (fun j => suffixIndex n 5 (d j)) (prefixIndex n 5 0) (prefixIndex n 5 1) (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4) (suffixIndex n 5 lower))) (extendMany 5 v env) ↔
        (v 0 ∈ env (d 0) ∧ v 1 ∈ env (d 6) ∧ v 2 ∈ env (d 6) ∧ v 3 ∈ env (d 6) ∧ v 4 ∈ env (d 6) ∧
          stageOneAssignment (v 0) (v 1) (v 3) ∈ env A ∧ stageOneAssignment (v 0) (v 2) (v 4) ∈ env A) →
          stageOneRawCollision M (fun j => env (d j)) (v 0) (v 1) (v 2) (v 3) (v 4) (env lower) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 v env ground members),
      M.realize_stageOneCollisionAt _ _ _ _ _ _ _ _ (extendMany_members 5 v env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_rightTripleMembershipFormula,
      extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · intro h t ht u hu u' hu' w hw w' hw' first second
    have ground : ∀ j : Fin 5, (![t,u,u',w,w'] : Fin 5 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members (d 0)) ht)
        (Fin.cases (M.transitive (members (d 6)) hu)
          (Fin.cases (M.transitive (members (d 6)) hu')
            (Fin.cases (M.transitive (members (d 6)) hw)
              (Fin.cases (M.transitive (members (d 6)) hw') (fun j => Fin.elim0 j)))))
    exact (actual ![t,u,u',w,w'] ground).1 (h _ ground) ⟨ht,hu,hu',hw,hw',first,second⟩
  · intro h v ground
    apply (actual v ground).2
    rintro ⟨ht,hu,hu',hw,hw',first,second⟩
    exact h (v 0) ht (v 1) hu (v 2) hu' (v 3) hw (v 4) hw' first second

theorem realize_stageOneTestsFormula {n : Nat} (d : Fin 15 → Fin n) (A lower : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneTestsFormula d A lower) env ↔
      stageOneRawTests M (fun j => env (d j)) (env A) (env lower) := by
  exact and_congr (M.realize_stageOneSinglesFormula d A lower env members)
    (M.realize_stageOneCollisionsFormula d A lower env members)

end TransitiveGround





namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageTwoConditionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (d : Fin 15 → Fin n) (levels alpha z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageTwoConditionFormula d levels alpha z) env ↔
      StageTwoConditionCode M (env levels) (env alpha) (fun j => env (d j)) (env z) := by
  rw [stageTwoConditionFormula, realize_exBlock]
  have actual (f : Fin 4 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 4 z)
          (prefixIndex n 4 0) (prefixIndex n 4 1)).toFormula
        (.conj (BoundedFormula.assignmentCutFormula (prefixIndex n 4 2)
          (suffixIndex n 4 levels) (suffixIndex n 4 alpha) (prefixIndex n 4 1)).toFormula
          (.conj (BoundedFormula.orderedPairFormula (prefixIndex n 4 3)
            (prefixIndex n 4 0) (prefixIndex n 4 2)).toFormula
            (.conj (.mem (prefixIndex n 4 3) (suffixIndex n 4 (d 7)))
              (stageOneTestsFormula (fun j => suffixIndex n 4 (d j))
                (prefixIndex n 4 1) (prefixIndex n 4 3))))))
          (extendMany 4 f env) ↔
        env z = ZFSet.pair (f 0) (f 1) ∧
          f 2 = assignmentCut (env levels) (env alpha) (f 1) ∧
          f 3 = ZFSet.pair (f 0) (f 2) ∧ f 3 ∈ env (d 7) ∧
          stageOneRawTests M (fun j => env (d j)) (f 1) (f 3) := by
    have allground := extendMany_members 4 f env ground members
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground,
        BoundedFormula.truth_orderedPairFormula]
      simp only [extendMany_prefix, extendMany_suffix]
    apply and_congr
    · rw [M.realize_assignmentCutFormula _ _ _ _ _ allground]
      simp only [extendMany_prefix, extendMany_suffix]
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ allground,
        BoundedFormula.truth_orderedPairFormula]
      simp only [extendMany_prefix]
    apply and_congr
    · rfl
    rw [M.realize_stageOneTestsFormula _ _ _ _ allground]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨pair, cut, lower, valid, tests⟩ := (actual f ground).1 body
    rw [cut] at lower
    exact ⟨f 0, f 1, pair, lower ▸ valid, lower ▸ tests⟩
  · rintro ⟨row, A, equal, valid, tests⟩
    have hrow : row ∈ M.sets := M.pair_left (equal ▸ members z)
    have hA : A ∈ M.sets := M.pair_right (equal ▸ members z)
    have hcut := M.assignmentCut_mem separation (members levels) (members alpha) hA
    have hlower := M.orderedPair_mem pairing hrow hcut
    let cut := assignmentCut (env levels) (env alpha) A
    let f : Fin 4 → ZFSet.{u} := ![row, A, cut, ZFSet.pair row cut]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases hrow (Fin.cases hA (Fin.cases hcut
        (Fin.cases hlower (fun j => Fin.elim0 j))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, rfl, rfl, valid, tests⟩⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_packedSuccessorConditionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (levels alpha data z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (packedSuccessorConditionFormula levels alpha data z) env ↔
      PackedSuccessorConditionCode M (env levels) (env alpha) (env data) (env z) := by
  rw [packedSuccessorConditionFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, ground, tuple, valid⟩
    have bounds := extendMany_members 15 fields env ground members
    have equal := (BoundedFormula.truth_nonemptyTupleFormula 14
      (suffixIndex n 15 data) (prefixIndex n 15) _).1
      ((BoundedFormula.realize_toFormula M _ _ bounds).1 tuple)
    have actual := (M.realize_stageTwoConditionFormula pairing separation (prefixIndex n 15)
      (suffixIndex n 15 levels) (suffixIndex n 15 alpha) (suffixIndex n 15 z)
      (extendMany 15 fields env) bounds).1 valid
    simp only [extendMany_prefix, extendMany_suffix] at equal actual
    exact ⟨fields, equal, actual⟩
  · rintro ⟨fields, equal, valid⟩
    have ground := M.refinementFormulaDataCode_fields_mem fields (equal ▸ members data)
    have bounds := extendMany_members 15 fields env ground members
    refine ⟨fields, ground, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 14
        (suffixIndex n 15 data) (prefixIndex n 15) _).2
      simpa only [extendMany_prefix, extendMany_suffix, refinementFormulaDataCode] using equal
    · apply (M.realize_stageTwoConditionFormula pairing separation (prefixIndex n 15)
        (suffixIndex n 15 levels) (suffixIndex n 15 alpha) (suffixIndex n 15 z)
        (extendMany 15 fields env) bounds).2
      simpa only [extendMany_prefix, extendMany_suffix] using valid

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ForcingHistoryConditionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_forcingHistoryEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (alpha history levels z : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (forcingHistoryEntryFormula alpha history levels z) env ↔
      ∃ data, ZFSet.pair (env alpha) data ∈ env history ∧
        PackedSuccessorConditionCode M (env levels) (env alpha) data (env z) := by
  rw [forcingHistoryEntryFormula, realize_ex]
  have actual (data : ZFSet.{u}) (ground : data ∈ M.sets) :
      Realize M.sets
        (.conj (BoundedFormula.pairMembershipFormula alpha.succ 0 history.succ).toFormula
          (packedSuccessorConditionFormula levels.succ alpha.succ 0 z.succ)) (extend data env) ↔
        ZFSet.pair (env alpha) data ∈ env history ∧
          PackedSuccessorConditionCode M (env levels) (env alpha) data (env z) := by
    apply and_congr
    · rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases ground members),
        BoundedFormula.truth_pairMembershipFormula]
      rfl
    · exact M.realize_packedSuccessorConditionFormula pairing separation _ _ _ _ _ (Fin.cases ground members)
  constructor
  · rintro ⟨data, ground, checked⟩
    exact ⟨data, (actual data ground).1 checked⟩
  · rintro ⟨data, entry, checked⟩
    have ground := M.pair_right (M.transitive (members history) entry)
    exact ⟨data, ground, (actual data ground).2 ⟨entry, checked⟩⟩

theorem realize_forcingHistoryConditionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (stages history levels z : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (forcingHistoryConditionFormula stages history levels z) env ↔
      ForcingHistoryConditionCode M (env stages) (env history) (env levels) (env z) := by
  change (∀ alpha ∈ M.sets, Realize M.sets
    (.imp (.mem 0 stages.succ) (forcingHistoryEntryFormula 0 history.succ levels.succ z.succ))
      (extend alpha env)) ↔ _
  constructor
  · intro checked alpha member
    have ground := M.transitive (members stages) member
    exact (M.realize_forcingHistoryEntryFormula pairing separation 0 history.succ levels.succ z.succ
      (extend alpha env) (Fin.cases ground members)).1
      ((realize_imp M.sets _ _ _).1 (checked alpha ground) member)
  · intro valid alpha ground
    apply (realize_imp M.sets _ _ _).2
    intro member
    exact (M.realize_forcingHistoryEntryFormula pairing separation 0 history.succ levels.succ z.succ
      (extend alpha env) (Fin.cases ground members)).2 (valid alpha member)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFlatCarrierSequences
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {R : Type u} (c : Presentation R) (Q B : ZFSet.{u})
variable (shape : Q ⊆ ZFSet.prod c.carrier B)
local notation "s" => SetMembers.presentation Q

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem flatCarrierSequence_projections_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hQ : Q ∈ M.sets) (hRows : c.carrier ∈ M.sets) (hB : B ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (seq : Nat → SetMembers Q)
    (whole : groundSequenceGraph seq ∈ M.sets) :
    natPresentation.graph c (fun n => flatCarrierRow c Q B shape (seq n.down)) ∈ M.sets ∧
      groundSequenceGraph (fun n => flatCarrierData c Q B shape (seq n)) ∈ M.sets := by
  obtain ⟨rowEq, dataEq⟩ := flatCarrier_coordinateGraphs c Q B shape
  have rowGround := M.rowAssignmentRows_mem pairing unions powers separation hQ hRows hB
  have dataGround := M.rowAssignmentData_mem pairing unions powers separation hQ hRows hB
  rw [← rowEq] at rowGround
  rw [← dataEq] at dataGround
  have first := M.relationCompose_mem pairing unions powers separation omega hQ hRows whole rowGround
  have second := M.relationCompose_mem pairing unions powers separation omega hQ hB whole dataGround
  have firstEq := natPresentation.relationCompose_graph (s) c (fun n => seq n.down) (flatCarrierRow c Q B shape)
  have secondEq := natPresentation.relationCompose_graph (s) (SetMembers.presentation B)
    (fun n => seq n.down) (flatCarrierData c Q B shape)
  change relationCompose ZFSet.omega Q c.carrier (groundSequenceGraph seq) ((s).graph c _) = _ at firstEq
  change relationCompose ZFSet.omega Q B (groundSequenceGraph seq) ((s).graph (SetMembers.presentation B) _) = _ at secondEq
  rw [firstEq] at first
  rw [secondEq] at second
  exact ⟨first, second⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundForcingHistorySuccessors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem forcingHistoryConditions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {rows I T stages history levels : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hLevels : levels ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.forcingHistoryConditions rows I T stages history levels ∈ M.sets := by
  have bound := M.stageOneCandidateBound_mem pairing unions powers separation hRows hI hT omega
  let params : Fin 3 → ZFSet.{u} := ![stages, history, levels]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hStages (Fin.cases hHistory (Fin.cases hLevels (fun j => Fin.elim0 j)))
  have selected := M.separation_mem separation (forcingHistoryConditionFormula 1 2 3 0) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (forcingHistoryConditionFormula 1 2 3 0)
      (extend z params)) (M.stageOneCandidateBound rows I T) =
      M.forcingHistoryConditions rows I T stages history levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_forcingHistoryConditions]
    apply and_congr_right
    intro member
    exact M.realize_forcingHistoryConditionFormula pairing separation 1 2 3 0 (extend z params)
      (Fin.cases (M.transitive bound member) ground)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialMainStage
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {C D rD c d0 d1 : ZFSet.{u}}
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
variable (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) (gap : ZFSet.pair d0 d1 ∈ rD)

noncomputable def initialMainStage : GroundMainStage M C D rD := by
  have ground := M.initialMainAlgebra_ground pairing unions separation infinite
  have hP := ground.1
  have hG := ground.2.1
  have hr := ground.2.2.1
  have hMeet := ground.2.2.2.1
  have hm := ground.2.2.2.2.1
  have hInv := ground.2.2.2.2.2.1
  have hA := ground.2.2.2.2.2.2
  have hBottom := M.transitive hP InitialMainAlgebra.bottom_mem
  have hTop := M.transitive hP InitialMainAlgebra.top_mem
  have height := M.twoPointHeight_mem pairing hBottom hTop (M.transitive hC hc)
    (M.transitive hD h0) (M.transitive hD h1)
  have strict : StrictLexHeightCode InitialMainAlgebra.carrier C D InitialMainAlgebra.order
      (twoPointHeight InitialMainAlgebra.bottom InitialMainAlgebra.top c d0 d1) rD := by
    rw [InitialMainAlgebra.carrier_eq_pair]
    exact twoPointHeight_strict InitialMainAlgebra.bottom_ne_top hc h0 h1 gap
  have small : M.groundEmbeddable
      (relationImage InitialMainAlgebra.carrier (ZFSet.prod C D)
        (twoPointHeight InitialMainAlgebra.bottom InitialMainAlgebra.top c d0 d1)) ZFSet.omega := by
    rw [InitialMainAlgebra.carrier_eq_pair]
    exact M.twoPointHeight_range_countable pairing unions powers separation infinite hC hD hc h0 h1
  exact GroundMainStage.ofCodes pairing unions powers separation hP hG hr hMeet hA hm hInv
    hC hD hrD height InitialMainAlgebra.meet_code InitialMainAlgebra.group_code
    InitialMainAlgebra.action_code InitialMainAlgebra.bottom_mem InitialMainAlgebra.least
    InitialMainAlgebra.top_mem InitialMainAlgebra.greatest strict small

end TransitiveGround

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRawRefinementStageWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem forcingStageCode_fields {P order top action : ZFSet.{u}}
    (ground : forcingStageCode P order top action ∈ M.sets) :
    P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets := by
  have fields := M.nonemptyTupleCode_field_mem 3 ![P, order, top, action] ground
  exact ⟨fields 0, fields 1, fields 2, fields 3⟩

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralRefinementHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

theorem realizeHistoryReindex (U : Set ZFSet.{u}) (φ : SetFormula 9)
    (env : Fin 8 → ZFSet.{u}) (z y x : ZFSet.{u}) :
    Realize U (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8] φ)
      (extend x (extend y (extend z env))) ↔
      Realize U φ (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5])) := by
  rw [realize_reindex]
  have args : (fun j : Fin 9 =>
      extend x (extend y (extend z env)) (![0, 1, 9, 3, 4, 5, 6, 7, 8] j)) =
      extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5]) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))))) j
  exact args ▸ Iff.rfl

theorem historyFormula_correct (φ : SetFormula 9) (env : Fin 8 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (target : ZFSet.{u}) (target_mem : target ∈ M.sets)
    (meaning : ∀ y ∈ M.sets, y ∈ target ↔
      ∃ x ∈ env 7, Realize M.sets φ
        (extend x (extend y ![env 6, env 0, env 1, env 2, env 3, env 4, env 5])))
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets
      (exactSetFormula 0 (.ex (.conj (.mem 0 10)
        (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8] φ))))
      (extend z env) ↔ z = target := by
  apply M.realize_exactSetFormula 0 _ (extend z env) hz
    (fun _ h => M.transitive target_mem h)
  intro y hy
  refine (realize_ex M.sets _ _).trans ?_
  change (∃ x ∈ M.sets, x ∈ env 7 ∧ Realize M.sets
    (SetFormula.reindex ![0, 1, 9, 3, 4, 5, 6, 7, 8] φ)
      (extend x (extend y (extend z env)))) ↔ y ∈ target
  refine Iff.trans ?_ (meaning y hy).symm
  constructor
  · rintro ⟨x, _, hx, holds⟩
    exact ⟨x, hx, (realizeHistoryReindex M.sets φ env z y x).mp holds⟩
  · rintro ⟨x, hx, holds⟩
    refine ⟨x, M.transitive (members 7) hx, hx, ?_⟩
    exact (realizeHistoryReindex M.sets φ env z y x).mpr holds

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)

noncomputable def supportedCertificateFamilyRelation
    (nodeOrder J : ZFSet.{u}) (validJ : ∀ z ∈ J, IsName s z)
    (H : ConditionFilter P) : ZFSet.{u} :=
  supportedCertificateRelation J (M.groundPower b.carrier)
    (M.groundSmallSubsets b.carrier ZFSet.omega)
    (M.groundRelations b.carrier (M.niceSupportNameCodes a s T K)) b.carrier
    (M.niceSupportNameCodes a s T K) nodeOrder (M.niceSupportRelation a s b T K)
    (Name.eval {p | H.mem p} (Name.inputEvaluationName s J validJ))
    (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
    (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
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

noncomputable def profileRelationImageDefinition
    (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 3 → ZFSet.{u} =>
      relationImage (env 0) (env 1) (env 2)) where
  formula := (BoundedFormula.relationImageEqualityFormula 0 1 2 3).toFormula
  closed := fun _ members => M.relationImage_mem separation (members 0) (members 1) (members 2)
  correct := by
    intro env members z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
      BoundedFormula.truth_relationImageEqualityFormula]
    rfl

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPreparationEventSupportGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def preparationEventSupportGraph (nodes E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ event support, z = ZFSet.pair event support ∧
    support = preparationEventUsedSupports nodes event) (ZFSet.prod E (M.groundPower nodes))

noncomputable def preparationUsedSupportSequence (nodes E events : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose ZFSet.omega E (M.groundPower nodes) events (M.preparationEventSupportGraph nodes E)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFairPreparationMonotonicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def fairPreparationStates (Q stages U E0 enumSelector : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (FairPreparationStateCode ZFSet.omega E0 enumSelector)
    (ZFSet.prod ZFSet.omega (ZFSet.prod Q
      (ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U)))))

noncomputable def fairPreparationTransition
    (Q stages U E0 enumSelector prepSelector gridGraph : ZFSet.{u}) : ZFSet.{u} :=
  let states := M.fairPreparationStates Q stages U E0 enumSelector
  ZFSet.sep (fun z => ∃ state next, z = ZFSet.pair state next ∧
    FairPreparationStepCode ZFSet.omega E0 stages U enumSelector prepSelector gridGraph state next)
    (ZFSet.prod states states)

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFairPreparationConditionSequences
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def fairPreparationConditionGraph
    (Q stages U E0 orbit : ZFSet.{u}) : ZFSet.{u} :=
  let tail := ZFSet.prod (M.groundRelations ZFSet.omega E0) (insert ∅ (ZFSet.prod stages U))
  let middle := ZFSet.prod Q tail
  let bound := ZFSet.prod ZFSet.omega middle
  relationCompose ZFSet.omega middle Q
    (relationCompose ZFSet.omega bound middle orbit (productSecond ZFSet.omega middle))
    (productFirst Q tail)

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOrdinaryMembershipAntichainFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def ordinaryMembershipDecisionFamily (T Q order tau : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun sigma : T => sigma.val)
    (fun sigma => M.ordinaryMembershipDecisions Q order sigma.val tau)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecordedPreparationSupportInclusions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def preparationUsedSupportUnion (nodes E events : ZFSet.{u}) : ZFSet.{u} :=
  (relationImage ZFSet.omega (M.groundPower nodes)
    (M.preparationUsedSupportSequence nodes E events)).sUnion

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRepresentativeIndexSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem representativeIndexAdditions_mem (separation : SeparationSchema M.sets)
    {I T Q c X : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (hc : c ∈ M.sets) (hX : X ∈ M.sets) :
    representativeIndexAdditions I T Q c X ∈ M.sets := by
  let params := extend I (extend T (extend Q (extend c (extend X Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.representativeIndexAdditionsMemberFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hT (Fin.cases hQ (Fin.cases hc
      (Fin.cases hX (fun i => Fin.elim0 i)))))) hI
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.representativeIndexAdditionsMemberFormula 0 1 2 3 4 5)
      (extend z params)) I = representativeIndexAdditions I T Q c X := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_representativeIndexAdditionsMemberFormula]
    change (z ∈ I ∧ z ∈ representativeIndexAdditions I T Q c X) ↔ _
    exact ⟨And.right, fun h =>
      ⟨((mem_representativeIndexAdditions I T Q c X z).1 h).1, h⟩⟩
  exact equal ▸ selected

theorem representativeIndexStep_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {I T Q c X : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (hc : c ∈ M.sets) (hX : X ∈ M.sets) :
    representativeIndexStep I T Q c X ∈ M.sets :=
  M.binary_union_mem pairing unions hX
    (M.representativeIndexAdditions_mem separation hI hT hQ hc hX)

noncomputable def definable_representativeIndexStep
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 5 → ZFSet.{u} =>
      representativeIndexStep (env 1) (env 2) (env 3) (env 4) (env 0)) where
  formula := exactSetFormula 0 (disj (.mem 0 2)
    (BoundedFormula.representativeIndexAdditionsMemberFormula 0 3 4 5 6 2).toFormula)
  closed := fun _ members => M.representativeIndexStep_mem pairing unions separation
    (members 1) (members 2) (members 3) (members 4) (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun _ h => M.transitive (M.representativeIndexStep_mem pairing unions separation
        (members 1) (members 2) (members 3) (members 4) (members 0)) h)
    intro w hw
    rw [realize_disj, BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members)),
      BoundedFormula.truth_representativeIndexAdditionsMemberFormula]
    exact ZFSet.mem_union.symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRetainedPreparationSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def retainedPreparationSelections (_M : TransitiveGround.{u})
    (A L R p levels : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x alpha row sourceA tail,
    z = ZFSet.pair x (ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail)) ∧
    ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row sourceA)) (ZFSet.pair p tail) ∈ R ∧
    sourceA ⊆ A ∧ x ∈ sourceA ∧ ZFSet.pair x alpha ∈ levels) (ZFSet.prod A L)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end


