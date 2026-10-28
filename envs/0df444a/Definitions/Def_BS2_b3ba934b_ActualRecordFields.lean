-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualRecordFields
-- name    : BS2_b3ba934b_ActualRecordFields
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:02:30.087789+00:00
-- url     : https://prove2.me/theorems/ec7b6deb-e4d4-497a-8bb3-f885bf9de0c3
-- title:
--   Sensitivity separation: ActualRecordFields (complete source module)
-- statement:
--   Complete Lean source module `ActualRecordFields` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. Original declarations and proof bodies are retained, with local import module paths rewritten for Prove2Me and three residual references explicitly qualified as ThreeBoundRecordFields.residual to avoid the Mathlib topology name collision. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualRecordFields.lean; original SHA-256 618a77beead468671fb9ea5d54895892f91ee92042329e87133995eded05c45f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Transport the exact record fields to the actual high candidate heads. -/
import Definitions.Def_BS2_b3ba934b_Q2RecordFields
import Definitions.Def_BS2_b3ba934b_ActualKindFilters
import Definitions.Def_BS2_b3ba934b_ActualQ2Enumeration

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundActualRecordFields
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundActualKindFilters
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundQ2 ThreeBoundRecordFields
open ThreeBoundActualEnumeration
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem guardSources_subset_high (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (t : ℕ → Fin n) (j : Fin n)
    (x : ((V × Bool) × I) → Bool) : guardSources S F t j x ⊆ highHeads S F t j x := by
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr (Finset.mem_filter.mp hw).2⟩

theorem guardSources_eq_filter (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (t : ℕ → Fin n) (j : Fin n)
    (x : ((V × Bool) × I) → Bool) (tag : V → Kind)
    (htag : ∀ w ∈ highHeads S F t j x,
      Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
        (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card
        (child x w false) (child x w true) (tag w)) :
    guardSources S F t j x = (highHeads S F t j x).filter fun w => isGuard (tag w) = true := by
  ext w
  constructor
  · intro hw
    have hh := guardSources_subset_high S F t j x hw
    refine Finset.mem_filter.mpr ⟨hh,?_⟩
    change decide (3 ≤ (tag w).val) = true
    apply decide_eq_true_eq.mpr
    by_contra hn
    have hp := kind_positive_only S F t j x w (tag w) (htag w hh) (by omega)
    exact hp.2.1 (Finset.mem_filter.mp hw).2
  · intro hw
    rcases Finset.mem_filter.mp hw with ⟨hh,hg⟩
    have hge : 3 ≤ (tag w).val := by simpa only [isGuard,decide_eq_true_eq] using hg
    have hg' := kind_guard_candidate S F t j x w (tag w) (htag w hh) hge
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨guardLevel (tag w),hg'⟩⟩

theorem card_filter_numbering {A : Type} [Fintype A] (H : Finset V) (e : A ≃ H) (p : V → Prop) :
    ((Finset.univ : Finset A).filter fun a => p (e a).val).card = (H.filter p).card := by
  apply Finset.card_bij (fun a _ => (e a).val)
  · intro a ha
    exact Finset.mem_filter.mpr ⟨(e a).property,(Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ hab
    exact e.injective (Subtype.ext hab)
  · intro w hw
    let wH : H := ⟨w,(Finset.mem_filter.mp hw).1⟩
    refine ⟨e.symm wH,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa only [e.apply_symm_apply] using (Finset.mem_filter.mp hw).2
    · simp only [e.apply_symm_apply,wH]

theorem typeCount_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val) (kind : Kind) :
    ThreeBoundRecordFields.typeCount ts kind = (H.filter fun w => tag w = kind).card := by
  rw [typeCount_eq_card]
  simp_rw [hget]
  convert card_filter_numbering H e (fun w => tag w = kind) using 1 <;>
    congr 1 <;> ext a <;> simp

theorem outCount_transport (ts : List Kind) (H : Finset V) (R : V → V → Prop)
    (hR : TournamentHighRows.IsTournament R) (e : Fin ts.length ≃ H) (w : Fin ts.length) :
    outCount (edges ts.length) (orientationBits (fun k l => R (e k).val (e l).val)) w =
      (H.filter (R (e w).val)).card := by
  have hRE : TournamentHighRows.IsTournament (fun k l => R (e k).val (e l).val) := by
    constructor
    · exact fun k => hR.loopless _
    · intro k l hkl
      exact hR.orient _ _ (fun he => hkl (e.injective (Subtype.ext he)))
  rw [outCount_orientation_eq_card _ hRE]
  exact card_filter_numbering H e (fun v => R (e w).val v)

theorem incoming_transport (ts : List Kind) (H G : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (hG : G = H.filter fun w => isGuard (tag w) = true) (w : Fin ts.length) :
    ThreeBoundRecordFields.incoming ts (orientationBits (fun k l => R (e k).val (e l).val)) w =
      (G.filter fun v => R v (e w).val).card := by
  have hRE : TournamentHighRows.IsTournament (fun k l => R (e k).val (e l).val) := by
    constructor
    · exact fun k => hR.loopless _
    · intro k l hkl
      exact hR.orient _ _ (fun he => hkl (e.injective (Subtype.ext he)))
  rw [incoming_orientation_eq_card _ _ hRE]
  simp_rw [hget]
  rw [hG,Finset.filter_filter]
  convert card_filter_numbering H e (fun v => isGuard (tag v) = true ∧ R v (e w).val) using 1 <;>
    congr 1 <;> ext a <;> simp

theorem histogram_transport (ts : List Kind) (H G : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (hG : G = H.filter fun w => isGuard (tag w) = true) (kind : Kind) (hits : ℕ) :
    histogram ts (orientationBits (fun k l => R (e k).val (e l).val)) kind hits =
      (H.filter fun w => tag w = kind ∧ min 2 (G.filter fun v => R v w).card = hits).card := by
  rw [histogram_eq_card]
  simp_rw [hget,incoming_transport ts H G tag R hR e hget hG]
  convert card_filter_numbering H e
    (fun w => tag w = kind ∧ min 2 (G.filter fun v => R v w).card = hits) using 1 <;>
      congr 1 <;> ext a <;> simp

theorem residual_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) (w : Fin ts.length) :
    _root_.ThreeBoundRecordFields.residual ts (orientationBits (fun k l => R (e k).val (e l).val)) w =
      count (e w).val - (H.filter (R (e w).val)).card := by
  rw [_root_.ThreeBoundRecordFields.residual,hget,outCount_transport ts H R hR e w,← hc (e w).val (e w).property]

theorem external_transport (ts : List Kind) (H G : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (hG : G = H.filter fun w => isGuard (tag w) = true)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) :
    external ts (orientationBits (fun k l => R (e k).val (e l).val)) =
      ∑ w ∈ G, (count w - (H.filter (R w)).card) := by
  rw [external_eq_sum,Finset.sum_filter]
  simp_rw [hget,residual_transport ts H tag R hR e hget count hc]
  rw [e.sum_comp (fun w : H =>
    if isGuard (tag w.val) = true then count w.val-(H.filter (R w.val)).card else 0)]
  rw [Finset.univ_eq_attach]
  rw [Finset.sum_attach H (fun w =>
    if isGuard (tag w) = true then count w-(H.filter (R w)).card else 0)]
  rw [hG,Finset.sum_filter]

theorem numbering_perm (ts : List Kind) (H : Finset V) (e : Fin ts.length ≃ H) :
    ((List.finRange ts.length).map fun k => (e k).val).Perm H.toList := by
  have hinj : Function.Injective (fun k : Fin ts.length => (e k).val) := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  apply (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).map hinj) H.nodup_toList).mpr
  intro w
  constructor
  · rintro hw
    obtain ⟨k,_,he⟩ := List.mem_map.mp hw
    exact Finset.mem_toList.mpr (he ▸ (e k).property)
  · intro hw
    have hwH := Finset.mem_toList.mp hw
    refine List.mem_map.mpr ⟨e.symm ⟨w,hwH⟩,List.mem_finRange _,?_⟩
    simp

theorem sorted_nat_eq_of_perm (xs ys : List ℕ) (h : xs.Perm ys) :
    xs.mergeSort (· ≤ ·) = ys.mergeSort (· ≤ ·) := by
  exact ((List.mergeSort_perm xs (· ≤ ·)).trans
    (h.trans (List.mergeSort_perm ys (· ≤ ·)).symm)).eq_of_pairwise'
    (List.pairwise_mergeSort' (· ≤ ·) xs) (List.pairwise_mergeSort' (· ≤ ·) ys)

theorem sortedResiduals_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) :
    sortedResiduals ts (orientationBits (fun k l => R (e k).val (e l).val)) =
      (H.toList.map fun w => count w-(H.filter (R w)).card).mergeSort (· ≤ ·) := by
  unfold sortedResiduals
  apply sorted_nat_eq_of_perm
  have hp := (numbering_perm ts H e).map (fun w => count w-(H.filter (R w)).card)
  rw [List.map_map] at hp
  have he : ((List.finRange ts.length).map
      (_root_.ThreeBoundRecordFields.residual ts (orientationBits (fun k l => R (e k).val (e l).val)))) =
      ((List.finRange ts.length).map fun k => count (e k).val-(H.filter (R (e k).val)).card) := by
    apply List.map_congr_left
    intro k _
    exact residual_transport ts H tag R hR e hget count hc k
  rw [he]
  exact hp

theorem residualPrefix_transport (ts : List Kind) (H : Finset V) (tag : V → Kind)
    (R : V → V → Prop) (hR : TournamentHighRows.IsTournament R)
    (e : Fin ts.length ≃ H) (hget : ∀ k, ts.get k = tag (e k).val)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) (k : ℕ) (hk : k ≤ H.card) :
    residualPrefix ts (orientationBits (fun a b => R (e a).val (e b).val)) k =
      (((H.toList.map fun w => count w-(H.filter (R w)).card).mergeSort (· ≤ ·)).take k).sum := by
  have hlen : ts.length = H.card := by
    simpa only [Fintype.card_fin,Fintype.card_coe] using Fintype.card_congr e
  rw [residualPrefix,if_pos (by omega),sortedResiduals_transport ts H tag R hR e hget count hc]

/-- All scalar record fields agree exactly with the corresponding actual
    finite-head statistics. The residual prefixes use the same sorted values. -/
theorem all_record_fields (ts : List Kind) (ds : List Bool)
    (H G : Finset V) (tag : V → Kind) (R : V → V → Prop)
    (hR : TournamentHighRows.IsTournament R) (e : Fin ts.length ≃ H)
    (hget : ∀ k, ts.get k = tag (e k).val)
    (hdirs : ds = orientationBits (fun k l => R (e k).val (e l).val))
    (hG : G = H.filter fun w => isGuard (tag w) = true)
    (count : V → ℕ) (hc : ∀ w ∈ H, count w = budget (tag w)) :
    let r := recordOfList (record (ts,ds))
    (∀ kind : Kind, r kind.val = (H.filter fun w => tag w = kind).card) ∧
    r 8 = (∑ w ∈ G, (count w-(H.filter (R w)).card)) ∧
    (∀ (kind : Kind) (hits : Fin 2), r (9+2*kind.val+hits.val) =
      (H.filter fun w => tag w = kind ∧
        min 2 (G.filter fun v => R v w).card = hits.val+1).card) ∧
    (∀ k : Fin 4, k.val+1 ≤ H.card → r (25+k.val) =
      (((H.toList.map fun w => count w-(H.filter (R w)).card).mergeSort (· ≤ ·)).take (k.val+1)).sum) := by
  subst ds
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · intro kind
    rw [record_type]
    exact typeCount_transport ts H tag e hget kind
  · rw [record_external]
    exact external_transport ts H G tag R hR e hget hG count hc
  · intro kind hits
    rw [record_histogram]
    exact histogram_transport ts H G tag R hR e hget hG kind (hits.val+1)
  · intro k hk
    rw [record_prefix]
    exact residualPrefix_transport ts H tag R hR e hget count hc (k.val+1) hk

end
end ThreeBoundActualRecordFields

#print axioms ThreeBoundActualRecordFields.guardSources_eq_filter
#print axioms ThreeBoundActualRecordFields.incoming_transport
#print axioms ThreeBoundActualRecordFields.external_transport
#print axioms ThreeBoundActualRecordFields.all_record_fields


