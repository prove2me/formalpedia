-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualKindFilters
-- name    : BS2_b3ba934b_ActualKindFilters
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:28:32.903977+00:00
-- url     : https://prove2.me/theorems/7d80e31b-f120-45f3-8ce3-e6acc9b3cb44
-- title:
--   Sensitivity separation: ActualKindFilters (complete source module)
-- statement:
--   Complete Lean source module `ActualKindFilters` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualKindFilters.lean; original SHA-256 598b6c51ded9802b69c6a5a16a7156e5bb0257892c4b379809994981b3c297a0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual candidates satisfy every recipe-dependent q2 record filter. -/
import Definitions.Def_BS2_b3ba934b_AllKindHeadCosts

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace ThreeBoundActualKindFilters
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundHeadExpressions ThreeBoundAllKindHeadCosts ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def guardLevel (kind : Fin 8) : ℕ := if kind.val ≤ 5 then kind.val-3 else kind.val-6

theorem kind_guard_candidate
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (t : ℕ → Fin n) (j : Fin n) (x : ((V × Bool) × I) → Bool) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind)
    (hg : 3 ≤ kind.val) :
    Q2CandidateTypes.GuardCandidate (fun k z => F (t k) z = true)
      (S.tolerance j) (failed S F j x w).card (guardLevel kind)
      (child x w false) (child x w true) := by
  fin_cases kind <;> simp only [Q2CandidateTypes.OfKind] at hk
  all_goals norm_num only at hg
  all_goals norm_num [guardLevel]
  all_goals first | exact hk.1 | exact hk | exact hk.2

theorem kind_positive_only
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (t : ℕ → Fin n) (j : Fin n) (x : ((V × Bool) × I) → Bool) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind)
    (hp : kind.val ≤ 2) :
    targetAt S F t j x w ∧ ¬ guardAt S F t j x w ∧ (failed S F j x w).card = kind.val := by
  fin_cases kind <;> simp only [Q2CandidateTypes.OfKind] at hk
  all_goals norm_num only at hp
  · have hc := hk.1.2.1
    refine ⟨target_of_positive S F t j x w 0 hk,?_,hc⟩
    rintro ⟨b,hb⟩
    have hbc := hb.2.1
    omega
  · have hc := hk.1.1.2.1
    refine ⟨target_of_positive S F t j x w 1 hk.1,?_,hc⟩
    rintro ⟨b,hb⟩
    have hbc := hb.2.1
    have he : b = 0 := by omega
    exact hk.2 (he ▸ hb)
  · have hc := hk.1.1.2.1
    refine ⟨target_of_positive S F t j x w 2 hk.1,?_,hc⟩
    rintro ⟨b,hb⟩
    have hbc := hb.2.1
    have he : b = 1 := by omega
    exact hk.2 (he ▸ hb)

theorem actual_kind_tolerance_one
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (t : ℕ → Fin n) (j : Fin n) (x : ((V × Bool) × I) → Bool) (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (t k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind)
    (hQ : S.tolerance j ≤ 1) : kind.val ≠ 2 ∧ kind.val ≠ 5 ∧ kind.val ≠ 7 := by
  fin_cases kind <;> simp only [Q2CandidateTypes.OfKind] at hk <;> norm_num
  · have hh := hk.1.1.1; omega
  · have hh := hk.1; omega
  · have hh := hk.1.1.1; omega

theorem actual_guard_filter
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x = false)
    (w : V) (b : ℕ)
    (hg : Q2CandidateTypes.GuardCandidate (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true)) :
    ¬ (b < a.tolerance ∧ a.threshold (b+1) ≤ c.threshold b) := by
  rintro ⟨hQ,hnext⟩
  apply no_guard_candidate_of_next S F hF i j P x hoff w b hg.2.1 _
    (by rw [matchE.weakTolerance]; omega)
    (by change (P.weak (b+1)).val ≤ (P.strong b).val; simpa only
      [matchE.weakThreshold,matchE.strongThreshold] using hnext)
  intro e
  cases e
  · exact hg.2.2.1
  · exact hg.2.2.2

theorem actual_positive_filter
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (x : ((V × Bool) × I) → Bool) (hoff : parent S F i x = false)
    (w : V) (kind : Fin 8)
    (hk : Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
      (child x w false) (child x w true) kind)
    (hp : kind.val ≤ 2) :
    c.guard ≠ (if kind.val=0 then a.threshold kind.val else
      min (a.threshold kind.val) (c.threshold (kind.val-1))) := by
  obtain ⟨ht,hng,hcount⟩ := kind_positive_only S F P.strong j x w kind hk hp
  have hhigh := Q2CandidateTypes.ofKind_high (fun z => F (S.guard j) z = true)
    (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j x w).card
    (child x w false) (child x w true) kind hk
  have hH : w ∈ highHeads S F P.strong j x :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hhigh⟩
  let k := (failed S F j x w).card
  let barrier : Fin n := if k=0 then P.weak 0 else min (P.weak k) (P.strong (k-1))
  have hfalse : F barrier (child x w (missing S F P.strong j x w)) = false := by
    have hw := target_weak_false S F hF i j P x hoff w ht
    by_cases hz : k=0
    · have hz' : (failed S F j x w).card = 0 := hz
      simpa [barrier,hz,hz'] using hw
    · have hprev := positive_only_previous_false S F hF i j P x w ht hng
        (Nat.pos_of_ne_zero hz)
      dsimp [barrier]
      rw [if_neg hz]
      rcases le_total (P.weak k) (P.strong (k-1)) with hh | hh
      · simpa only [min_eq_left hh] using hw
      · simpa only [min_eq_right hh] using hprev
  have htrue := high_guards_true S F hF i j P x w hH (missing S F P.strong j x w)
  have hval : barrier.val = if kind.val=0 then a.threshold kind.val else
      min (a.threshold kind.val) (c.threshold (kind.val-1)) := by
    dsimp [barrier]
    by_cases hz : k=0
    · have hk0 : kind.val=0 := by dsimp [k] at hz; omega
      simp [hz,hk0,matchE.weakThreshold]
    · have hk0 : kind.val≠0 := by dsimp [k] at hz; omega
      rw [if_neg hz,if_neg hk0]
      change min (P.weak k).val (P.strong (k-1)).val = _
      simp only [matchE.weakThreshold,matchE.strongThreshold,k,hcount]
  intro he
  have eqb : S.guard j = barrier := Fin.ext (matchE.strongGuard.trans (he.trans hval.symm))
  rw [eqb,hfalse] at htrue
  contradiction

end
end ThreeBoundActualKindFilters

#print axioms ThreeBoundActualKindFilters.actual_guard_filter
#print axioms ThreeBoundActualKindFilters.actual_positive_filter
#print axioms ThreeBoundActualKindFilters.actual_kind_tolerance_one


