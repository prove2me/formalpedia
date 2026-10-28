-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualHeadCosts
-- name    : BS2_b3ba934b_ActualHeadCosts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:23:17.709416+00:00
-- url     : https://prove2.me/theorems/cb216c6b-2e21-42fe-9e1c-6acb367b05fa
-- title:
--   Sensitivity separation: ActualHeadCosts (complete source module)
-- statement:
--   Complete Lean source module `ActualHeadCosts` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualHeadCosts.lean; original SHA-256 a66d58d8ea25978ac8f19433350b0fb930a74053dcbb642a8fdac2b6ddf28781; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact head-cost formulas instantiated from actual graded candidate states. -/
import Definitions.Def_BS2_b3ba934b_GradedGlobalCover

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace ThreeBoundActualHeadCosts
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover
open scoped Classical BigOperators
noncomputable section
variable {L I V : Type} [LinearOrder L] [Fintype I] [Fintype V]
variable (S : Stage L I V) (F : L → (I → Bool) → Bool) (hF : Nested F)
  (i j : L) (P : PairData S F i j) (x : ((V × Bool) × I) → Bool)
include hF P

theorem high_guards_true (w : V) (hw : w ∈ highHeads S F P.strong j x) (c : Bool) :
    F (S.guard j) (child x w c) = true := by
  have hh := Q2CandidateTypes.high_guard_true (fun z => F (S.guard j) z = true)
    (fun b z => F (P.strong b) z = true) (S.tolerance j) (failed S F j x w).card
    (child x w false) (child x w true)
    (fun b hb z hz => hF _ _ (P.guardTarget b hb) z hz) (Finset.mem_filter.mp hw).2
  cases c
  · exact hh.1
  · exact hh.2

theorem target_parts_eq (w : V) (hw : targetAt S F P.strong j x w) :
    actualHeadParts S F P.strong j x w =
      positiveParts F (S.guard j) (P.strong (failed S F j x w).card)
        (child x w) (missing S F P.strong j x w) (hitChildren S F P.strong j x w) := by
  funext c
  simp only [actualHeadParts,positiveParts,hw,true_and]

theorem guard_parts_eq (w : V) (hw : ¬ targetAt S F P.strong j x w) :
    actualHeadParts S F P.strong j x w =
      guardParts F (S.guard j) (child x w) (hitChildren S F P.strong j x w) := by
  funext c
  simp only [actualHeadParts,guardParts,hw,false_and,if_false,Finset.empty_union]

theorem negative_guard_false (w : V) (hw : w ∈ negativeTargets S F P.strong j x) :
    F (S.guard j) (child x w (missing S F P.strong j x w)) = false := by
  rcases (Finset.mem_filter.mp hw).2 with ⟨ht,hn⟩
  have hpartner := (target_missing S F P.strong j x w ht).2
  have hpg := hF _ _ (P.guardTarget _ ht.1) _ hpartner
  cases hg : F (S.guard j) (child x w (missing S F P.strong j x w)) with
  | false => rfl
  | true =>
      apply False.elim
      apply hn
      left
      refine ⟨(failed S F j x w).card,ht,?_⟩
      cases hm : missing S F P.strong j x w <;> simp_all

theorem guard_source_weak_eligibility (hoff : parent S F i x = false)
    (v : V) (hv : v ∈ guardSources S F P.strong j x)
    (w : V) (hw : w ∈ failed S F j x v) :
    F (S.guard i) (child x w (S.label v w)) = true := by
  obtain ⟨b,hb⟩ := (Finset.mem_filter.mp hv).2
  apply ThreeBoundGradedCandidates.guard_hit_eligible S F hF i j P x hoff v b
    hb.1 hb.2.1 _ w hw
  intro c
  cases c
  · exact hb.2.2.1
  · exact hb.2.2.2

theorem hit_weak_eligibility (hoff : parent S F i x = false)
    (w : V) (hw : w ∈ highHeads S F P.strong j x)
    (c : Bool) (hc : c ∈ hitChildren S F P.strong j x w) :
    F (S.guard i) (child x w c) = true := by
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hc
  rcases Finset.mem_filter.mp hv with ⟨hsource,hR⟩
  have hfailed : w ∈ failed S F j x v :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR,
      high_guards_true S F hF i j P x w hw (S.label v w)⟩
  simpa only [he] using guard_source_weak_eligibility S F hF i j P x hoff v hsource w hfailed

theorem target_weak_false (hoff : parent S F i x = false)
    (w : V) (hw : targetAt S F P.strong j x w) :
    F (P.weak (failed S F j x w).card)
      (child x w (missing S F P.strong j x w)) = false := by
  exact target_missing_weak_false S F hF i j P x hoff w _ _ hw.1 rfl
    (target_missing S F P.strong j x w hw).2

theorem positive_only_previous_false (w : V)
    (hw : targetAt S F P.strong j x w) (hng : ¬ guardAt S F P.strong j x w)
    (hpos : 0 < (failed S F j x w).card) :
    F (P.strong ((failed S F j x w).card-1))
      (child x w (missing S F P.strong j x w)) = false := by
  let d := (failed S F j x w).card
  have hp := (target_missing S F P.strong j x w hw).2
  have hprev := hF _ _ (P.strongMono (Nat.sub_le d 1)) _ hp
  cases hf : F (P.strong (d-1)) (child x w (missing S F P.strong j x w)) with
  | false => rfl
  | true =>
      apply False.elim
      apply hng
      refine ⟨d-1,⟨(Nat.sub_le d 1).trans hw.1,by dsimp [d] at *; omega,?_⟩⟩
      cases hm : missing S F P.strong j x w <;> simp_all

/-- An actual positive-only candidate has the barrier used in the exact oracle. -/
theorem positive_only_head_bound
    (hoff : parent S F i x = false) (w : V)
    (hw : w ∈ highHeads S F P.strong j x)
    (ht : targetAt S F P.strong j x w) (hng : ¬ guardAt S F P.strong j x w)
    (a d s q : ℕ)
    (hp : PBound F (S.guard j)
      (if (failed S F j x w).card = 0 then P.weak 0 else
        min (P.weak (failed S F j x w).card) (P.strong ((failed S F j x w).card-1)))
      (P.strong (failed S F j x w).card) a)
    (hd : DBound F (S.guard j) (S.guard i)
      (if (failed S F j x w).card = 0 then P.weak 0 else
        min (P.weak (failed S F j x w).card) (P.strong ((failed S F j x w).card-1)))
      (P.strong (failed S F j x w).card) d)
    (hs : BBound F (S.guard j) (S.guard i) s)
    (hb : BBound F (S.guard j) (P.strong (failed S F j x w).card) q) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      positiveCost a (min d (a+s)) q (incomingSources S F P.strong j x w).card := by
  rw [target_parts_eq S F hF i j P x w ht]
  apply positive_head_cost_min F (S.guard j) (S.guard i) _ _ (child x w)
    (missing S F P.strong j x w) _ w a d s q _ hp hd hs hb
    (high_guards_true S F hF i j P x w hw _) _
    (target_missing S F P.strong j x w ht).2
    (hit_weak_eligibility S F hF i j P x hoff w hw)
    (hitChildren_card_le S F P.strong j x w)
  have hweak := target_weak_false S F hF i j P x hoff w ht
  by_cases hzero : (failed S F j x w).card = 0
  · simpa [hzero] using hweak
  · rw [if_neg hzero]
    have hprev := positive_only_previous_false S F hF i j P x w ht hng (Nat.pos_of_ne_zero hzero)
    rcases le_total (P.weak (failed S F j x w).card)
      (P.strong ((failed S F j x w).card-1)) with hh | hh
    · simpa only [min_eq_left hh] using hweak
    · simpa only [min_eq_right hh] using hprev

theorem overlap_previous_true (w : V) (hg : guardAt S F P.strong j x w) :
    ∀ c, F (P.strong ((failed S F j x w).card-1)) (child x w c) = true := by
  obtain ⟨b,hb⟩ := hg
  have hc := hb.2.1
  have he : (failed S F j x w).card-1 = b := by omega
  rw [he]
  intro c
  cases c
  · exact hb.2.2.1
  · exact hb.2.2.2

theorem overlap_head_bound (hoff : parent S F i x = false) (w : V)
    (ht : targetAt S F P.strong j x w) (hg : guardAt S F P.strong j x w)
    (p d m q : ℕ)
    (hp : PBound F (P.strong ((failed S F j x w).card-1))
      (P.weak (failed S F j x w).card) (P.strong (failed S F j x w).card) p)
    (hd : DBound F (S.guard j) (P.strong ((failed S F j x w).card-1))
      (P.weak (failed S F j x w).card) (P.strong (failed S F j x w).card) d)
    (hm : MBound F (S.guard j) (P.strong ((failed S F j x w).card-1))
      (P.weak (failed S F j x w).card) m)
    (hb : BBound F (S.guard j) (P.strong (failed S F j x w).card) q) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      overlapCost (min p d) (min d (min p d+m)) q
        (incomingSources S F P.strong j x w).card := by
  rw [target_parts_eq S F hF i j P x w ht]
  exact overlap_head_cost F (S.guard j) _ _ _ (child x w) _ _ w p d m q _ hp hd hm hb
    (overlap_previous_true S F hF i j P x w hg _)
    (target_weak_false S F hF i j P x hoff w ht)
    (target_missing S F P.strong j x w ht).2
    (hitChildren_card_le S F P.strong j x w)

theorem pure_guard_strong_next_false (hoff : parent S F i x = false)
    (w : V) (b : ℕ) (hbQ : b+1 ≤ S.tolerance j)
    (hg : Q2CandidateTypes.GuardCandidate (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true))
    (hnt : ¬ targetAt S F P.strong j x w) :
    ∀ c, F (P.strong (b+1)) (child x w c) = false := by
  have hstrongoff := strong_false_of_weak_false S F hF i j P x hoff
  have hno : ¬ Q2CandidateTypes.Accepted (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card (child x w false) (child x w true) := by
    rintro ⟨hQ,h0,h1⟩
    have he : parent S F j x = true := (parent_true_iff S F j x).2
      ⟨w,hQ,by rw [P.strongDef]; simp only [h0,h1,Bool.and_self]⟩
    rw [hstrongoff] at he
    contradiction
  have hnp : ¬ Q2CandidateTypes.PositiveCandidate (fun z => F (S.guard j) z = true)
      (fun k z => F (P.strong k) z = true) (S.tolerance j)
      (failed S F j x w).card (b+1) (child x w false) (child x w true) := by
    intro h
    apply hnt
    have he := h.1.2.1
    simpa only [targetAt,he] using h.1
  have hfalse := Q2CandidateTypes.pure_guard_next_both_false
    (fun z => F (S.guard j) z = true) (fun k z => F (P.strong k) z = true)
    (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true)
    hbQ (fun k hk z hz => hF _ _ (P.guardTarget k hk) z hz) hg hnp hno
  intro c
  cases c
  · exact Bool.eq_false_iff.mpr hfalse.1
  · exact Bool.eq_false_iff.mpr hfalse.2

/-- All intervals in the pure lower G head formula are forced by actual weak
    rejection and by exclusion of the overlapping target candidate. -/
theorem pure_lower_guard_head_bound (hoff : parent S F i x = false)
    (w : V) (b : ℕ) (hbQ : b+1 ≤ S.tolerance j)
    (hg : Q2CandidateTypes.GuardCandidate (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true))
    (hnt : ¬ targetAt S F P.strong j x w)
    (m low mid : ℕ)
    (hm : MBound F (S.guard j) (P.strong b) (P.strong (b+1)) m)
    (hl : MBound F (S.guard j) (P.strong b) (P.weak (b+1)) low)
    (hh : MBound F (S.guard j) (P.weak (b+1)) (P.strong (b+1)) mid) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      guardCost (min m (max low mid)) (min (2*m) (max (2*low) (low+mid)))
        (incomingSources S F P.strong j x w).card := by
  rw [guard_parts_eq S F hF i j P x w hnt]
  apply lower_guard_head_cost F (S.guard j) (P.strong b) (P.weak (b+1))
    (P.strong (b+1)) (child x w) _ w m low mid _ hm hl hh _
    (pure_guard_strong_next_false S F hF i j P x hoff w b hbQ hg hnt)
    (guard_next_weak_false S F hF i j P x hoff w b hg.2.1 (hbQ.trans P.tolerances))
    (hitChildren_card_le S F P.strong j x w)
  intro c
  cases c
  · exact hg.2.2.1
  · exact hg.2.2.2

theorem pure_guard_head_B_bound (w : V) (b : ℕ)
    (hg : Q2CandidateTypes.GuardCandidate (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true))
    (hnt : ¬ targetAt S F P.strong j x w) (q : ℕ)
    (hb : BBound F (S.guard j) (P.strong b) q) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      guardCost q (2*q) (incomingSources S F P.strong j x w).card := by
  rw [guard_parts_eq S F hF i j P x w hnt]
  apply top_guard_head_cost F (S.guard j) (P.strong b) (child x w) _ w q _ hb _
    (hitChildren_card_le S F P.strong j x w)
  intro c
  cases c
  · exact hg.2.2.1
  · exact hg.2.2.2

end
end ThreeBoundActualHeadCosts

#print axioms ThreeBoundActualHeadCosts.positive_only_head_bound
#print axioms ThreeBoundActualHeadCosts.overlap_head_bound
#print axioms ThreeBoundActualHeadCosts.guard_source_weak_eligibility
#print axioms ThreeBoundActualHeadCosts.pure_lower_guard_head_bound
#print axioms ThreeBoundActualHeadCosts.pure_guard_head_B_bound


