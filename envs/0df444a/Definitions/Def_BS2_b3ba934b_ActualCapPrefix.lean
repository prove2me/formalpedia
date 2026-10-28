-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualCapPrefix
-- name    : BS2_b3ba934b_ActualCapPrefix
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:06:32.979998+00:00
-- url     : https://prove2.me/theorems/a2ba23bd-0b03-4274-af4b-b02e4ae917e5
-- title:
--   Sensitivity separation: ActualCapPrefix (complete source module)
-- statement:
--   Complete Lean source module `ActualCapPrefix` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualCapPrefix.lean; original SHA-256 54a31c537548cc4ea9f8b1fbb7d176c8c76303c01efa8aa278e4c25202486d62; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- All numerical prefix constraints hold for the actual candidate record. -/
import Definitions.Def_BS2_b3ba934b_RecordCapStats
import Definitions.Def_BS2_b3ba934b_ActualResidualCaps

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundActualCaps
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualHeadCosts ThreeBoundActualEnumeration
open ThreeBoundActualTargets ThreeBoundActualResidualCaps ThreeBoundTagPrefixes
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundRecordCaps ThreeBoundAccounting
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

/-- The combinatorial exclusions used by the numerical q2 prefix routine. -/
structure CapsSound (R : V → V → Prop) (ell : V → V → Bool) (caps : Caps) : Prop where
  ordinary : ∀ q, q ≤ 2 → CandidateCoherence.NoOrdinary R ell q (Caps.at caps.ordinary q)
  source : ResidualCaps.DominatorCardBound R ell 1 (caps.pcross+1)
  double : ResidualCaps.DominatorCardBound R ell 2 (Caps.at caps.zero 2+1)
  markedOne : ∀ q, 1 ≤ q → q ≤ 2 →
    ResidualCaps.MarkedCardBound R ell q 1 (q+1) (Caps.at caps.marked (q-1))
  markedTwo : ∀ q, 1 ≤ q → q ≤ 2 →
    ResidualCaps.MarkedCardBound R ell q 2 (2*(q+1))
      (Caps.at caps.marked (if q=1 then 4 else 5))
  zeroThree : ResidualCaps.MarkedCardBound R ell 1 3 0 (Caps.at caps.marked 6)
  zeroFour : ResidualCaps.MarkedCardBound R ell 2 4 0 (Caps.at caps.marked 7)
  zeroThree_pos : 1 ≤ Caps.at caps.marked 6
  zeroFour_pos : 1 ≤ Caps.at caps.marked 7

theorem actual_capPrefix (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (input : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strong j input,
      Q2CandidateTypes.OfKind (fun z => F (S.guard j) z = true)
        (fun k z => F (P.strong k) z = true) (S.tolerance j) (failed S F j input w).card
        (child input w false) (child input w true) (tag w))
    (hc : ∀ w ∈ highHeads S F P.strong j input,
      (failed S F j input w).card = ThreeBoundQ2.budget (tag w))
    (caps : Caps) (hcap : CapsSound S.Adj S.label caps) (r : Q2Record)
    (hx : ∀ k : Fin 8, r k.val = typeCount (highHeads S F P.strong j input) tag k)
    (hrs : ∀ k : Fin 4, k.val+1 ≤ (highHeads S F P.strong j input).card →
      r (25+k.val) = residualPrefix S F P.strong j input (k.val+1))
    (q : ℕ) (hq : q ≤ 2) :
    (targetPrefix S F P.strong j input q).card ≤ capPrefix caps r q := by
  let H := highHeads S F P.strong j input
  let T := targetPrefix S F P.strong j input q
  have hhead : headCount r = H.card := headCount_card H tag r hx
  have hlow : lowCount r q = ((H \ T).filter fun w => (failed S F j input w).card ≤ q).card := by
    exact (lowCount_card H tag r hx q).trans
      (congrArg Finset.card (outside_high_eq S F hF i j P input hQ tag hk q q).symm)
  have hnext : nextCount r q = ((H \ T).filter fun w => (failed S F j input w).card ≤ q+1).card := by
    exact (nextCount_card H tag r hx q).trans
      (congrArg Finset.card (outside_high_eq S F hF i j P input hQ tag hk q (q+1)).symm)
  have helig : eligibleCount r q = (H.filter fun w => (failed S F j input w).card ≤ q+1).card := by
    refine (eligibleCount_card H tag r hx q).trans ?_
    congr 1
    ext w
    simp only [Finset.mem_filter]
    by_cases hw : w ∈ H
    · simp only [hw,true_and,hc w hw]
    · simp [hw]
  have hpos (b : ℕ) (hb : b ≤ 2) : positivePrefix r b =
      (targetPrefix S F P.strong j input b ∩ H).card := by
    exact (positivePrefix_card H tag r hx b hb).trans
      (congrArg Finset.card (prefix_high_eq S F hF i j P input hQ tag hk b).symm)
  apply capPrefix_bound
  · rw [hlow,hnext]
    exact actual_ordinary_prefix_cap S hR F hF i j P input q _ (hcap.ordinary q hq)
  · intro hq0 hm
    subst q
    rw [hhead] at hm
    have h := actual_dominator_prefix_cap S hR F hF i j P input 1 (caps.pcross+1) hm hcap.source
    rw [← hpos 0 (by omega),← hrs ⟨0,by omega⟩ hm] at h
    simpa [positivePrefix,positiveCount] using h
  · intro hq0 hm
    subst q
    rw [hhead] at hm
    have h := actual_dominator_prefix_cap S hR F hF i j P input 2 (Caps.at caps.zero 2+1) hm hcap.double
    rw [← hpos 0 (by omega),← hrs ⟨1,by omega⟩ hm] at h
    simpa [positivePrefix,positiveCount] using h
  · intro hq0 hm
    rw [helig] at hm
    rw [hnext]
    exact actual_marked_prefix_cap S F hF i j P input q 1 _ hm
      (by simpa using hcap.markedOne q (by omega) hq)
  · intro hq0 hm
    rw [helig] at hm
    rw [hnext]
    exact actual_marked_prefix_cap S F hF i j P input q 2 _ hm
      (hcap.markedTwo q (by omega) hq)
  · intro hq1 hm
    subst q
    rw [hhead] at hm
    have h := actual_zero_marked_prefix_cap S hR F hF i j P input 1 3 _ hm (by omega) hcap.zeroThree
    rw [← hpos 1 (by omega),← hrs ⟨2,by omega⟩ hm] at h
    have hp := hcap.zeroThree_pos
    change _ ≤ _ + _ - 1 + r 27
    norm_num only [Fin.val_mk] at h
    omega
  · intro hq2 hm
    subst q
    rw [hhead] at hm
    have h := actual_zero_marked_prefix_cap S hR F hF i j P input 2 4 _ hm (by omega) hcap.zeroFour
    rw [← hpos 2 (by omega),← hrs ⟨3,by omega⟩ hm] at h
    have hp := hcap.zeroFour_pos
    change _ ≤ _ + _ - 1 + r 28
    norm_num only [Fin.val_mk] at h
    omega

end
end ThreeBoundActualCaps

#print axioms ThreeBoundActualCaps.actual_capPrefix


