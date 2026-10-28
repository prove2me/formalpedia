-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxRecordCaps
-- name    : BS2_b3ba934b_MinmaxRecordCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:41:57.301944+00:00
-- url     : https://prove2.me/theorems/860d3542-e0fc-475a-813f-f727446ba1b1
-- title:
--   Sensitivity separation: MinmaxRecordCaps (complete source module)
-- statement:
--   Complete Lean source module `MinmaxRecordCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxRecordCaps.lean; original SHA-256 40463f086533f2269029ddf96406b34e7f8d91536058b3ab561691e9f2f0816e; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Numeric prefix-cap routine interpreted for actual min/max target candidates. -/
import Definitions.Def_BS2_b3ba934b_MinmaxQ2Types
import Definitions.Def_BS2_b3ba934b_ActualCapPrefix

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxQ2
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCaps
open ThreeBoundActualCaps (CapsSound)
open ThreeBoundNumeric ThreeBoundCapAlgorithm ThreeBoundRecordCaps ThreeBoundAccounting
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem actual_capPrefix (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (input : ((V × Bool) × I) → Bool)
    (hQ : S.tolerance j ≤ 2) (tag : V → Fin 8)
    (hk : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      ThreeBoundHighTypes.OfKind 2
        (PositiveCandidate S F P.strongLower P.strongUpper j input w)
        (GuardCandidate S F P.strongLower P.strongUpper j input w) (tag w))
    (hc : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      (failed S F j input w).card = ThreeBoundQ2.budget (tag w))
    (caps : Caps) (hcap : CapsSound S.Adj S.label caps) (r : Q2Record)
    (hx : ∀ k : Fin 8, r k.val = typeCount (highHeads S F P.strongLower P.strongUpper j input) tag k)
    (hrs : ∀ k : Fin 4, k.val+1 ≤ (highHeads S F P.strongLower P.strongUpper j input).card →
      r (25+k.val) = residualPrefix S F P.strongLower P.strongUpper j input (k.val+1))
    (q : ℕ) (hq : q ≤ 2) :
    (targetPrefix S F P.strongLower P.strongUpper j input q).card ≤ capPrefix caps r q := by
  let H := highHeads S F P.strongLower P.strongUpper j input
  let T := targetPrefix S F P.strongLower P.strongUpper j input q
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
      (targetPrefix S F P.strongLower P.strongUpper j input b ∩ H).card := by
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
end ThreeBoundMinmaxQ2

#print axioms ThreeBoundMinmaxQ2.actual_capPrefix


