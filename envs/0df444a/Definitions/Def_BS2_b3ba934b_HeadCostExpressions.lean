-- Prove2me | Definitions.Def_BS2_b3ba934b_HeadCostExpressions
-- name    : BS2_b3ba934b_HeadCostExpressions
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:25:00.145732+00:00
-- url     : https://prove2.me/theorems/e89a362f-b22e-4321-adb3-0c403c47fba4
-- title:
--   Sensitivity separation: HeadCostExpressions (complete source module)
-- statement:
--   Complete Lean source module `HeadCostExpressions` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/HeadCostExpressions.lean; original SHA-256 86dcbb11c5c1af194bcda98ae1161b497e554b8052573bd522fa628f8ee5d7b0; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Interpreting the exact numeric q2 head-cost expressions on actual heads. -/
import Definitions.Def_BS2_b3ba934b_ActualHeadCosts
import Definitions.Def_BS2_b3ba934b_Q2RawExpressions
import Definitions.Def_BS2_b3ba934b_ProfileIntervals

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace ThreeBoundHeadExpressions
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundHeadCharge ThreeBoundGradedCandidates ThreeBoundGradedCover ThreeBoundActualHeadCosts
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem plusExpr_bound_all (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (i j k : Fin n) (hjk : j ≤ k) :
    PBound F i j k ((plusExpr n i.val j.val k.val).eval v) := by
  by_cases hij : i < j
  · exact plusExpr_bound F v hv i j k hij hjk
  · intro x hi hj
    have he := hF j i (le_of_not_gt hij) x hi
    rw [hj] at he
    contradiction

theorem minusExpr_bound_all (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (i j k : Fin n) (hij : i ≤ j) :
    MBound F i j k ((minusExpr n i.val j.val k.val).eval v) := by
  by_cases hjk : j < k
  · exact minusExpr_bound F v hv i j k hij hjk
  · intro x hj hk
    have he := hF k j (le_of_not_gt hjk) x hj
    rw [hk] at he
    contradiction

theorem unionExpr_bound_all (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (v : Profile n) (hv : Upper F v) (i j k l : Fin n) (hij : i ≤ j) (hkl : k ≤ l) :
    DBound F i j k l ((unionExpr n i.val j.val k.val l.val).eval v) := by
  by_cases hjk : j < k
  · exact unionExpr_bound F v hv i j k l hij hjk hkl
  · intro x hj hk
    have he := hF k j (le_of_not_gt hjk) x hj
    rw [hk] at he
    contradiction

theorem positiveCost_cap (a u j incoming : ℕ) :
    positiveCost a u j (min 2 incoming) = positiveCost a u j incoming := by
  unfold positiveCost
  split_ifs <;> omega

theorem overlapCost_cap (a u j incoming : ℕ) :
    overlapCost a u j (min 2 incoming) = overlapCost a u j incoming := by
  unfold overlapCost
  split_ifs <;> omega

theorem guardCost_cap (one two incoming : ℕ) :
    guardCost one two (min 2 incoming) = guardCost one two incoming := by
  unfold guardCost
  split_ifs <;> omega

structure EntryMatch (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) : Prop where
  weakGuard : (S.guard i).val = a.guard
  strongGuard : (S.guard j).val = c.guard
  weakTolerance : S.tolerance i = a.tolerance
  strongTolerance : S.tolerance j = c.tolerance
  weakThreshold : ∀ b, (P.weak b).val = a.threshold b
  strongThreshold : ∀ b, (P.strong b).val = c.threshold b

theorem positive_only_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (w : V)
    (hw : w ∈ highHeads S F P.strong j x)
    (ht : targetAt S F P.strong j x w) (hng : ¬ guardAt S F P.strong j x w)
    (hk : (failed S F j x w).card ≤ 2) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      (headCost n a c (failed S F j x w).card
        (min 2 (incomingSources S F P.strong j x w).card)).eval v := by
  let k := (failed S F j x w).card
  let bar : Fin n := if k=0 then P.weak 0 else min (P.weak k) (P.strong (k-1))
  have hbar : bar ≤ P.strong k := by
    dsimp [bar]
    split_ifs with he
    · simpa only [he] using P.targets k ht.1
    · exact (min_le_left _ _).trans (P.targets k ht.1)
  let ap := (plusExpr n (S.guard j).val bar.val (P.strong k).val).eval v
  let dp := (unionExpr n (S.guard j).val (S.guard i).val bar.val (P.strong k).val).eval v
  let sp := (bExpr n (S.guard j).val (S.guard i).val).eval v
  let jp := (bExpr n (S.guard j).val (P.strong k).val).eval v
  have hp := plusExpr_bound_all F hF v hv (S.guard j) bar (P.strong k) hbar
  have hd := unionExpr_bound_all F hF v hv (S.guard j) (S.guard i) bar (P.strong k) P.guards hbar
  have hs := bExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hb := bExpr_bound F v hv (S.guard j) (P.strong k) (P.guardTarget k ht.1)
  have hbound := positive_only_head_bound S F hF i j P x hoff w hw ht hng ap dp sp jp hp hd hs hb
  have hbarval : bar.val = if k=0 then a.threshold k else min (a.threshold k) (c.threshold (k-1)) := by
    dsimp [bar]
    split_ifs with he
    · simp only [he,matchE.weakThreshold]
    · change min (P.weak k).val (P.strong (k-1)).val = _
      rw [matchE.weakThreshold,matchE.strongThreshold]
  have heq : (headCost n a c k (min 2 (incomingSources S F P.strong j x w).card)).eval v =
      positiveCost ap (min dp (ap+sp)) jp (incomingSources S F P.strong j x w).card := by
    rw [← positiveCost_cap]
    dsimp [headCost]
    rw [if_pos hk]
    simp only [Expr.eval,positiveCost,ap,dp,sp,jp,matchE.weakGuard,matchE.strongGuard,
      matchE.strongThreshold,hbarval]
    split_ifs <;> rfl
  rw [heq]
  exact hbound

theorem overlap_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (w : V)
    (ht : targetAt S F P.strong j x w) (hg : guardAt S F P.strong j x w)
    (hk : 1 ≤ (failed S F j x w).card) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      (headCost n a c ((failed S F j x w).card+5)
        (min 2 (incomingSources S F P.strong j x w).card)).eval v := by
  let k := (failed S F j x w).card
  have hgp : S.guard j ≤ P.strong (k-1) :=
    P.guardTarget (k-1) ((Nat.sub_le _ _).trans ht.1)
  have hws : P.weak k ≤ P.strong k := P.targets k ht.1
  let pp := (plusExpr n (P.strong (k-1)).val (P.weak k).val (P.strong k).val).eval v
  let dp := (unionExpr n (S.guard j).val (P.strong (k-1)).val (P.weak k).val (P.strong k).val).eval v
  let mp := (minusExpr n (S.guard j).val (P.strong (k-1)).val (P.weak k).val).eval v
  let jp := (bExpr n (S.guard j).val (P.strong k).val).eval v
  have hp := plusExpr_bound_all F hF v hv (P.strong (k-1)) (P.weak k) (P.strong k) hws
  have hd := unionExpr_bound_all F hF v hv (S.guard j) (P.strong (k-1))
    (P.weak k) (P.strong k) hgp hws
  have hm := minusExpr_bound_all F hF v hv (S.guard j) (P.strong (k-1)) (P.weak k) hgp
  have hb := bExpr_bound F v hv (S.guard j) (P.strong k) (P.guardTarget k ht.1)
  have hbound := overlap_head_bound S F hF i j P x hoff w ht hg pp dp mp jp hp hd hm hb
  have heq : (headCost n a c (k+5) (min 2 (incomingSources S F P.strong j x w).card)).eval v =
      overlapCost (min pp dp) (min dp (min pp dp+mp)) jp
        (incomingSources S F P.strong j x w).card := by
    rw [← overlapCost_cap]
    dsimp [headCost]
    rw [if_neg (show ¬ k+5 ≤ 5 by dsimp [k] at *; omega)]
    simp only [Nat.add_sub_cancel,overlapCost,pp,dp,mp,jp,
      matchE.strongGuard,matchE.weakThreshold,matchE.strongThreshold]
    split_ifs <;> rfl
  rw [heq]
  exact hbound

theorem pure_lower_guard_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (w : V) (b : ℕ) (hb : b ≤ 2)
    (hbQ : b+1 ≤ S.tolerance j)
    (hg : Q2CandidateTypes.GuardCandidate (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true))
    (hnt : ¬ targetAt S F P.strong j x w) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      (headCost n a c (b+3) (min 2 (incomingSources S F P.strong j x w).card)).eval v := by
  have hgt := P.guardTarget b hg.1
  have hgw : S.guard j ≤ P.weak (b+1) :=
    P.guards.trans (P.weakGuardTarget (b+1) (hbQ.trans P.tolerances))
  let m := (minusExpr n (S.guard j).val (P.strong b).val (P.strong (b+1)).val).eval v
  let low := (minusExpr n (S.guard j).val (P.strong b).val (P.weak (b+1)).val).eval v
  let mid := (minusExpr n (S.guard j).val (P.weak (b+1)).val (P.strong (b+1)).val).eval v
  have hm := minusExpr_bound_all F hF v hv (S.guard j) (P.strong b) (P.strong (b+1)) hgt
  have hl := minusExpr_bound_all F hF v hv (S.guard j) (P.strong b) (P.weak (b+1)) hgt
  have hh := minusExpr_bound_all F hF v hv (S.guard j) (P.weak (b+1)) (P.strong (b+1)) hgw
  have hbound := pure_lower_guard_head_bound S F hF i j P x hoff w b hbQ hg hnt m low mid hm hl hh
  have heq : (headCost n a c (b+3) (min 2 (incomingSources S F P.strong j x w).card)).eval v =
      guardCost (min m (max low mid)) (min (2*m) (max (2*low) (low+mid)))
        (incomingSources S F P.strong j x w).card := by
    rw [← guardCost_cap]
    dsimp [headCost]
    rw [if_pos (show b+3 ≤ 5 by omega)]
    simp only [Nat.add_sub_cancel]
    rw [if_pos (show b < c.tolerance by rw [← matchE.strongTolerance]; omega)]
    simp only [guardCost,m,low,mid,matchE.strongGuard,matchE.weakThreshold,matchE.strongThreshold]
    split_ifs <;> rfl
  rw [heq]
  exact hbound

theorem guardCost_linear (j incoming : ℕ) :
    guardCost j (2*j) incoming = min 2 incoming * j := by
  by_cases h0 : incoming = 0
  · simp [h0,guardCost]
  · by_cases h1 : incoming = 1
    · simp [h1,guardCost]
    · have hmin : min 2 incoming = 2 := by omega
      simp [guardCost,h0,h1,hmin]

theorem pure_top_guard_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (w : V) (b : ℕ) (hb : b ≤ 2) (hbQ : b = S.tolerance j)
    (hg : Q2CandidateTypes.GuardCandidate (fun k z => F (P.strong k) z = true)
      (S.tolerance j) (failed S F j x w).card b (child x w false) (child x w true))
    (hnt : ¬ targetAt S F P.strong j x w) :
    (headBits w (actualHeadParts S F P.strong j x w)).card ≤
      (headCost n a c (b+3) (min 2 (incomingSources S F P.strong j x w).card)).eval v := by
  let q := (bExpr n (S.guard j).val (P.strong b).val).eval v
  have hq := bExpr_bound F v hv (S.guard j) (P.strong b) (P.guardTarget b hg.1)
  have hbound := pure_guard_head_B_bound S F hF i j P x w b hg hnt q hq
  have heq : (headCost n a c (b+3) (min 2 (incomingSources S F P.strong j x w).card)).eval v =
      guardCost q (2*q) (incomingSources S F P.strong j x w).card := by
    rw [guardCost_linear]
    dsimp [headCost]
    rw [if_pos (show b+3 ≤ 5 by omega)]
    simp only [Nat.add_sub_cancel]
    rw [if_neg (show ¬ b < c.tolerance by rw [hbQ,matchE.strongTolerance]; omega)]
    simp only [q,matchE.strongGuard,matchE.strongThreshold]
    split_ifs with he
    · simp only [he,zero_mul,Expr.eval]
    · rfl
  rw [heq]
  exact hbound

end
end ThreeBoundHeadExpressions

#print axioms ThreeBoundHeadExpressions.positive_only_expr_bound
#print axioms ThreeBoundHeadExpressions.overlap_expr_bound
#print axioms ThreeBoundHeadExpressions.pure_lower_guard_expr_bound
#print axioms ThreeBoundHeadExpressions.pure_top_guard_expr_bound


