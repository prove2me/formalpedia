-- Prove2me | Definitions.Def_BS2_b3ba934b_ActualNegativeBound
-- name    : BS2_b3ba934b_ActualNegativeBound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:12:34.913024+00:00
-- url     : https://prove2.me/theorems/54f77db4-97e3-458f-af9d-38d727f0f052
-- title:
--   Sensitivity separation: ActualNegativeBound (complete source module)
-- statement:
--   Complete Lean source module `ActualNegativeBound` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/ActualNegativeBound.lean; original SHA-256 4afbf5cf56d05f9b385717e11ba7ffcaccea8defccc630bd6537c882535bfb00; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_ActualCapPrefix
import Definitions.Def_BS2_b3ba934b_NegativeGreedy
import Definitions.Def_BS2_b3ba934b_NumericOrderBounds
import Definitions.Def_BS2_b3ba934b_HeadCostExpressions

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundActualNegativeBound
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundGradedCandidates
open ThreeBoundGradedCover ThreeBoundActualTargets ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundHeadExpressions ThreeBoundNumericOrder ThreeBoundNegativeGreedy
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

def negativeExpr (n : ℕ) (caps : Caps) (c : Entry) (r : Q2Record) : Expr n :=
  Expr.sum ((List.range (c.tolerance+1)).map fun k =>
    negativeCount caps c.tolerance r k * aExpr n c.guard (c.threshold k))

theorem negativeExpr_eval (caps : Caps) (c : Entry) (r : Q2Record) (v : Profile n) :
    (negativeExpr n caps c r).eval v =
      ((List.range (c.tolerance+1)).map fun k =>
        negativeCount caps c.tolerance r k * (aExpr n c.guard (c.threshold k)).eval v).sum := by
  rw [negativeExpr,Expr.eval_sum,List.map_map]
  rfl

theorem negativeBits_expr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : Entry) (matchE : EntryMatch S F i j P a c)
    (input : ((V × Bool) × I) → Bool) (hQ : S.tolerance j ≤ 2)
    (v : Profile n) (hv : Upper F v) (hordered : Ordered v) (caps : Caps) (r : Q2Record)
    (hprefix : ∀ k, k ≤ S.tolerance j →
      (targetPrefix S F P.strong j input k).card ≤ capPrefix caps r k)
    (hpos : ∀ k, k ≤ S.tolerance j → positivePrefix r k =
      (targetPrefix S F P.strong j input k ∩ highHeads S F P.strong j input).card) :
    (negativeBits S F P.strong j input).card ≤ (negativeExpr n caps c r).eval v := by
  let cost := fun k => (aExpr n c.guard (c.threshold k)).eval v
  let count := fun k => (negativeTier S F P.strong j input k).card
  have hb : ∀ k, k ≤ S.tolerance j → ABound F (S.guard j) (P.strong k) (cost k) := by
    intro k hk
    have h := aExpr_bound F v hv (S.guard j) (P.strong k) (P.guardTarget k hk)
    simpa only [matchE.strongGuard,matchE.strongThreshold,cost] using h
  have hfirst := negativeBits_card_le S F hF i j P input cost hb
  have hp : ∀ k, k ≤ S.tolerance j → (∑ b ∈ Finset.range (k+1), count b) ≤
      capPrefix caps r k-positivePrefix r k := by
    intro k hk
    have h := negative_prefix_after_positive S F P.strong j input k _ (hprefix k hk)
    rw [← hpos k hk] at h
    exact h
  have ha : ∀ k, k+1 ≤ S.tolerance j → cost (k+1) ≤ cost k := by
    intro k hk
    have h := aExpr_antitone_right v hordered (S.guard j) (P.strong k) (P.strong (k+1))
      (P.guardTarget k (by omega)) (P.strongMono (by omega))
    simpa only [matchE.strongGuard,matchE.strongThreshold,cost] using h
  have hsecond := negative_weighted caps r (S.tolerance j) hQ count cost hp ha
  have h := hfirst.trans hsecond
  rw [matchE.strongTolerance] at h
  rw [negativeExpr_eval]
  exact h

end
end ThreeBoundActualNegativeBound

#print axioms ThreeBoundActualNegativeBound.negativeBits_expr_bound


