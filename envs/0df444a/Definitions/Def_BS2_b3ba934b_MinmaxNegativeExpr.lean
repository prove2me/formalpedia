-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxNegativeExpr
-- name    : BS2_b3ba934b_MinmaxNegativeExpr
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:45:58.884584+00:00
-- url     : https://prove2.me/theorems/c98d7ced-909d-46f1-ae60-bcddb681071a
-- title:
--   Sensitivity separation: MinmaxNegativeExpr (complete source module)
-- statement:
--   Complete Lean source module `MinmaxNegativeExpr` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxNegativeExpr.lean; original SHA-256 7b02d4be20c85b5b32bceca91d83ef9faad009d63203e8a67e42868e6805d003; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The exact greedy negative contribution bounds every actual min/max input. -/
import Definitions.Def_BS2_b3ba934b_MinmaxNegative

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxA
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundNumericOrder ThreeBoundNegativeGreedy
open ThreeBoundMinmaxNumeric (EntryMatch)
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem negativeExpr_eval (caps : Caps) (c : ThreeBoundMinmaxNumeric.Entry)
    (r : Q2Record) (v : Profile n) :
    (negativeExpr n caps c r).eval v =
      ((List.range (c.tolerance+1)).map fun k =>
        negativeCount caps c.tolerance r k * (aExpr n c.guard (c.lowerAt k)).eval v).sum := by
  rw [negativeExpr,Expr.eval_sum,List.map_map]
  rfl

theorem negativeBits_expr_bound (S : Stage (Fin n) I V)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry)
    (hm : EntryMatch S F i j P a c)
    (input : ((V × Bool) × I) → Bool) (hQ : S.tolerance j ≤ 2)
    (v : Profile n) (hv : Upper F v) (hordered : Ordered v) (caps : Caps) (r : Q2Record)
    (hprefix : ∀ k, k ≤ S.tolerance j →
      (targetPrefix S F P.strongLower P.strongUpper j input k).card ≤ capPrefix caps r k)
    (hpos : ∀ k, k ≤ S.tolerance j → positivePrefix r k =
      (targetPrefix S F P.strongLower P.strongUpper j input k ∩
        highHeads S F P.strongLower P.strongUpper j input).card) :
    (negativeBits S F P.strongLower P.strongUpper j input).card ≤
      (negativeExpr n caps c r).eval v := by
  let cost := fun k => (aExpr n c.guard (c.lowerAt k)).eval v
  let count := fun k => (negativeTier S F P.strongLower P.strongUpper j input k).card
  have hb : ∀ k, k ≤ S.tolerance j → ABound F (S.guard j) (P.strongLower k) (cost k) := by
    intro k hk
    have h := aExpr_bound F v hv (S.guard j) (P.strongLower k) (P.guardTarget k hk)
    simpa only [hm.strongGuard,hm.strongLower k hk,cost] using h
  have hfirst := negativeBits_card_le S F hF i j P input cost hb
  have hp : ∀ k, k ≤ S.tolerance j → (∑ b ∈ Finset.range (k+1), count b) ≤
      capPrefix caps r k-positivePrefix r k := by
    intro k hk
    have h := negative_prefix_after_positive S F P.strongLower P.strongUpper j input k _ (hprefix k hk)
    rw [← hpos k hk] at h
    exact h
  have ha : ∀ k, k+1 ≤ S.tolerance j → cost (k+1) ≤ cost k := by
    intro k hk
    have hk' : k ≤ S.tolerance j := by omega
    have h := aExpr_antitone_right v hordered (S.guard j) (P.strongLower k) (P.strongLower (k+1))
      (P.guardTarget k hk') (P.strongLowerMono (by omega))
    simpa only [hm.strongGuard,hm.strongLower k hk',hm.strongLower (k+1) hk,cost] using h
  have hsecond := negative_weighted caps r (S.tolerance j) hQ count cost hp ha
  have h := hfirst.trans hsecond
  rw [hm.strongTolerance] at h
  rw [negativeExpr_eval]
  exact h

end
end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.negativeBits_expr_bound


