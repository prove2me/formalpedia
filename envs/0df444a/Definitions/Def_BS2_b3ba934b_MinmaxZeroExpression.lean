-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxZeroExpression
-- name    : BS2_b3ba934b_MinmaxZeroExpression
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:53:32.05611+00:00
-- url     : https://prove2.me/theorems/b2bda9ce-7485-4772-8c86-b2385f4cbb95
-- title:
--   Sensitivity separation: MinmaxZeroExpression (complete source module)
-- statement:
--   Complete Lean source module `MinmaxZeroExpression` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxZeroExpression.lean; original SHA-256 079b2ea35da0d77f4afadd2ee676bc1d175f4da1d0679d4f23f6ef2a0d0b3a29; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact numeric expression adapter for the strict min/max zero-tolerance theorem. -/
import Definitions.Def_BS2_b3ba934b_MinmaxZeroBound
import Definitions.Def_BS2_b3ba934b_MinmaxEntryMatch
import Definitions.Def_BS2_b3ba934b_MinmaxAExpressions
import Definitions.Def_BS2_b3ba934b_HeadCostExpressions

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

namespace ThreeBoundMinmaxZeroExpression
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxZeroSets
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

noncomputable def numericCosts
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (a c : ThreeBoundMinmaxNumeric.Entry) (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) : Costs S F i j P where
  a := (plusExpr n c.guard (a.lowerAt 0) (c.lowerAt 0)).eval v
  au := (plusExpr n c.guard (a.upperAt 0) (c.upperAt 0)).eval v
  a2 := (plusExpr n (c.lowerAt 0) (a.upperAt 0) (c.upperAt 0)).eval v
  b := (aExpr n c.guard (c.lowerAt 0)).eval v
  bu := (aExpr n c.guard (c.upperAt 0)).eval v
  s := (bExpr n c.guard a.guard).eval v
  jc := (bExpr n c.guard (c.lowerAt 0)).eval v
  ju := (bExpr n c.guard (c.upperAt 0)).eval v
  d := (unionExpr n c.guard a.guard (a.lowerAt 0) (c.lowerAt 0)).eval v
  du := (unionExpr n c.guard a.guard (a.upperAt 0) (c.upperAt 0)).eval v
  d2 := (unionExpr n c.guard (c.lowerAt 0) (a.upperAt 0) (c.upperAt 0)).eval v
  ha := by
    simpa only [hm.strongGuard,hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _)] using
      plusExpr_bound_all F hF v hv (S.guard j) (P.weakLower 0) (P.strongLower 0) (P.lowerOrder 0 (Nat.zero_le _))
  hau := by
    simpa only [hm.strongGuard,hm.weakUpper 0 (Nat.zero_le _),hm.strongUpper 0 (Nat.zero_le _)] using
      plusExpr_bound_all F hF v hv (S.guard j) (P.weakUpper 0) (P.strongUpper 0) (P.upperOrder 0 (Nat.zero_le _))
  ha2 := by
    simpa only [hm.strongLower 0 (Nat.zero_le _),hm.weakUpper 0 (Nat.zero_le _),hm.strongUpper 0 (Nat.zero_le _)] using
      plusExpr_bound_all F hF v hv (P.strongLower 0) (P.weakUpper 0) (P.strongUpper 0) (P.upperOrder 0 (Nat.zero_le _))
  hb := by
    simpa only [hm.strongGuard,hm.strongLower 0 (Nat.zero_le _)] using
      aExpr_bound F v hv (S.guard j) (P.strongLower 0) (P.guardTarget 0 (Nat.zero_le _))
  hbu := by
    simpa only [hm.strongGuard,hm.strongUpper 0 (Nat.zero_le _)] using
      aExpr_bound F v hv (S.guard j) (P.strongUpper 0)
        ((P.guardTarget 0 (Nat.zero_le _)).trans (P.strongLowerUpper 0 (Nat.zero_le _)))
  hs := by
    simpa only [hm.strongGuard,hm.weakGuard] using bExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  hj := by
    simpa only [hm.strongGuard,hm.strongLower 0 (Nat.zero_le _)] using
      bExpr_bound F v hv (S.guard j) (P.strongLower 0) (P.guardTarget 0 (Nat.zero_le _))
  hju := by
    simpa only [hm.strongGuard,hm.strongUpper 0 (Nat.zero_le _)] using
      bExpr_bound F v hv (S.guard j) (P.strongUpper 0)
        ((P.guardTarget 0 (Nat.zero_le _)).trans (P.strongLowerUpper 0 (Nat.zero_le _)))
  hd := by
    simpa only [hm.strongGuard,hm.weakGuard,hm.weakLower 0 (Nat.zero_le _),hm.strongLower 0 (Nat.zero_le _)] using
      unionExpr_bound_all F hF v hv (S.guard j) (S.guard i) (P.weakLower 0) (P.strongLower 0)
        P.guards (P.lowerOrder 0 (Nat.zero_le _))
  hdu := by
    simpa only [hm.strongGuard,hm.weakGuard,hm.weakUpper 0 (Nat.zero_le _),hm.strongUpper 0 (Nat.zero_le _)] using
      unionExpr_bound_all F hF v hv (S.guard j) (S.guard i) (P.weakUpper 0) (P.strongUpper 0)
        P.guards (P.upperOrder 0 (Nat.zero_le _))
  hd2 := by
    simpa only [hm.strongGuard,hm.strongLower 0 (Nat.zero_le _),hm.weakUpper 0 (Nat.zero_le _),hm.strongUpper 0 (Nat.zero_le _)] using
      unionExpr_bound_all F hF v hv (S.guard j) (P.strongLower 0) (P.weakUpper 0) (P.strongUpper 0)
        (P.guardTarget 0 (Nat.zero_le _)) (P.upperOrder 0 (Nat.zero_le _))

def ZeroCapsMatch (caps : Caps) : Prop :=
  Caps.at caps.zero 0=22 ∧ Caps.at caps.zero 1=19 ∧ Caps.at caps.zero 2=17 ∧
    Caps.at caps.zero 3=19 ∧ Caps.at caps.zero 5=17 ∧ Caps.at caps.zero 7=17

theorem zeroAExpr_eval
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (a c : ThreeBoundMinmaxNumeric.Entry) (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (caps : Caps) (hcap : ZeroCapsMatch caps) :
    (ThreeBoundMinmaxA.zeroAExpr n caps a c).eval v =
      if 1≤a.tolerance ∧ a.lowerAt 1≤c.lowerAt 0 ∧ a.upperAt 1≤c.upperAt 0 then
        (numericCosts S F hF i j P a c hm v hv).first
      else (numericCosts S F hF i j P a c hm v hv).total := by
  obtain ⟨h0,h1,h2,h3,h5,h7⟩ := hcap
  dsimp only [ThreeBoundMinmaxA.zeroAExpr]
  by_cases hg : 1≤a.tolerance ∧ a.lowerAt 1≤c.lowerAt 0 ∧ a.upperAt 1≤c.upperAt 0 <;>
    simp only [hg,and_true,true_and,if_true,if_false,h0,h1,h2,h3,h5,h7,ThreeBoundMinmaxA.positiveExpr,
      Expr.maximum,List.foldr_cons,List.foldr_nil,ThreeBoundNumeric.eval_add,
      ThreeBoundNumeric.eval_mul,ThreeBoundNumeric.eval_min,ThreeBoundNumeric.eval_max,
      Expr.eval,Costs.total,Costs.first,Costs.positive,Costs.cross,Costs.high,
      ThreeBoundMinmaxZeroLocal.highCost,numericCosts,Nat.max_zero]

theorem zeroAExpr_sound
    (S : Stage (Fin n) I V) (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : ThreeBoundMinmaxTransfer.PairData S F i j)
    (a c : ThreeBoundMinmaxNumeric.Entry) (hm : ThreeBoundMinmaxNumeric.EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (caps : Caps) (hcap : ZeroCapsMatch caps)
    (hexcl : Exclusions S) (hq : c.tolerance=0) :
    ABound (parent S F) i j ((ThreeBoundMinmaxA.zeroAExpr n caps a c).eval v) := by
  rw [zeroAExpr_eval S F hF i j P a c hm v hv caps hcap]
  have hqS : S.tolerance j=0 := hm.strongTolerance.trans hq
  intro x hoff
  let C := numericCosts S F hF i j P a c hm v hv
  by_cases hg : 1≤a.tolerance ∧ a.lowerAt 1≤c.lowerAt 0 ∧ a.upperAt 1≤c.upperAt 0
  · rw [if_pos hg]
    have hqi : 1≤S.tolerance i := by simpa only [hm.weakTolerance] using hg.1
    have ht : P.weakLower 1≤P.strongLower 0 := by
      change (P.weakLower 1).val≤(P.strongLower 0).val
      rw [hm.weakLower 1 hqi,hm.strongLower 0 (Nat.zero_le _)]
      exact hg.2.1
    have hu : P.weakUpper 1≤P.strongUpper 0 := by
      change (P.weakUpper 1).val≤(P.strongUpper 0).val
      rw [hm.weakUpper 1 hqi,hm.strongUpper 0 (Nat.zero_le _)]
      exact hg.2.2
    exact no_guard_bound S hR F hF i j P hqS x hoff
      (guards_empty_of_forbidden S F hF i j P hqS x hoff hqi ht hu) hexcl C
  · rw [if_neg hg]
    exact zero_bound S hR F hF i j P hqS x hoff hexcl C

end
end ThreeBoundMinmaxZeroExpression

#print axioms ThreeBoundMinmaxZeroExpression.zeroAExpr_sound


