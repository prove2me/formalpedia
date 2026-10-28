-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxHighRecord
-- name    : BS2_b3ba934b_MinmaxHighRecord
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:57:29.385694+00:00
-- url     : https://prove2.me/theorems/b814cc8e-2120-4374-8bbd-57835016a083
-- title:
--   Sensitivity separation: MinmaxHighRecord (complete source module)
-- statement:
--   Complete Lean source module `MinmaxHighRecord` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxHighRecord.lean; original SHA-256 d1d0a64ffcf08b772010a10f246a236f2ee251cae2849e46c7bbe5446d67ccbb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Actual min/max high-head and external residual record bounds. -/
import Definitions.Def_BS2_b3ba934b_MinmaxKindCost
import Definitions.Def_BS2_b3ba934b_ActualRecordFields
import Definitions.Def_BS2_b3ba934b_HeadCostOrder

set_option autoImplicit false
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxA
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover
open ThreeBoundHeadCharge (headBits)
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundNumeric ThreeBoundFullProfile ThreeBoundQ2
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem sum_range_eight (f : ℕ → ℕ) :
    ((List.range 8).map f).sum = ∑ k : Fin 8, f k.val := by
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Fin.val_zero,Fin.val_succ,Fin.val_one]
  norm_num only [Nat.reduceAdd]
  omega

theorem highExpr_eval (a c : ThreeBoundMinmaxNumeric.Entry) (r : Q2Record) (v : Profile n) :
    (highExpr n a c r).eval v = ∑ k : Kind,
      (r k.val * (headCost n a c k.val 0).eval v +
       r (9+2*k.val) * ((headCost n a c k.val 1).eval v-(headCost n a c k.val 0).eval v) +
       r (10+2*k.val) * ((headCost n a c k.val 2).eval v-(headCost n a c k.val 0).eval v)) := by
  rw [highExpr,Expr.eval_sum,List.map_map,sum_range_eight]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Function.comp_apply,ThreeBoundHeadCostOrder.eval_add,
    ThreeBoundHeadCostOrder.eval_scale,ThreeBoundNumeric.eval_sub]

theorem highBits_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (hQ : S.tolerance j ≤ 2)
    (tag : V → Kind)
    (htag : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j x,
      ThreeBoundHighTypes.OfKind 2
        (PositiveCandidate S F P.strongLower P.strongUpper j x w)
        (GuardCandidate S F P.strongLower P.strongUpper j x w) (tag w))
    (r : Q2Record)
    (htypes : ∀ k : Kind, r k.val =
      ((highHeads S F P.strongLower P.strongUpper j x).filter fun w => tag w = k).card)
    (hhist : ∀ (k : Kind) (h : Fin 2), r (9+2*k.val+h.val) =
      ((highHeads S F P.strongLower P.strongUpper j x).filter fun w => tag w = k ∧
        min 2 (incomingSources S F P.strongLower P.strongUpper j x w).card = h.val+1).card) :
    (highBits S F P.strongLower P.strongUpper j x).card ≤ (highExpr n a c r).eval v := by
  let H := highHeads S F P.strongLower P.strongUpper j x
  let inc := fun w => (incomingSources S F P.strongLower P.strongUpper j x w).card
  let sets := fun w => headBits w (actualHeadParts S F P.strongLower P.strongUpper j x w)
  let cost := fun k : Kind => fun h => (headCost n a c k.val h).eval v
  have hcost : ∀ w ∈ H, (sets w).card ≤ cost (tag w) (min 2 (inc w)) := by
    intro w hw
    exact actual_kind_headCost_bound S F hF i j P a c matchE v hv x hoff hQ w (tag w) (htag w hw)
  have hb := ThreeBoundAccounting.histogram_delta_bound H tag inc sets cost hcost
    (fun k => headCost_zero_le a c v k.val 1) (fun k => headCost_zero_le a c v k.val 2)
  letI : DecidableEq ((V × Bool) × I) := fun a b => Classical.propDecidable (a=b)
  have heHigh : highBits S F P.strongLower P.strongUpper j x = H.biUnion sets := by
    ext bit
    simp only [highBits,H,sets,Finset.mem_biUnion]
  rw [heHigh]
  apply hb.trans_eq
  rw [highExpr_eval]
  apply Finset.sum_congr rfl
  intro k _
  have hh1 := hhist k 0
  have hh2 := hhist k 1
  have hindex : 9+2*k.val+1 = 10+2*k.val := by omega
  simp only [Fin.val_zero,Fin.val_one,Nat.add_zero,zero_add,hindex,Nat.reduceAdd] at hh1 hh2
  have ht0 : ThreeBoundAccounting.typeCount H tag k = r k.val := by
    unfold ThreeBoundAccounting.typeCount
    convert (htypes k).symm using 1 <;> congr 1 <;> ext w <;> simp [H]
  have ht1 : ThreeBoundAccounting.hist H tag inc k 1 = r (9+2*k.val) := by
    unfold ThreeBoundAccounting.hist
    convert hh1.symm using 1 <;> congr 1 <;> ext w <;> simp [H,inc]
  have ht2 : ThreeBoundAccounting.hist H tag inc k 2 = r (10+2*k.val) := by
    unfold ThreeBoundAccounting.hist
    convert hh2.symm using 1 <;> congr 1 <;> ext w <;> simp [H,inc]
  rw [ht0,ht1,ht2]

theorem externalBits_expr_bound
    (S : Stage (Fin n) I V) (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry) (matchE : EntryMatch S F i j P a c)
    (v : Profile n) (hv : Upper F v) (x : ((V × Bool) × I) → Bool)
    (hoff : parent S F i x = false) (r : Q2Record)
    (hext : r 8 = ∑ w ∈ guardSources S F P.strongLower P.strongUpper j x,
      ((failed S F j x w).card-((highHeads S F P.strongLower P.strongUpper j x).filter (S.Adj w)).card)) :
    (ThreeBoundMinmaxCover.externalBits S F P.strongLower P.strongUpper j x).card ≤
      (r 8 * bExpr n c.guard a.guard).eval v := by
  have hs := bExpr_bound F v hv (S.guard j) (S.guard i) P.guards
  have hb := ThreeBoundAccounting.externalBits_card_le S F i j x
    (guardSources S F P.strongLower P.strongUpper j x) (highHeads S F P.strongLower P.strongUpper j x)
    (high_guards_true S F hF i j P x)
    (by
      intro z hz w hw
      obtain ⟨b,hb⟩ := (Finset.mem_filter.mp hz).2
      exact guard_hit_eligible S F hF i j P x hoff z b hb w hw) _ hs
  change (ThreeBoundMinmaxCover.externalBits S F P.strongLower P.strongUpper j x).card ≤ _ at hb
  rw [← hext,matchE.strongGuard,matchE.weakGuard] at hb
  exact hb


end
end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.highBits_expr_bound
#print axioms ThreeBoundMinmaxA.externalBits_expr_bound


