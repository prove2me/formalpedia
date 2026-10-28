-- Prove2me | Definitions.Def_BS2_b3ba934b_MinmaxQ2Bound
-- name    : BS2_b3ba934b_MinmaxQ2Bound
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:58:40.308105+00:00
-- url     : https://prove2.me/theorems/796af529-9949-4e54-93f5-8fdd1aa51b41
-- title:
--   Sensitivity separation: MinmaxQ2Bound (complete source module)
-- statement:
--   Complete Lean source module `MinmaxQ2Bound` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MinmaxQ2Bound.lean; original SHA-256 fd82e85e186f0d61182afb355fa198754aaf84451adf94c5bfefa460dcb89643; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Complete semantic q2 upward bound for actual min/max parent functions. -/
import Definitions.Def_BS2_b3ba934b_MinmaxRecordAllowed
import Definitions.Def_BS2_b3ba934b_MinmaxHighRecord
import Definitions.Def_BS2_b3ba934b_MinmaxEnumeration

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

namespace ThreeBoundMinmaxA
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxCandidates ThreeBoundMinmaxCover ThreeBoundMinmaxQ2
open ThreeBoundMinmaxNumeric (EntryMatch)
open ThreeBoundActualCaps (CapsSound)
open ThreeBoundActualRecordFields ThreeBoundRecordCaps
open ThreeBoundNumeric ThreeBoundFullProfile
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {I V : Type} [Fintype I] [Fintype V]

theorem actual_record_cost (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry) (matchE : EntryMatch S F i j P a c)
    (input : ((V × Bool) × I) → Bool) (hoff : parent S F i input = false)
    (hQ : S.tolerance j ≤ 2) (caps : Caps) (hcaps : CapsSound S.Adj S.label caps)
    (v : Profile n) (hv : Upper F v) (hordered : Ordered v) :
    ∃ xs ∈ ThreeBoundQ2.records,
      recordAllowedFor caps a c (recordOfList xs) = true ∧
      (flipsTo (parent S F j) true input).card ≤ (recordCost n caps a c (recordOfList xs)).eval v := by
  obtain ⟨tag,htag,hcount',hout'⟩ := actual_high_tags S F hF i j P input 2 hQ
  have hcount : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      (failed S F j input w).card=ThreeBoundQ2.budget (tag w) := by
    simpa only [ThreeBoundMinmaxQ2.budget_eq] using hcount'
  have hout : ∀ w ∈ highHeads S F P.strongLower P.strongUpper j input,
      ((highHeads S F P.strongLower P.strongUpper j input).filter (S.Adj w)).card ≤
        ThreeBoundQ2.budget (tag w) := by
    simpa only [ThreeBoundMinmaxQ2.budget_eq] using hout' 
  obtain ⟨ts,ds,e,hsort,hget,hdirs,hmem⟩ :=
    actual_record_exists S hR F hF i j P input hQ tag htag hout
  let H := highHeads S F P.strongLower P.strongUpper j input
  let G := guardSources S F P.strongLower P.strongUpper j input
  let r := recordOfList (ThreeBoundQ2.record (ts,ds))
  have hG : G = H.filter fun w => ThreeBoundQ2.isGuard (tag w) = true :=
    guardSources_eq_filter S F i j P input hQ tag htag
  obtain ⟨htypes,hext,hhist,hrs⟩ := all_record_fields ts ds H G tag S.Adj hR e hget hdirs hG
    (fun w => (failed S F j input w).card) hcount
  have hx : ∀ kind : Fin 8, r kind.val = ThreeBoundAccounting.typeCount H tag kind := by
    intro kind
    unfold ThreeBoundAccounting.typeCount
    convert htypes kind using 1 <;> congr 1 <;> ext w <;> simp [H]
  have hres : ∀ k : Fin 4, k.val+1 ≤ H.card →
      r (25+k.val) = ThreeBoundMinmaxCaps.residualPrefix S F P.strongLower P.strongUpper j input (k.val+1) := by
    intro k hk
    exact hrs k hk
  have hprefix (q : ℕ) (hq : q ≤ 2) :
      (targetPrefix S F P.strongLower P.strongUpper j input q).card ≤ capPrefix caps r q :=
    actual_capPrefix S hR F hF i j P input hQ tag htag hcount caps hcaps r hx hres q hq
  have hpos (q : ℕ) (hq : q ≤ 2) : positivePrefix r q =
      (targetPrefix S F P.strongLower P.strongUpper j input q ∩ H).card :=
    (positivePrefix_card H tag r hx q hq).trans
      (congrArg Finset.card (prefix_high_eq S F hF i j P input hQ tag htag q).symm)
  have hallowed : recordAllowedFor caps a c r = true := by
    apply actual_recordAllowedFor S F hF i j P a c matchE input hoff hQ tag htag caps r hx
    intro q hq
    have hq2 : q ≤ 2 := by rw [← matchE.strongTolerance] at hq; omega
    rw [hpos q hq2]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (hprefix q hq2)
  have hnegative := negativeBits_expr_bound S F hF i j P a c matchE input hQ v hv hordered caps r
    (fun q hq => hprefix q (hq.trans hQ)) (fun q hq => hpos q (hq.trans hQ))
  have hhigh := highBits_expr_bound S F hF i j P a c matchE v hv input hoff hQ tag htag r htypes
    (by
      intro kind hits
      convert hhist kind hits using 1 <;> congr 1 <;> ext w <;> simp [H,G,incomingSources])
  have hexternal := externalBits_expr_bound S F hF i j P a c matchE v hv input hoff r hext
  have hcover := upward_subset S F hF i j P input
    (strong_false_of_weak_false S F hF i j P input hoff)
  have htotal := ThreeBoundAccounting.union_cover_bound
    (flipsTo (parent S F j) true input) (negativeBits S F P.strongLower P.strongUpper j input)
    (highBits S F P.strongLower P.strongUpper j input) (ThreeBoundMinmaxCover.externalBits S F P.strongLower P.strongUpper j input)
    _ _ _ (by
      intro bit hb
      have hh := hcover hb
      simpa only [Finset.mem_union] using hh) hnegative hhigh hexternal
  refine ⟨ThreeBoundQ2.record (ts,ds),hmem,hallowed,?_⟩
  change _ ≤ (r 8 * bExpr n c.guard a.guard).eval v+
    (negativeExpr n caps c r).eval v+(highExpr n a c r).eval v
  change _ ≤ (negativeExpr n caps c r).eval v+(highExpr n a c r).eval v+
    (r 8 * bExpr n c.guard a.guard).eval v at htotal
  omega

theorem gradedAExpr_bound (S : Stage (Fin n) I V)
    (hR : TournamentHighRows.IsTournament S.Adj)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F)
    (i j : Fin n) (P : PairData S F i j) (a c : ThreeBoundMinmaxNumeric.Entry) (matchE : EntryMatch S F i j P a c)
    (hQ : S.tolerance j ≤ 2) (caps : Caps) (hcaps : CapsSound S.Adj S.label caps)
    (records : List (List ℕ)) (hrecords : ∀ xs ∈ ThreeBoundQ2.records, xs ∈ records)
    (v : Profile n) (hv : Upper F v) (hordered : Ordered v) :
    ABound (parent S F) i j ((gradedAExpr n caps records a c).eval v) := by
  intro input hoff
  obtain ⟨xs,hxs,ha,hb⟩ := actual_record_cost S hR F hF i j P a c matchE input hoff
    hQ caps hcaps v hv hordered
  apply hb.trans
  rw [gradedAExpr,Expr.eval_maximum]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨recordCost n caps a c (recordOfList xs),?_,rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨xs,hrecords xs hxs,by simp only [ha,ite_true]⟩

end
end ThreeBoundMinmaxA

#print axioms ThreeBoundMinmaxA.gradedAExpr_bound


