-- Prove2me | Definitions.Def_BS2_b3ba934b_OrdinaryNumericCases
-- name    : BS2_b3ba934b_OrdinaryNumericCases
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:30:45.132016+00:00
-- url     : https://prove2.me/theorems/8109624c-d6a8-4799-9523-0947204f187c
-- title:
--   Sensitivity separation: OrdinaryNumericCases (complete source module)
-- statement:
--   Complete Lean source module `OrdinaryNumericCases` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/OrdinaryNumericCases.lean; original SHA-256 a7a9622c86611655479dfd01063dbe9696ab439777116d4260166bb6f1179473; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Exact compatibility of the ordinary finite arithmetic cases with the new
expression evaluator. The q=1, three-positive branch uses the proved cap 26. -/
import Definitions.Def_BS2_b3ba934b_RawConditionalBase

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions
open scoped Classical
noncomputable section
variable {n : ℕ}

def ordinaryCaps10007 : Caps := {
  ordinary := #[23,30,37,43,49,54,60,65,71]
  guard := #[20,28,34,40,46,53,59,64,70]
  target := #[20,29,35,41,47,53,59,64,70]
  marked := #[29,35,41,47,27,34,24,28,31,29,34,27]
  zero := #[22,19,17,19,20,17,18,17]
  pcross := 19 }

deriving instance DecidableEq for OrdinaryCase

def booleanOrdinaryCase (q m u : ℕ) : OrdinaryCase :=
  let low := (u*m+u.choose 2)-q*u
  ⟨u,ThreeBoundOrdinaryArchive.ZT.candidateTotalCap q m u,
    m*(q+1)-m.choose 2,min (m.choose 2) (2*m),low,low-u,
    ThreeBoundOrdinaryArchive.ZP.markedCap q m⟩

/-- A small exhaustive arithmetic identity, checked by the Lean kernel. -/
theorem ordinaryCase_finite : ∀ (q : Fin 9) (m : Fin 20) (u : Fin 18),
    (u.val+m.val).choose 2 ≤ q.val*u.val+(q.val+1)*m.val →
    u.val ≤ ThreeBoundOrdinaryArchive.ZT.candidateTotalCap q.val m.val u.val →
    ordinaryCase ordinaryCaps10007 q.val m.val u.val=some (booleanOrdinaryCase q.val m.val u.val) := by
  decide +kernel

theorem ordinaryCase_of_candidate (q m u : ℕ) (hq : q ≤ 8) (hm : m ≤ 2*q+3) (hu : u ≤ 2*q+1)
    (hc : (u+m).choose 2 ≤ q*u+(q+1)*m)
    (hcap : u ≤ ThreeBoundOrdinaryArchive.ZT.candidateTotalCap q m u) :
    ordinaryCase ordinaryCaps10007 q m u=some (booleanOrdinaryCase q m u) := by
  exact ordinaryCase_finite ⟨q,by omega⟩ ⟨m,by omega⟩ ⟨u,by omega⟩ hc hcap

theorem booleanOrdinaryCase_mem (q qa m u : ℕ) (hq : q ≤ 8)
    (hm : m ≤ (if qa=q then 2*q+3 else 0)) (hu : u ≤ 2*q+1)
    (hc : (u+m).choose 2 ≤ q*u+(q+1)*m)
    (hcap : u ≤ ThreeBoundOrdinaryArchive.ZT.candidateTotalCap q m u) :
    booleanOrdinaryCase q m u ∈ ordinaryCases ordinaryCaps10007 q (qa == q) := by
  have hm' : m ≤ 2*q+3 := by split_ifs at hm <;> omega
  have hcase := ordinaryCase_of_candidate q m u hq hm' hu hc hcap
  apply List.mem_flatMap.mpr
  refine ⟨m,?_,?_⟩
  · apply List.mem_range.mpr
    simpa only [beq_iff_eq] using (Nat.lt_succ_of_le hm)
  · apply List.mem_filterMap.mpr
    exact ⟨u,List.mem_range.mpr (by omega),hcase⟩

theorem positiveCaseCost_mono_j (q m u a b s j k : ℕ) (hjk : j ≤ k) :
    ThreeBoundOrdinaryArchive.ZT.positiveCaseCost q m u a b s j ≤
      ThreeBoundOrdinaryArchive.ZT.positiveCaseCost q m u a b s k := by
  dsimp only [ThreeBoundOrdinaryArchive.ZT.positiveCaseCost,ThreeBoundOrdinaryArchive.ZT.deletionCost]
  gcongr

theorem zeroCost_mono_j (a b s j k d : ℕ) (hjk : j ≤ k) :
    ThreeBoundOrdinaryArchive.ZT.zeroCost a b s j d ≤ ThreeBoundOrdinaryArchive.ZT.zeroCost a b s k d := by
  unfold ThreeBoundOrdinaryArchive.ZT.zeroCost
  gcongr

/-- Every realizable positive ordinary case occurs in the numeric maximum. -/
theorem ordinaryAExpr_case_bound (v : Profile n) (ta ga qa tb gb q m u : ℕ)
    (hpos : 0<q) (hq : q ≤ 8)
    (hm : m ≤ (if qa=q then 2*q+3 else 0)) (hu : u ≤ 2*q+1)
    (hc : (u+m).choose 2 ≤ q*u+(q+1)*m)
    (hcap : u ≤ ThreeBoundOrdinaryArchive.ZT.candidateTotalCap q m u)
    (hskip : 0<u → gb ≠ ta) :
    ThreeBoundOrdinaryArchive.ZT.positiveCaseCost q m u
      ((plusExpr n gb ta tb).eval v) ((aExpr n gb tb).eval v)
      ((bExpr n gb ga).eval v) ((bExpr n gb tb).eval v) ≤
      (ordinaryAExpr n ordinaryCaps10007 ta ga qa tb gb q).eval v := by
  have hmem := booleanOrdinaryCase_mem q qa m u hq hm hu hc hcap
  have hskip' : ¬ (0<u ∧ gb=ta) := by rintro ⟨hu,he⟩; exact hskip hu he
  simp only [ordinaryAExpr,if_neg (by omega : q≠0),Expr.eval_maximum,List.map_map]
  apply le_maximum_of_mem
  apply List.mem_map.mpr
  refine ⟨booleanOrdinaryCase q m u,hmem,?_⟩
  simp only [Function.comp_apply,booleanOrdinaryCase,if_neg hskip',
    ThreeBoundOrdinaryArchive.ZT.positiveCaseCost,ThreeBoundOrdinaryArchive.ZT.deletionCost,
    eval_add,eval_mul,eval_max]

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.ordinaryCase_finite
#print axioms ThreeBoundConditionalNumeric.ordinaryAExpr_case_bound


