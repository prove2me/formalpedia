-- Prove2me | Definitions.Def_BS2_b3ba934b_CapAlgorithm
-- name    : BS2_b3ba934b_CapAlgorithm
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:32:23.710979+00:00
-- url     : https://prove2.me/theorems/7e514985-1dc3-4f9a-8fec-793ffc3d3a5a
-- title:
--   Sensitivity separation: CapAlgorithm (complete source module)
-- statement:
--   Complete Lean source module `CapAlgorithm` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/CapAlgorithm.lean; original SHA-256 f6ba20d1d9b36b58f2afc8f1b744cbedfa0c71a2875d9ab5af50a7161880f316; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Numerical prefix-cap composition, separated from its actual candidate
proofs. Each premise is one of the independently established labeling caps. -/
import Definitions.Def_BS2_b3ba934b_Q2RawExpressions
import Definitions.Def_BS2_b3ba934b_GlobalAccounting

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

namespace ThreeBoundCapAlgorithm
open ThreeBoundNumeric
open scoped BigOperators Classical

def lowCount (x : Q2Record) (q : ℕ) : ℕ :=
  ((List.range 8).filterMap fun t =>
    if !positiveInside t q ∧ kindBudget t ≤ q then some (x t) else none).sum

def nextCount (x : Q2Record) (q : ℕ) : ℕ :=
  ((List.range 8).filterMap fun t =>
    if !positiveInside t q ∧ kindBudget t ≤ q+1 then some (x t) else none).sum

def eligibleCount (x : Q2Record) (q : ℕ) : ℕ :=
  ((List.range 8).filterMap fun t => if kindBudget t ≤ q+1 then some (x t) else none).sum

theorem capPrefix_bound (caps : Caps) (x : Q2Record) (q a : ℕ)
    (hbase : a ≤ min (Caps.at caps.ordinary q-1-lowCount x q)
      (Caps.at caps.ordinary q-nextCount x q))
    (hs : q=0 → 1 ≤ headCount x → a ≤ x 0+caps.pcross+x 25)
    (hd : q=0 → 2 ≤ headCount x → a ≤ x 0+Caps.at caps.zero 2+x 26)
    (hm₁ : q≠0 → 1 ≤ eligibleCount x q →
      a ≤ Caps.at caps.marked (q-1)-1+(1-nextCount x q))
    (hm₂ : q≠0 → 2 ≤ eligibleCount x q →
      a ≤ Caps.at caps.marked (if q=1 then 4 else 5)-1+(2-nextCount x q))
    (hz₁ : q=1 → 3 ≤ headCount x → a ≤ positivePrefix x q+Caps.at caps.marked 6-1+x 27)
    (hz₂ : q=2 → 4 ≤ headCount x → a ≤ positivePrefix x q+Caps.at caps.marked 7-1+x 28) :
    a ≤ capPrefix caps x q := by
  unfold capPrefix
  dsimp only
  split_ifs <;> simp_all [lowCount,nextCount,eligibleCount,le_min_iff]

theorem sum_filterMap_eight (x : ℕ → ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((List.range 8).filterMap fun k => if p k then some (x k) else none).sum =
      ∑ k : Fin 8, if p k.val then x k.val else 0 := by
  simp only [List.range_succ,List.range_zero,List.filterMap_append,List.filterMap_cons,
    List.filterMap_nil,List.sum_append,List.sum_cons,List.sum_nil,
    Fin.sum_univ_succ,Fin.sum_univ_zero,Fin.val_zero,Fin.val_succ,Fin.val_one]
  split_ifs <;> simp_all <;> omega

end ThreeBoundCapAlgorithm

#print axioms ThreeBoundCapAlgorithm.capPrefix_bound


