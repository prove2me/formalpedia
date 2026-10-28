-- Prove2me | Definitions.Def_BS2_b3ba934b_Q2FastEvaluator
-- name    : BS2_b3ba934b_Q2FastEvaluator
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:28:27.386+00:00
-- url     : https://prove2.me/theorems/9a5d0650-9d5e-405b-ac7c-8c63863e03b6
-- title:
--   Sensitivity separation: Q2FastEvaluator (complete source module)
-- statement:
--   Complete Lean source module `Q2FastEvaluator` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Q2FastEvaluator.lean; original SHA-256 1546b3f5edf37a4f1d981653a5dc4525b89288e3d9c17f39a3e6a93a22ba0978; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Efficient arithmetic evaluation of the same raw q2 formulas.
The equivalence theorem below is proved in Lean; the optimization merely
shares the 24 head costs instead of rebuilding them for every record. -/
import Definitions.Def_BS2_b3ba934b_Q2RawExpressions
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile

def computedCosts (n : ℕ) (v : Profile n) (a c : Entry) : Array (Array ℕ) := #[
  #[(headCost n a c 0 0).eval v,(headCost n a c 0 1).eval v,(headCost n a c 0 2).eval v],
  #[(headCost n a c 1 0).eval v,(headCost n a c 1 1).eval v,(headCost n a c 1 2).eval v],
  #[(headCost n a c 2 0).eval v,(headCost n a c 2 1).eval v,(headCost n a c 2 2).eval v],
  #[(headCost n a c 3 0).eval v,(headCost n a c 3 1).eval v,(headCost n a c 3 2).eval v],
  #[(headCost n a c 4 0).eval v,(headCost n a c 4 1).eval v,(headCost n a c 4 2).eval v],
  #[(headCost n a c 5 0).eval v,(headCost n a c 5 1).eval v,(headCost n a c 5 2).eval v],
  #[(headCost n a c 6 0).eval v,(headCost n a c 6 1).eval v,(headCost n a c 6 2).eval v],
  #[(headCost n a c 7 0).eval v,(headCost n a c 7 1).eval v,(headCost n a c 7 2).eval v]
]

def readCost (costs : Array (Array ℕ)) (t h : ℕ) : ℕ :=
  (costs.getD t #[]).getD h 0

theorem readCost_computed (n : ℕ) (v : Profile n) (a c : Entry)
    (t : Fin 8) (h : Fin 3) :
    readCost (computedCosts n v a c) t.val h.val = (headCost n a c t.val h.val).eval v := by
  fin_cases t <;> fin_cases h <;> rfl

def recordCostFast (n : ℕ) (v : Profile n) (caps : Caps) (a c : Entry)
    (costs : Array (Array ℕ)) (x : Q2Record) : ℕ :=
  x 8 * (bExpr n c.guard a.guard).eval v +
  ((List.range (c.tolerance+1)).map fun k=>
    negativeCount caps c.tolerance x k * (aExpr n c.guard (c.threshold k)).eval v).sum +
  ((List.range 8).map fun t=>
    x t * readCost costs t 0 +
    x (9+2*t) * (readCost costs t 1-readCost costs t 0) +
    x (10+2*t) * (readCost costs t 2-readCost costs t 0)).sum

theorem recordCostFast_eq (n : ℕ) (v : Profile n) (caps : Caps) (a c : Entry)
    (x : Q2Record) :
    recordCostFast n v caps a c (computedCosts n v a c) x = (recordCost n caps a c x).eval v := by
  simp only [recordCostFast,recordCost,Expr.eval,Expr.eval_sum,List.map_map]
  congr 1

def rawAFast (n : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (a c : Entry) : ℕ :=
  let qi := a.tolerance
  let q := c.tolerance
  if q=0 then (ordinaryAExpr n caps a.t0 a.guard
    (if 1 ≤ qi ∧ a.threshold 1 ≤ c.t0 then 1 else 0) c.t0 c.guard 0).eval v
  else if 3 ≤ q then (ordinaryAExpr n caps a.t0 a.guard qi c.t0 c.guard q).eval v
  else
    let costs := computedCosts n v a c
    let first := maximum (records.filterMap fun xs=>
      let x := recordOfList xs
      if recordAllowedFor caps a c x then some (recordCostFast n v caps a c costs x) else none)
    if c.ordinary then
      ((interval q (qi+1)).filterMap fun level=>
        if a.threshold level ≤ c.t0 then
          some ((ordinaryAExpr n caps (a.threshold level) a.guard level c.t0 c.guard q).eval v)
        else none).foldl Nat.min first
    else first

theorem rawAFast_eq (n : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (a c : Entry) : rawAFast n v caps records a c = (rawAExpr n caps records a c).eval v := by
  by_cases h0 : c.tolerance=0
  · simp only [rawAFast,rawAExpr,h0,if_pos]
  by_cases h3 : 3≤c.tolerance
  · simp only [rawAFast,rawAExpr,h0,h3,if_neg,if_pos,if_false,if_true]
  by_cases ho : c.ordinary=true <;>
    simp [rawAFast,rawAExpr,h0,h3,ho,Expr.eval_minimum,Expr.eval_maximum,
      List.map_filterMap,Function.comp_def,apply_ite,recordCostFast_eq]

def rawPFast (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (j k l : Entry) : ℕ :=
  if j.same k then 0 else
    let first := rawAFast n v caps records k l
    if j.tolerance=0 ∧ l.tolerance=0 then
      let cross := caps.pcross*(aExpr n j.guard l.t0).eval v
      let m₀ := (minusExpr n l.guard j.t0 k.t0).eval v
      let m₁ := (minusExpr n l.guard k.guard j.guard).eval v
      let z₁ := 2*(bExpr n l.guard j.t0).eval v+cross+
        max ((plusExpr n j.t0 k.t0 l.t0).eval v) m₁
      let target := if j.t0 < k.t0 then cross+maximum [2*m₀,
        m₀+(bExpr n l.guard k.t0).eval v,
        (unionExpr n l.guard j.t0 k.t0 l.t0).eval v+(bExpr n l.guard l.t0).eval v] else 0
      let guard := if k.guard < j.guard then cross+max (2*(bExpr n l.guard k.t0).eval v)
        (2*(bExpr n l.guard l.t0).eval v+m₁) else 0
      min (min first z₁) (max target guard)
    else first

theorem rawPFast_eq (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (j k l : Entry) : rawPFast n degree v caps records j k l =
      (rawPExpr n degree caps records j k l).eval v := by
  simp only [rawPFast,rawPExpr,rawAFast_eq]
  split_ifs <;> simp [Expr.eval,Expr.eval_maximum,maximum,apply_ite]

def rawDFast (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (i j k l : Entry) : ℕ :=
  let first := (rawMExpr n degree i j k).eval v + rawPFast n degree v caps records j k l
  if j.tolerance=0 ∧ l.tolerance=0 then
    let strict := if j.same k then 0 else
      let bb := (bExpr n i.t0 l.t0).eval v
      let aa := (aExpr n l.guard i.guard).eval v
      maximum [(primitiveMExpr n degree i.t0 i.guard 0 j k).eval v,
        if j.t0 < k.t0 then bb+degree*aa+(unionExpr n i.t0 j.t0 k.t0 l.t0).eval v else 0,
        if k.guard < j.guard then 2*bb+(degree-1)*aa+
          (unionExpr n l.guard k.guard j.guard i.guard).eval v else 0]
    min first strict
  else first

theorem rawDFast_eq (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (i j k l : Entry) : rawDFast n degree v caps records i j k l =
      (rawDExpr n degree caps records i j k l).eval v := by
  simp only [rawDFast,rawDExpr,rawPFast_eq]
  split_ifs <;> simp [Expr.eval,Expr.eval_maximum,maximum,apply_ite]

def rawFast (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (recipe : Fin n → Entry) : Profile n
  | .a i j => rawAFast n v caps records (recipe i) (recipe j)
  | .b i j => (rawBExpr n degree (recipe i) (recipe j)).eval v
  | .m i j => (rawMExpr n degree (recipe i) (recipe j) (recipe (next j))).eval v
  | .p j l => rawPFast n degree v caps records (recipe j) (recipe (next j)) (recipe l)
  | .d i j l => rawDFast n degree v caps records (recipe i) (recipe j) (recipe (next j)) (recipe l)

theorem rawFast_eq (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (recipe : Fin n → Entry) : rawFast n degree v caps records recipe =
      rawTransfer n degree caps records recipe v := by
  funext coord
  cases coord <;> simp only [rawFast,rawTransfer,rawExpr,rawAFast_eq,rawPFast_eq,rawDFast_eq]

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.rawAFast_eq
#print axioms ThreeBoundNumeric.rawFast_eq


