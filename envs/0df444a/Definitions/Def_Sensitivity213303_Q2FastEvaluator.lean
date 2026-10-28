-- Prove2me | Definitions.Def_Sensitivity213303_Q2FastEvaluator
-- name    : Sensitivity213303_Q2FastEvaluator
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:20:41.798477+00:00
-- url     : https://prove2.me/theorems/1994876d-7491-48fd-af37-12f5c1a19f6f
-- title:
--   Shared-cost evaluation of the exact tolerance-two transfer formulas
-- statement:
--   The evaluator computes the eight-by-three head-cost array once and reuses it across all high-head records. Each record cost adds the external guard contribution, the greedily allocated negative-head contribution, and the incoming-hit histogram increments. rawAFast takes the prescribed feasible-record maximum and ordinary refinements; rawPFast and rawDFast add the strict conditional refinements. Separate equivalence theorems identify these efficient evaluators with the original arithmetic expressions.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module Q2FastEvaluator; source SHA256 1546b3f5edf37a4f1d981653a5dc4525b89288e3d9c17f39a3e6a93a22ba0978.

/- Efficient arithmetic evaluation of the same raw q2 formulas.
The equivalence theorem below is proved in Lean; the optimization merely
shares the 24 head costs instead of rebuilding them for every record. -/
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile


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



def recordCostFast (n : ℕ) (v : Profile n) (caps : Caps) (a c : Entry)
    (costs : Array (Array ℕ)) (x : Q2Record) : ℕ :=
  x 8 * (bExpr n c.guard a.guard).eval v +
  ((List.range (c.tolerance+1)).map fun k=>
    negativeCount caps c.tolerance x k * (aExpr n c.guard (c.threshold k)).eval v).sum +
  ((List.range 8).map fun t=>
    x t * readCost costs t 0 +
    x (9+2*t) * (readCost costs t 1-readCost costs t 0) +
    x (10+2*t) * (readCost costs t 2-readCost costs t 0)).sum



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







end ThreeBoundNumeric


