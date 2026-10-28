-- Prove2me | Definitions.Def_Sensitivity213303_CachedRawChecker
-- name    : Sensitivity213303_CachedRawChecker
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:23:44.716998+00:00
-- url     : https://prove2.me/theorems/638fb638-8a5c-4cc3-97e0-93f3c18e835b
-- title:
--   Cached coefficients for exact record-cost verification
-- statement:
--   CostValues stores the child guard, negative-target and head-cost coefficients obtained by evaluating a raw transition at one profile. cachedRecordCost combines those coefficients with a record’s counts, and cachedRecordCheck tests the resulting bound. coeffCheck verifies agreement with the original symbolic coefficients, while indexedCachedCheck checks a specified lookup-table row. The cache avoids repeating common expression evaluation without changing the quantity certified.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module CachedRawChecker; source SHA256 4cb1820a38697618ea1e8472aa4127de8d7c6c806248856ec1a9049238dfa09c.

import Definitions.Def_Sensitivity213303_ClosureCertificate
import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2FastEvaluator
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RawBoundChecker
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
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile

structure CostValues where
  heads : Array (Array ℕ)
  guard : ℕ
  negative : Array ℕ

def coeffCheck (n : ℕ) (v : Profile n) (a c : Entry) (values : CostValues) : Bool :=
  values.heads==computedCosts n v a c &&
  values.guard==(bExpr n c.guard a.guard).eval v &&
  (List.range (c.tolerance+1)).all fun k=>
    values.negative.getD k 0==(aExpr n c.guard (c.threshold k)).eval v

def cachedRecordCost (caps : Caps) (q : ℕ) (values : CostValues) (x : Q2Record) : ℕ :=
  x 8*values.guard+
  ((List.range (q+1)).map fun k=>negativeCount caps q x k*values.negative.getD k 0).sum+
  ((List.range 8).map fun t=>x t*readCost values.heads t 0+
    x (9+2*t)*(readCost values.heads t 1-readCost values.heads t 0)+
    x (10+2*t)*(readCost values.heads t 2-readCost values.heads t 0)).sum



def cachedRecordCheck (caps : Caps) (a c : Entry) (values : CostValues)
    (bound : ℕ) (xs : List ℕ) : Bool :=
  let x:=recordOfList xs
  if recordAllowedFor caps a c x then cachedRecordCost caps c.tolerance values x≤bound else true

def indexedCachedCheck (caps : Caps) (records : List (List ℕ)) (a c : Entry)
    (values : CostValues) (bound k : ℕ) : Bool :=
  cachedRecordCheck caps a c values bound (records[k]?.getD [])





end ThreeBoundNumeric


