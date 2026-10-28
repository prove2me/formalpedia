-- Prove2me | Definitions.Def_Sensitivity213303_RawBoundChecker
-- name    : Sensitivity213303_RawBoundChecker
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:21:42.084993+00:00
-- url     : https://prove2.me/theorems/e25ebc58-31ed-4d6f-bee7-9152c8986aa5
-- title:
--   Indexed finite checks for the maximum graded upward cost
-- statement:
--   For a nested-profile input, two recipes, labeling caps and a proposed bound L, recordBoundCheck accepts an infeasible record or verifies that its exact weighted cost is at most L. indexedRecordCheck applies this predicate to one index of the supplied finite record list, and recordMaximum takes the maximum over feasible rows. The soundness theorem combines a covering collection of index checks into a bound on the whole maximum.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module RawBoundChecker; source SHA256 eef3ec6945a7a5b72aecc0f7018f065cd2f856bde07963297a30f4f3a2c1960a.

/- Bounded exact checks for a raw q2 maximum. Every record is covered by its
index in the supplied finite list. Chunking changes proof evaluation cost,
not the mathematical maximum or its semantic assumptions. -/
import Definitions.Def_Sensitivity213303_ClosureCertificate
import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2FastEvaluator
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
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile



def recordBoundCheck (n : ℕ) (v : Profile n) (caps : Caps) (a c : Entry)
    (bound : ℕ) (xs : List ℕ) : Bool :=
  let x := recordOfList xs
  if recordAllowedFor caps a c x then
    recordCostFast n v caps a c (computedCosts n v a c) x≤bound
  else true

def indexedRecordCheck (n : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (a c : Entry) (bound k : ℕ) : Bool :=
  recordBoundCheck n v caps a c bound (records[k]?.getD [])



def recordMaximum (n : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (a c : Entry) : ℕ :=
  let costs := computedCosts n v a c
  maximum (records.filterMap fun xs=>
    let x := recordOfList xs
    if recordAllowedFor caps a c x then some (recordCostFast n v caps a c costs x) else none)







end ThreeBoundNumeric


