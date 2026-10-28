-- Prove2me | Definitions.Def_Sensitivity213303_PreparedRawChecker
-- name    : Sensitivity213303_PreparedRawChecker
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:25:45.63125+00:00
-- url     : https://prove2.me/theorems/8b851638-8dd9-4e17-bf1e-21e3bc0e9822
-- title:
--   Verified cached prefix allocations for graded record checks
-- statement:
--   PreparedValues stores record feasibility and the negative-candidate allocations for a fixed tolerance and labeling-cap system. PreparedOK states exact agreement with the original allowed-record predicate and greedy negative counts. The checker adds the recipe-specific state restrictions, computes the weighted cost from cached coefficients, and tests it against a proposed natural-number bound at a balanced-table index. Soundness lemmas connect these cached computations to the original raw A expression.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module PreparedRawChecker; source SHA256 48d41645deba94349602164ef88f37bbcc01c726df185bb5d88d6740cb8ef1a2.

/- Reuse the exact record cap computation across all recipe pairs. -/
import Definitions.Def_Sensitivity213303_CachedRawChecker
import Definitions.Def_Sensitivity213303_ClosureCertificate
import Definitions.Def_Sensitivity213303_ClosureHomogeneity
import Definitions.Def_Sensitivity213303_FlatProfiles
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2FastEvaluator
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_Sensitivity213303_RawBoundChecker
import Definitions.Def_Sensitivity213303_RecordLookup
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring



set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundNumeric

structure PreparedValues where
  feasible : Bool
  negative : Array ℕ

def PreparedOK (caps : Caps) (q : ℕ) (x : Q2Record) (p : PreparedValues) : Prop :=
  p.feasible=allowedRecord caps q x ∧
    (p.feasible=true → ∀ k : Fin (q+1), p.negative.getD k.val 0=negativeCount caps q x k.val)

instance (caps : Caps) (q : ℕ) (x : Q2Record) (p : PreparedValues) :
    Decidable (PreparedOK caps q x p) := by unfold PreparedOK; infer_instance

def recordStateAllowed (a c : Entry) (x : Q2Record) : Bool :=
  (List.range (c.tolerance+1)).all (fun k =>
      !(k<a.tolerance ∧ a.threshold (k+1)≤c.threshold k) ||
        (x (3+k)==0 && (if k=0 then x 6==0 else if k=1 then x 7==0 else true))) &&
    (List.range (c.tolerance+1)).all (fun k => x k==0 ||
      !(c.guard==(if k=0 then a.threshold k else min (a.threshold k) (c.threshold (k-1)))))



def preparedCost (q : ℕ) (p : PreparedValues) (values : CostValues) (x : Q2Record) : ℕ :=
  x 8*values.guard+
  ((List.range (q+1)).map fun k=>p.negative.getD k 0*values.negative.getD k 0).sum+
  ((List.range 8).map fun t=>x t*readCost values.heads t 0+
    x (9+2*t)*(readCost values.heads t 1-readCost values.heads t 0)+
    x (10+2*t)*(readCost values.heads t 2-readCost values.heads t 0)).sum



def preparedRecordCheck (a c : Entry) (p : PreparedValues) (values : CostValues)
    (bound : ℕ) (xs : List ℕ) : Bool :=
  let x:=recordOfList xs
  if p.feasible && recordStateAllowed a c x then preparedCost c.tolerance p values x≤bound else true



def indexedPreparedCheck (table : RecordLookup) (pre : ℕ → PreparedValues)
    (a c : Entry) (values : CostValues) (bound k : ℕ) : Bool :=
  preparedRecordCheck a c (pre k) values bound (table.get k)



end ThreeBoundNumeric


