-- Prove2me | Definitions.Def_Sensitivity213303_RecordLookup
-- name    : Sensitivity213303_RecordLookup
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:24:38.50245+00:00
-- url     : https://prove2.me/theorems/4548e901-af9e-458e-985f-061c1f6377c2
-- title:
--   Indexed binary lookup for an exact list of case records
-- statement:
--   A RecordLookup tree stores one exact record at each leaf. At a branch, an index below the cut is routed left and any other index is routed right after subtracting the cut. Validity requires the cut to equal the number of leaves in the left subtree and recursively requires both subtrees valid. The indexed cached check retrieves a row by this representation and applies its exact record-cost checker. Validity is decidable and proves agreement with the flattened row list.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module RecordLookup; source SHA256 2e5ce300e00fc4b5bff13e83e8dd316316fb7334890ab9d2559f1615c9a45952.

/- Verified logarithmic lookup for a finite list of exact case records. -/
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
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring



set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric

inductive RecordLookup where
  | leaf : List ℕ → RecordLookup
  | branch : ℕ → RecordLookup → RecordLookup → RecordLookup

def RecordLookup.rows : RecordLookup → List (List ℕ)
  | .leaf row => [row]
  | .branch _ left right => left.rows++right.rows

def RecordLookup.get : RecordLookup → ℕ → List ℕ
  | .leaf row, _ => row
  | .branch cut left right, k => if k<cut then left.get k else right.get (k-cut)

def RecordLookup.valid : RecordLookup → Prop
  | .leaf _ => True
  | .branch cut left right => cut=left.rows.length ∧ left.valid ∧ right.valid

def RecordLookup.validDecidable : (table : RecordLookup) → Decidable table.valid
  | .leaf _ => inferInstanceAs (Decidable True)
  | .branch cut left right => by
      letI : Decidable left.valid := validDecidable left
      letI : Decidable right.valid := validDecidable right
      exact inferInstanceAs (Decidable (cut=left.rows.length ∧ left.valid ∧ right.valid))

instance (table : RecordLookup) : Decidable table.valid := table.validDecidable



def indexedFastCachedCheck (caps : Caps) (table : RecordLookup) (a c : Entry)
    (values : CostValues) (bound k : ℕ) : Bool :=
  cachedRecordCheck caps a c values bound (table.get k)



end ThreeBoundNumeric


