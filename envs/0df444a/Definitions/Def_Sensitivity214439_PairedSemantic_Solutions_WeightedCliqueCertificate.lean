-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_WeightedCliqueCertificate
-- name    : Sensitivity214439_PairedSemantic_Solutions_WeightedCliqueCertificate
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:34.416589+00:00
-- url     : https://prove2.me/theorems/8204eb93-a3b2-4ae2-9bec-ae8ed7375bc0
-- title:
--   Weighted coloring and branch certificate checks
-- statement:
--   A color-class fee is the maximum nonnegative vertex weight in that class, with fee zero for an empty class. The weighted coloring check requires independent classes covering the candidate mask and bounds their total fees.
--
--   The recursive certificate check accepts either such a coloring leaf or a vertex split. The inside branch restricts the mask to neighbors and subtracts the split vertex's weight from the budget; the outside branch removes that vertex. The checker verifies the subtraction bound and both branches.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/WeightedCliqueCertificate.lean lines 11–94; SHA256 72037be65f9252ea0e5fab90db142b411b84bef23fde2c287be9bddd815bedc9; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_CliqueCertificate
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Nat.Bitwise

namespace SensitivityCliqueCertificate
end SensitivityCliqueCertificate
namespace SensitivityWeightedCliqueCertificate
end SensitivityWeightedCliqueCertificate



/-! The same explicit branch/coloring proof objects with nonnegative vertex weights. -/
namespace SensitivityWeightedCliqueCertificate

open scoped BigOperators
open SensitivityCliqueCertificate
set_option autoImplicit false

def classFee (weight : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | v :: rest => max (weight v) (classFee weight rest)





def coloringCheck (adj weight : ℕ → ℕ) (mask bound : ℕ) (classes : List (List ℕ)) : Bool :=
  decide ((classes.map (classFee weight)).sum ≤ bound) &&
    (decide (mask &&& maskOf classes.flatten = mask) && classes.all (independentCheck adj))



def check (adj weight : ℕ → ℕ) (mask bound : ℕ) : Certificate → Bool
  | .color classes => coloringCheck adj weight mask bound classes
  | .split v inside outside =>
      decide (weight v ≤ bound) &&
      (check adj weight (mask &&& adj v) (bound - weight v) inside &&
        check adj weight (mask ^^^ 2 ^ v) bound outside)





end SensitivityWeightedCliqueCertificate


