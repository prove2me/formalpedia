-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_NumericOwnFees
-- name    : Sensitivity214439_Phase0_Solutions_NumericOwnFees
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:39:35.633806+00:00
-- url     : https://prove2.me/theorems/ce7b4c77-d175-44c3-b438-65c0afe74f19
-- title:
--   A unary own-target joint price
-- statement:
--   For weak rank $w$, old child height $h$, and needed destination rank $n$, set the loss price to $M(w,h-1)$. The unary joint price is
--   $$
--   \begin{cases}
--   \min\!\left(M(w,h-1)+A(h,n),\,J(w,h-1,n)\right),
--   &h\le n<12,\\
--   M(w,h-1),&\text{otherwise}.
--   \end{cases}
--   $$
--   It combines a separate loss-and-gain estimate with the available exact-source child joint bound.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/NumericOwnFees.lean lines 27–32; SHA256 77855ca2efe7e5d8c7f59147706ff37b0d438facadf3c26fa305d3e189231fbf; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericRecurrence
import Definitions.Def_Sensitivity214439_Phase0_Solutions_LocalNumericSemanticBridge
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityNumericOwnFees
end SensitivityNumericOwnFees
namespace SensitivityOwnNaturalFees
end SensitivityOwnNaturalFees
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction



/-! Integer own-child fees and their exact scaled event bounds. -/
namespace SensitivityNumericOwnFees

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityOwnNaturalFees SensitivityLocalNumericSemantics
set_option autoImplicit false

variable {I Color : Type}





def unaryJointFee (v : NumericBounds) (weak old needed : ℕ) : ℕ :=
  let loss := SensitivityLocalNumeric.entry v.profile 2 weak (old-1)
  if old ≤ needed ∧ needed < 12 then
    min (loss + SensitivityLocalNumeric.entry v.profile 0 old needed)
      (v.joint weak (old-1) needed)
  else loss

















end
end SensitivityNumericOwnFees


