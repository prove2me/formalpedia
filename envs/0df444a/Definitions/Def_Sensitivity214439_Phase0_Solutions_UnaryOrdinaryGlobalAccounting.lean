-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalAccounting
-- name    : Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalAccounting
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T18:52:43.074496+00:00
-- url     : https://prove2.me/theorems/97c309a1-81b4-4737-a01b-47f2c989212c
-- title:
--   Scalar charge for ordinary unary global events
-- statement:
--   For an ordinary context, write $L,T,G,D,E$ for its low rows, high targets, high guard heads, donors, and external donors. Define the total scalar charge
--   $$
--   |L|p_{\rm low}+|T|p_{\rm high}
--   +|D\cap T|(p_{\rm marked}-p_{\rm high})
--   +|D\cap G|p_{\rm internal}+|E|p_{\rm external}.
--   $$
--   The marked increment uses natural-number subtraction; the context's valid prices ensure that the marked price is at least the high price.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; task source lean/Solutions/UnaryOrdinaryGlobalAccounting.lean lines 18–21; SHA256 9e9ba1ba57baecb88ac31c65f9430c422a7f48d2fcb3e46f1c684deefd6a6089; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryContext
import Definitions.Def_Sensitivity214439_Phase0_Solutions_UnaryOrdinaryGlobalNumeric
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivityUnaryOrdinaryContext
end SensitivityUnaryOrdinaryContext
namespace SensitivityUnaryOrdinaryContext.Context
end SensitivityUnaryOrdinaryContext.Context
namespace SensitivityUnaryOrdinaryGlobalNumeric
end SensitivityUnaryOrdinaryGlobalNumeric



/-! Each ordinary unary repairing coordinate is charged once to a low row,
target head, internal donor, or external donor. -/
namespace SensitivityUnaryOrdinaryContext

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityGuardEvents
open SensitivityUnaryOrdinaryGlobalNumeric
set_option autoImplicit false

variable {V I Color : Type} [Fintype V] [Fintype I]

namespace Context

def charge (c : Context V I Color) : ℕ :=
  c.low.card*c.prices.low + c.targets.card*c.prices.high +
    (c.donors ∩ c.targets).card*(c.prices.marked-c.prices.high) +
    (c.donors ∩ c.guardHeads).card*c.prices.internal + c.external.card*c.prices.external







end Context
end
end SensitivityUnaryOrdinaryContext


