-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_FiniteHeadReindexing
-- name    : Sensitivity214439_PairedSemantic_Solutions_FiniteHeadReindexing
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:45:37.531306+00:00
-- url     : https://prove2.me/theorems/8f31da93-fa9d-412c-accf-954231fa7238
-- title:
--   Pulling an actual head subset back to finite indices
-- statement:
--   Defines indexedSet(head,S) as all indices i in Fin n whose numbered head lies in S. This finite pullback supports exact reindexing of high sets, guard subsets, and incoming incidences.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/FiniteHeadReindexing.lean lines 13–14; SHA256 86c4773e81e243e924ebda2869d1ad6adac37e6e9d97a4540c7fd51240b84a23; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace SensitivityFiniteHeadReindexing
end SensitivityFiniteHeadReindexing



/-! Reindexing finite head sets by an arbitrary injective enumeration.
The enumeration can be the one used by a tournament record certificate. -/
namespace SensitivityFiniteHeadReindexing

noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

variable {n : ℕ} {V A : Type}

def indexedSet (head : Fin n → V) (S : Finset V) : Finset (Fin n) :=
  Finset.univ.filter fun i => head i ∈ S
























end
end SensitivityFiniteHeadReindexing


