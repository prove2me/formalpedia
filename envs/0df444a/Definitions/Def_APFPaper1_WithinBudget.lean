-- Prove2me | Definitions.Def_APFPaper1_WithinBudget
-- name    : APFPaper1_WithinBudget
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-13T01:49:54.943702+00:00
-- url     : https://prove2.me/theorems/36badeaf-3889-48a3-94d4-9680f665598f
-- title:
--   Witnessed same-protocol budget feasibility
-- statement:
--   WithinBudget L S b means that one protocol p on the same supplied Ledger serves the finite family S and has complete price at most b. This is witnessed feasibility, distinct from the infimal inequality cost L S <= b at an unattained endpoint. Generic Ledger values are not thereby physically instantiated.
-- source:
--   Paper 1 Supplement v9.27:1754-1782, especially 1778-1782, with ledger admissibility distinguished from substrate wording at 1851-1862. Historical WithinBudget definition lines 47-48 retained; only explicit Record carrier/current provider binding added. FOUNDATION_INPUTS 2026-10-04.1 unchanged.

import Definitions.Def_APFPaper1_CostLedger

set_option autoImplicit false

namespace APFPaper1.Foundation

/-- Witnessed budget feasibility for the SAME original Ledger and protocol.
Paper 1 Supplement v9.27:1778-1782 distinguishes this actual witness from
infimal ledger admissibility at an unattained endpoint. This definition
asserts no global affordability, attainment or cost/familyCost bridge. -/
def WithinBudget {D P Record : Type*} (L : Ledger D P Record) (S : Finset D) (b : ℝ) : Prop :=
  ∃ p, L.serves p S ∧ L.price p ≤ b

end APFPaper1.Foundation


