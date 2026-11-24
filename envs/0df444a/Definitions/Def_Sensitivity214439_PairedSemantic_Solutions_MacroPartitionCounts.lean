-- Prove2me | Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionCounts
-- name    : Sensitivity214439_PairedSemantic_Solutions_MacroPartitionCounts
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T19:56:29.971379+00:00
-- url     : https://prove2.me/theorems/dac3093b-1888-4aff-b944-03c047aa975d
-- title:
--   A single count stored at each represented guard cluster
-- statement:
--   Defines clusterCounts to place a cluster's supplied amount only at the least-index representative of a cluster that contains a guard index, and zero elsewhere. Summing this function therefore counts each relevant source macro once.
-- source:
--   Formalization for https://prove2.me/campaigns/block-sensitivity-vs-sensitivity; checked task source lean/Solutions/MacroPartitionCounts.lean lines 14–15; SHA256 2037b609f86a3cc25b982ede6311762781adf9ce5e7dc1b28204aa6a32027705; original campaign checkpoint SHA256 ed463039fb45e15e0e62a99e149dc811ac44ae8f790a5ae03ea5a7501f0639df.

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_MacroPartitionModel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

namespace SensitivityMacroPartitionModel
end SensitivityMacroPartitionModel



/-! The counts attached to a cluster are kept once for pricing and once per
guard head for the uncompressed incidence budget. The finite product of
bounded counts includes every actual assignment. -/
namespace SensitivityMacroPartitionModel

noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false

variable {n : ℕ} {M : Type}

def clusterCounts (cluster : Fin n → M) (G : Finset (Fin n)) (amount : M → ℕ) (k : Fin n) : ℕ :=
  if k ∈ G.image (least cluster) then amount (cluster k) else 0





















end
end SensitivityMacroPartitionModel


