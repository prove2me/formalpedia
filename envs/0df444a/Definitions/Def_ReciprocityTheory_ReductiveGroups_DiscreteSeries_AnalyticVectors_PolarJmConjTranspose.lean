-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:58.830971+00:00
-- url     : https://prove2.me/theorems/1317eee2-dc68-40cc-bab7-13e9f700d0da
-- title:
--   Polar Jm Conj Transpose
-- statement:
--   Definitions and structural lemmas for Polar Jm Conj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/AnalyticVectors/PolarJmConjTranspose.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace PolarDecomposition
def polar_L (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℝ) • CFC.log (gᴴ * g)
end PolarDecomposition
end ReciprocityTheory.ChartRestriction.DS


