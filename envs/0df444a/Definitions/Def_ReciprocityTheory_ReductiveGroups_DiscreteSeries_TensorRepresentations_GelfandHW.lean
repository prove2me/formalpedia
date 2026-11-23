-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:23.314284+00:00
-- url     : https://prove2.me/theorems/45c9d417-bff0-4b00-b523-cb1f691788c9
-- title:
--   Gelfand HW
-- statement:
--   Definitions and structural lemmas for Gelfand HW, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/GelfandHW.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
def hwShift (ν : Fin n → ℝ) : Fin n → ℂ := fun r => ((ν r : ℝ) : ℂ) + (((n - 1 - (r : ℕ) : ℕ) : ℝ) : ℂ)
end ReciprocityTheory.ChartRestriction.DS


