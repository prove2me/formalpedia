-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSheetLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:50:17.740016+00:00
-- url     : https://prove2.me/theorems/f8c0825c-9b40-449e-961f-9f749882fee8
-- title:
--   PSheet Lift
-- statement:
--   Definitions and structural lemmas for PSheet Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSheetLift.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSheetLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_eval_bsmul_of_isMultiHomog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_prod_update_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights
open Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomogIdeal mcPts segre IsSheet bsmul eval_bsmul_of_isMultiHomog
  prod_update_eq)
namespace SheetLift
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def lift [DecidableEq K] (i0 : (k : K) → ι k) (k0 : K) (w : ((k : K) → ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => (if p.1 = k0 then w i0 else 1) * (w (Function.update i0 p.1 p.2) / w i0)
end SheetLift
end GroundTheory.Heights₂.Heights


