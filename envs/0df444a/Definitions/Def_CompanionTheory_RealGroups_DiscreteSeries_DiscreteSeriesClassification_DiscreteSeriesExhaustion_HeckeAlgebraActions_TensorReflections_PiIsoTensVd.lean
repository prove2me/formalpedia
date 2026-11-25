-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd
-- name    : CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_TensorReflections_PiIsoTensVd
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:16.1366+00:00
-- url     : https://prove2.me/theorems/30179dd9-82da-4c64-bb8b-eae2642ab751
-- title:
--   Pi Iso Tens Vd
-- statement:
--   Definitions and structural lemmas for Pi Iso Tens Vd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/TensorReflections/PiIsoTensVd.lean

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {n : ℕ}
def piIso {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) : (Fin n → X.V) ≃ₗ[ℂ] (Fin n → X'.V) :=
  LinearEquiv.piCongrRight fun _ : Fin n => e
end CompanionTheory.RgExh.Hk


