-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_BesselIntegrals_BesselXiIntegrable
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_BesselIntegrals_BesselXiIntegrable
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T02:39:13.315346+00:00
-- url     : https://prove2.me/theorems/d95e3838-f863-4f60-8956-ef3ce962499c
-- title:
--   Bessel Xi Integrable
-- statement:
--   Definitions and structural lemmas for Bessel Xi Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/BesselIntegrals/BesselXiIntegrable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.HCXi
def BesselXiIntegrable : Prop := Formalism.FourierDecayAlt.B.XiExists
end GlobalTheory.HCXi


