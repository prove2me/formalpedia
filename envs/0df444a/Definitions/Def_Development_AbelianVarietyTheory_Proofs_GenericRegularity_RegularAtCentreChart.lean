-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentreChart
-- name    : Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentreChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:39.343635+00:00
-- url     : https://prove2.me/theorems/6a37a7f0-3310-4c5c-b121-0921c58ff4ba
-- title:
--   Regular At Centre Chart
-- statement:
--   Definitions and structural lemmas for Regular At Centre Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentreChart.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Reg.Transfer
open IsLocalRing NumberField IsDedekindDomain Formalism.L2.Pj Formalism.L2.PjFree ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Reg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
end GlobalTheory.Reg.Transfer


