-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_PushMemHarmK
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:04:57.914662+00:00
-- url     : https://prove2.me/theorems/81542999-3d8f-45a2-bb50-a5d835fd7001
-- title:
--   Push Mem Harm K
-- statement:
--   Definitions and structural lemmas for Push Mem Harm K, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/PushMemHarmK.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_UnitaryDetClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PushHarm
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDetClass
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n : ℕ}
end GlobalTheory.PushHarm


