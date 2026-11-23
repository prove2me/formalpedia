-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBtOfTangentOfSeries
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvBtOfTangentOfSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:36.769046+00:00
-- url     : https://prove2.me/theorems/91a25452-06a2-40c8-b840-e5d2c846c19b
-- title:
--   Ev Bt Of Tangent Of Series
-- statement:
--   Definitions and structural lemmas for Ev Bt Of Tangent Of Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvBtOfTangentOfSeries.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvBtStatement
import Definitions.Def_ReciprocityTheory_DualLattices_WFrobStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PSerFrobStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
namespace GlobalTheory
namespace BtAssembly
variable {R₀ : Type} [CommRing R₀]
end BtAssembly
end GlobalTheory


