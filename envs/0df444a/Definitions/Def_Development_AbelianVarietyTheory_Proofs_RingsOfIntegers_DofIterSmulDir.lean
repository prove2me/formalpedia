-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DofIterSmulDir
-- name    : Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DofIterSmulDir
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:11.420837+00:00
-- url     : https://prove2.me/theorems/03e06275-2b68-4196-9e1f-84fcf09367bf
-- title:
--   Dof Iter Smul Dir
-- statement:
--   Definitions and structural lemmas for Dof Iter Smul Dir, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DofIterSmulDir.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory.DirScale
variable {R : Type} [CommRing R] {d : ℕ}
end GlobalTheory.DirScale


