-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
-- name    : Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:30:43.041848+00:00
-- url     : https://prove2.me/theorems/27202f06-b7b4-4681-8522-23356dd300c5
-- title:
--   Exp SNeg Mul Exp S
-- statement:
--   Definitions and structural lemmas for Exp SNeg Mul Exp S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/ExpSNegMulExpS.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
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
namespace GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
section Lift
variable (k : Type) [CommRing k]
end Lift
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
end GlobalTheory.NablaExpConj


