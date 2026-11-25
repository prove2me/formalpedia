-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
-- name    : Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:00:51.2718+00:00
-- url     : https://prove2.me/theorems/ac2f8801-dbb2-4ac3-b7fe-a194bd8e876d
-- title:
--   Valuation Eq Pair Of Unit Germ
-- statement:
--   Definitions and structural lemmas for Valuation Eq Pair Of Unit Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValuationEqPairOfUnitGerm.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
namespace VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
variable (Y : FBChart C V O dd)
def l (m : Fin dd) : MvPowerSeries (Fin dd) C := un1 (Y.lg m)
def e (k : Fin dd) : MvPowerSeries (Fin dd) C := un1 (Y.ex k)
def J (m k : Fin dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv C k (l Y m))
end VP
end Formalism.L2.FormalSeriesBounds


