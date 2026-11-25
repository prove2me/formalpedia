-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieValG
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T08:11:27.789071+00:00
-- url     : https://prove2.me/theorems/386fcdce-cf9a-5acb-839d-54947fa6b294
-- title:
--   Row Tie Val G
-- statement:
--   Definitions and structural lemmas for Row Tie Val G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValG.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfUnitGerm
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
  {Var : Type} [Fintype Var] {n : ℕ}
def colLin (M : Var → Fin n × Fin dd → C) (b : Fin n) : Var → Fin dd → C := fun x i => M x (b, i)
variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)
def linPt (q : Fin n × Fin dd) : MvPowerSeries Var C := MvPowerSeries.subst (linS (colLin M q.1)) (e Y q.2)
def linPull (F : PS C n dd) : MvPowerSeries Var C := MvPowerSeries.subst (linPt Y M) F
def RR (b : Fin n) (i j : Fin dd) : MvPowerSeries Var C :=
  linPull Y M (ev (n := n) ![pt C dd b, 0] (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j)))
end VP
end Formalism.L2.FormalSeriesBounds


