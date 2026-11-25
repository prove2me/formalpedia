-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieValCr
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:29:41.738539+00:00
-- url     : https://prove2.me/theorems/24e50a6b-d09d-5630-9f12-fbc143816dd7
-- title:
--   Row Tie Val Cr
-- statement:
--   Definitions and structural lemmas for Row Tie Val Cr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValCr.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValBr
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}
def mapAt (ε : Pt C 1 dd) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (ε i)
variable (Y : FBChart C V O dd)
end VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
end Formalism.L2.FormalSeriesBounds


