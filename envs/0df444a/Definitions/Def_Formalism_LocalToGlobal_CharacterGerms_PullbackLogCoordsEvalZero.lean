-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
-- name    : Formalism_LocalToGlobal_CharacterGerms_PullbackLogCoordsEvalZero
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:41:59.366017+00:00
-- url     : https://prove2.me/theorems/571f183c-1aff-499d-b963-1d26a4345f04
-- title:
--   Pullback Log Coords Eval Zero
-- statement:
--   Definitions and structural lemmas for Pullback Log Coords Eval Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/PullbackLogCoordsEvalZero.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
def exZero (Y : FBChart C V O dd) : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C :=
  fun q => if q.1 = 0 then un1 (Y.ex q.2) else 0
def ExpODESt (Y : FBChart C V O dd) : Prop :=
  ∀ i j : Fin dd, MvPowerSeries.pderiv C i (un1 (Y.ex j)) =
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv C ((1 : Fin 2), i) (Y.B.FK C j))
namespace VP
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))
def Mu : WVO I → Fin dd → C := fun w i => (p w.1).u w.2.1 w.2.2 i
end VP
end Formalism.L2.FormalSeriesBounds


