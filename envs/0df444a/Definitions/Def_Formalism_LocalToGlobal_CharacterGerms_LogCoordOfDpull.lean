-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
-- name    : Formalism_LocalToGlobal_CharacterGerms_LogCoordOfDpull
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:26:16.833578+00:00
-- url     : https://prove2.me/theorems/c116eb04-9b42-4a7f-8e17-739fbb8eca5a
-- title:
--   Log Coord Of Dpull
-- statement:
--   Definitions and structural lemmas for Log Coord Of Dpull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LogCoordOfDpull.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfLogUnitGerm
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
def DPullSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  ∀ (n : ℕ) (b : Fin n) (c : WVO I → C) (F : PS C n dd),
    pullN Y p (DofN (Y.B.FK C) b (fun i => ∑ w : WVO I, c w * (p w.1).u w.2.1 w.2.2 i) F) =
      ∑ w : WVO I, c w • MvPowerSeries.pderiv C (b, w) (pullN Y p F)
namespace VP
variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}
end VP
end Formalism.L2.FormalSeriesBounds


