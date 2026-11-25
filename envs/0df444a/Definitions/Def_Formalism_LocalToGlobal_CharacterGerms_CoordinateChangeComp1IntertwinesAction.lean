-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
-- name    : Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:10:57.219712+00:00
-- url     : https://prove2.me/theorems/05f65862-844a-531f-81c2-ae3495e316f0
-- title:
--   Coordinate Change Comp1 Intertwines Action
-- statement:
--   Definitions and structural lemmas for Coordinate Change Comp1 Intertwines Action, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/CoordinateChangeComp1IntertwinesAction.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
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
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}
variable (Y : FBChart C V O dd)
end VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
def projList (π : Orb → Fin 2 → Fin dd → PS C 1 dd) : List (Fin dd → PS C 1 dd) :=
  (Finset.univ : Finset (Orb × Fin 2)).toList.map fun s => π s.1 s.2
def SumProjSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ i, pull1 Y p (pt C dd (0 : Fin 1) i) = pull1 Y p (VP.sumL Y (projList π) i)
end Formalism.L2.FormalSeriesBounds


