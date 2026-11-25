-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
-- name    : Formalism_LocalToGlobal_CharacterGerms_FirstPartialLawAtPoints
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:45:45.970239+00:00
-- url     : https://prove2.me/theorems/fa6cc023-faec-4d35-a709-645c07a366be
-- title:
--   First Partial Law At Points
-- statement:
--   Definitions and structural lemmas for First Partial Law At Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FirstPartialLawAtPoints.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValuationEqPairOfBiadditiveCross
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
section Three
variable {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
include ha hb hc
end Three
def GoodPt (V : VF C) (a : Fin dd → MvPowerSeries τ C) : Prop :=
  (∀ i, MvPowerSeries.constantCoeff (a i) = 0) ∧ ∀ i, IntS V (a i)
def sumL : List (Fin dd → MvPowerSeries τ C) → (Fin dd → MvPowerSeries τ C)
  | [] => fun _ => 0
  | a :: l => addAt Y a (sumL l)
end VP
end Formalism.L2.FormalSeriesBounds


