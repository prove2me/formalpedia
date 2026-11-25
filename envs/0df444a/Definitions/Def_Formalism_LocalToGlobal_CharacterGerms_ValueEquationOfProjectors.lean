-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
-- name    : Formalism_LocalToGlobal_CharacterGerms_ValueEquationOfProjectors
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T10:19:42.998918+00:00
-- url     : https://prove2.me/theorems/dc7cdd12-7430-488d-a6b5-d2aa41243d50
-- title:
--   Value Equation Of Projectors
-- statement:
--   Definitions and structural lemmas for Value Equation Of Projectors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValueEquationOfProjectors.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoordinateChangeComp1IntertwinesAction
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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
variable (Y : FBChart C V O dd)
def exAt (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C := fun i => MvPowerSeries.subst a (e Y i)
end VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
def zePart (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (s : Orb × Fin 2) (m : Fin dd) : MvPowerSeries (WVO I) C :=
  ∑ c : I s.1 s.2, (p s.1).u s.2 c m • (MvPowerSeries.X (⟨s.1, ⟨s.2, c⟩⟩ : WVO I) : MvPowerSeries (WVO I) C)
end Formalism.L2.FormalSeriesBounds


