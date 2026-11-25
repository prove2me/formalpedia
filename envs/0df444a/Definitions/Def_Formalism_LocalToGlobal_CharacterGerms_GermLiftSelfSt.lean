-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
-- name    : Formalism_LocalToGlobal_CharacterGerms_GermLiftSelfSt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:26.990237+00:00
-- url     : https://prove2.me/theorems/fe0e5431-96ba-5fd3-9d1e-985daf6ace7b
-- title:
--   Germ Lift Self St
-- statement:
--   Definitions and structural lemmas for Germ Lift Self St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/GermLiftSelfSt.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValG
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_mvExp

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
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]
abbrev IS (I0 : Orb → Type) : Orb → Fin 2 → Type := fun o _ => I0 o
section Defs
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))
def uS (w : WVO (IS I0)) : Fin 2 × Fin dd → C := (Y.rawSelf (p w.1)).u w.2.1 w.2.2
def pull2 (F : PS C 2 dd) : MvPowerSeries (WVO (IS I0)) C := VP.linPull Y (uS Y p) F
def MS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (x : Fin N × WVO (IS I0)) (q : Fin n × Fin dd) : C :=
  ∑ col : Fin 2, if pl (x.1, col) = q.1 then uS Y p x.2 (col, q.2) else 0
def pullS {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (F : PS C n dd) : MvPowerSeries (Fin N × WVO (IS I0)) C :=
  VP.linPull Y (MS Y p pl) F
def UnitSelfSt : Prop :=
  SelfSep Y p → ∃ U : PS C 2 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)
def GermLiftSelfSt (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g))
    (t : ∀ _ : Fin 2, I0 o → MvPowerSeries (I0 o) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 2 dd, IntS V G ∧ pull2 Y p G = toAllS (I := IS I0) o F
end Defs
namespace VP
variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)
end VP
end Formalism.L2.FormalSeriesBounds


