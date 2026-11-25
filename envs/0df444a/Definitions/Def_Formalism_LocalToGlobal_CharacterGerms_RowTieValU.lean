-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValU
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTieValU
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T08:47:29.698823+00:00
-- url     : https://prove2.me/theorems/0dfcae24-4f72-5e2f-be84-3283d2a3f36a
-- title:
--   Row Tie Val U
-- statement:
--   Definitions and structural lemmas for Row Tie Val U, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieValU.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieValL
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
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]
def IsIU (V : VF C) {σ : Type} (U : MvPowerSeries σ C) : Prop :=
  IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0
section Defs
variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))
structure IsProj (π : Orb → Fin 2 → Fin dd → PS C 1 dd) : Prop where
  int : ∀ o g i, IntS V (π o g i)
  cc : ∀ o g i, MvPowerSeries.constantCoeff (π o g i) = 0
  pull : ∀ o g i, pull1 Y p (π o g i) = toAllS o ((Y.raw (p o)).expPt g i)
def Aterm (π : Orb → Fin 2 → Fin dd → PS C 1 dd) (s s' : Orb × Fin 2) : PS C 1 dd :=
  FB.expS C ((Y.k : C) • ev (n := 1) ![π s.1 s.2, comp1 (Y.B.actK C Y.w0) (π s'.1 s'.2)] Y.h)
def barS (s : Orb × Fin 2) : Orb × Fin 2 := (s.1, 1 - s.2)
def BiaddSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∃ U : PS C 1 dd, IsIU V U ∧
    pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p U * ∏ s : Orb × Fin 2, ∏ s' : Orb × Fin 2, pull1 Y p (Aterm Y π s s')
def CrossSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ s s' : Orb × Fin 2, s' ≠ barS s →
    ∃ U : PS C 1 dd, IsIU V U ∧ pull1 Y p (Aterm Y π s s') = pull1 Y p U
def PairSt : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ o : Orb, ∃ U : PS C 1 dd, IsIU V U ∧
    pull1 Y p (Aterm Y π (o, 0) (o, 1)) * pull1 Y p (Aterm Y π (o, 1) (o, 0)) =
      pull1 Y p U * toAllS o (mvExp (Y.raw (p o)).hRow)
end Defs
end Formalism.L2.FormalSeriesBounds


