-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
-- name    : Formalism_LocalToGlobal_CharacterGerms_RowTiePHStab
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:58.835793+00:00
-- url     : https://prove2.me/theorems/0a642299-5c3e-4ff9-b9c5-270155280f41
-- title:
--   Row Tie PHStab
-- statement:
--   Definitions and structural lemmas for Row Tie PHStab, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHStab.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
section Coeff
variable {τ : Type}
def E2 (P Q : τ) : τ →₀ ℕ := Finsupp.single P 1 + Finsupp.single Q 1
end Coeff
section Subst
variable {τ κ : Type} [Fintype κ]
end Subst
section Exp
variable [CharZero C] {n dd : ℕ}
end Exp
section Bil
variable {dd : ℕ}
def Tg (dd : ℕ) (g : Fin 2) : Set (Fin 2 × Fin dd) := {s | s.1 = g}
def bil (F : PS C 2 dd) (w v : Fin dd → C) : C :=
  ∑ i, ∑ j, coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) F * (w i * v j)
variable {h : PS C 2 dd}
  (hh : ∀ (g : Fin 2) (e : Fin 2 × Fin dd →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0)
  {φ : Pt C 1 dd} (hφ : ∀ i, constantCoeff (φ i) = 0)
include hh hφ
end Bil
section Final
variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
end Final
end Formalism.L2.FormalSeriesBounds


