-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:30:28.461654+00:00
-- url     : https://prove2.me/theorems/e1731571-c70d-4f2b-9d44-0dcf439b6f63
-- title:
--   Le Weight Of Coeff Pow
-- statement:
--   Definitions and structural lemmas for Le Weight Of Coeff Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
namespace GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}
def mainTerm [Fintype κ] (l : ℕ) (c : C) : MvPowerSeries (κ ⊕ κ) C :=
  c • ∑ j, MvPowerSeries.X (Sum.inl j) ^ l * MvPowerSeries.X (Sum.inr j)
def mult (O : Subring C) (l : ℕ) : AddSubgroup C :=
  O.toAddSubgroup.map (AddMonoidHom.mulLeft (l : C))
def intRing (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    change 0 ≤ v (a * b)
    rw [v.map_mul]
    exact add_nonneg ha hb
  one_mem' := v.map_one.ge
  add_mem' ha hb := v.map_le_add ha hb
  zero_mem' := by
    change 0 ≤ v 0
    rw [v.map_zero]
    exact le_top
  neg_mem' {a} ha := by
    change 0 ≤ v (-a)
    rwa [v.map_neg]
def intBelow (O : Subring C) (m : σ →₀ ℕ) : Submonoid (MvPowerSeries σ C) where
  carrier := {F | ∀ p ≤ m, MvPowerSeries.coeff p F ∈ O}
  one_mem' p _ := by
    classical
    rw [MvPowerSeries.coeff_one]
    split_ifs
    exacts [O.one_mem, O.zero_mem]
  mul_mem' {F G} hF hG p hp := by
    classical
    rw [MvPowerSeries.coeff_mul]
    refine sum_mem fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    exact O.mul_mem (hF _ ((hx ▸ le_self_add).trans hp)) (hG _ ((hx ▸ le_add_self).trans hp))
end GlobalTheory.UnitCase


