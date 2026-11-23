-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtCoeffSingleSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:22.21622+00:00
-- url     : https://prove2.me/theorems/8a194110-c315-40e7-947a-907f783b5e57
-- title:
--   Pt Coeff Single Subst
-- statement:
--   Definitions and structural lemmas for Pt Coeff Single Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/PtCoeffSingleSubst.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtOrderProdSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
section Int
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
def ptIntSub : Subring C where
  carrier := {x | 0 ≤ v x}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, v.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp [v.map_one]
  add_mem' {a b} ha hb := le_trans (le_min ha hb) (v.map_add _ _)
  zero_mem' := by simp [v.map_zero]
  neg_mem' {a} ha := by simpa [Set.mem_ofPred_eq, v.map_neg] using ha
def ptIntSer (σ : Type*) : Subring (MvPowerSeries σ C) where
  carrier := {f | ∀ α, coeff α f ∈ ptIntSub v}
  mul_mem' {f g} hf hg α := by
    rw [coeff_mul]
    exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hf _) (hg _)
  one_mem' α := by
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {f g} hf hg α := by rw [map_add]; exact Subring.add_mem _ (hf α) (hg α)
  zero_mem' α := by rw [map_zero]; exact Subring.zero_mem _
  neg_mem' {f} hf α := by rw [map_neg]; exact Subring.neg_mem _ (hf α)
variable {v}
end Int
section Lin
variable {R : Type*} [CommRing R]
end Lin
section Law
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
end Law
end
end ReciprocityTheory.ChartRestriction.G.Sh


