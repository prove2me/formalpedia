-- Prove2me | solution 1 for Autoconvolutions.Parameters.tendsto_geomRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:32.595816+00:00
-- url     : https://prove2.me/submissions/ce15656b-5063-4150-b46b-6f18a408143b

module
public import Definitions.Def_Autoconvolutions_Witness
public import Definitions.Def_Autoconvolutions_Coefficients
public import Definitions.Def_Autoconvolutions_GoodBlocks
public import Definitions.Def_Autoconvolutions_Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Definitions.Def_Autoconvolutions_Main

set_option autoImplicit true
@[expose] public section
public section
open Filter Finset Polynomial
open scoped BigOperators Topology
open Autoconvolutions Autoconvolutions.Parameters
namespace Autoconvolutions.Parameters
theorem _root_.solution {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto (geomRatio q) atTop (𝓝 q) := by
  have hnorm : ‖q‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hq₀]
  have hnum := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).tendsto_sum_nat
  have hden := (hasSum_geometric_of_lt_one hq₀.le hq₁).tendsto_sum_nat
  have hq : 1 - q ≠ 0 := (sub_pos.mpr hq₁).ne'
  have h := (hnum.div (hden.pow 2) (pow_ne_zero 2 (inv_ne_zero hq))).comp
    (tendsto_add_atTop_nat 1)
  have he : (q / (1 - q) ^ 2) / ((1 - q)⁻¹) ^ 2 = q := by field_simp
  rw [he] at h
  exact h
end Autoconvolutions.Parameters
