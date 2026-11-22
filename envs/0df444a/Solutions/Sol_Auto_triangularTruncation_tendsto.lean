-- Prove2me | solution 1 for Auto.triangularTruncation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:47:55.641037+00:00
-- url     : https://prove2.me/submissions/b93ceba1-c5e3-4db2-b157-5785b753f5dd

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_triangular_snd_ne_zero
public import Theorems.Thm_Auto_triangularTruncation_eq

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
public section
open scoped ENNReal NNReal
open MeasureTheory Filter Topology Real
public section
open Auto
open MeasureTheory Filter Topology Matrix Real
open scoped ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section
namespace Auto
theorem _root_.solution (H F G : SchwartzMap (ℝ × ℝ) ℂ) :
    Tendsto (triangularTruncation H F G) (𝓝[>] (0 : ℝ)) (𝓝 (triangularPV H F G)) := by
  have hi := triangularOddQuotient_integrable H F G
  have hc : Tendsto (fun ε : ℝ => ∫ q : (ℝ × ℝ) × ℝ,
      if ε < |q.2| then triangularOddQuotient H F G q else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q, triangularOddQuotient H F G q)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun q => ‖triangularOddQuotient H F G q‖)
    · filter_upwards [] with ε
      exact hi.aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const measurable_snd.abs)
    · filter_upwards [] with ε
      filter_upwards [] with q
      split_ifs <;> simp
    · exact hi.norm
    · filter_upwards [triangular_snd_ne_zero] with q hq
      have he : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < |q.2| :=
        (eventually_lt_nhds (abs_pos.mpr hq)).filter_mono nhdsWithin_le_nhds
      exact tendsto_const_nhds.congr' (he.mono fun ε hε => (if_pos hε).symm)
  apply (hc.const_mul (2 : ℂ)⁻¹).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (triangularTruncation_eq H F G hε).symm
end Auto
