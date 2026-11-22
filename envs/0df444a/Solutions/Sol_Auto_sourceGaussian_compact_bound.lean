-- Prove2me | solution 1 for Auto.sourceGaussian_compact_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:52:55.137566+00:00
-- url     : https://prove2.me/submissions/c5e38286-629b-44e1-b9fb-2b50cb997ca2

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_lattice_sampling_dominated_convergence
public import Theorems.Thm_Auto_sourceGaussian_lattice_bound
public import Theorems.Thm_Auto_exists_support_bound
public import Theorems.Thm_Auto_tendsto_lattice_norm_cube
public import Theorems.Thm_Auto_sourceGaussian_continuous
public import Theorems.Thm_Auto_sourceGaussian_support

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
theorem _root_.solution (F : Fin 3 → ℝ × ℝ → ℂ)
    (hc : ∀ v, Continuous (F v)) (hs : ∀ v, HasCompactSupport (F v))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ x, sourceGaussianIntegrand F a b x‖ ≤
      3 * heatBoundConstant * ∏ v, (∫ p, ‖F v p‖ ^ 3) ^ (1 / 3 : ℝ) := by
  classical
  choose ρ hρ hF using fun v => exists_support_bound (hs v)
  let R := ∑ v, ρ v
  have hv (v : Fin 3) : ρ v ≤ R :=
    Finset.single_le_sum (fun i _ => hρ i) (Finset.mem_univ v)
  have hR : 0 ≤ R := Finset.sum_nonneg fun v _ => hρ v
  have hsupp : ∀ v p, R < ‖p‖ → F v p = 0 :=
    fun v p hp => hF v p ((hv v).trans_lt hp)
  have hcomp : HasCompactSupport (sourceGaussianIntegrand F a b) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Fin 3 → ℝ) R)
      (fun x hx => sourceGaussian_support F hR hsupp x (by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))
  have hcont := sourceGaussian_continuous F hc ha hab
  have hlim := lattice_sampling_dominated_convergence
    (sourceGaussianIntegrand F a b)
    (hcont.bounded_above_of_compact_support hcomp)
    ⟨R, sourceGaussian_support F hR hsupp⟩ ∅ (fun x _ => hcont.continuousAt)
  have hnorm (v : Fin 3) := (tendsto_lattice_norm_cube (hc v) (hs v)).rpow_const
    (p := 1 / 3) (Or.inr (by norm_num))
  have hprod := (tendsto_finsetProd Finset.univ (fun v _ => hnorm v)).const_mul
    (3 * heatBoundConstant)
  refine le_of_tendsto_of_tendsto hlim.norm hprod ?_
  have hzero : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using h.pow 2
  filter_upwards [eventually_gt_atTop 0, hzero.eventually (ge_mem_nhds ha)]
    with N hN hNa
  exact sourceGaussian_lattice_bound F hR hsupp hN hNa hab
end Auto
