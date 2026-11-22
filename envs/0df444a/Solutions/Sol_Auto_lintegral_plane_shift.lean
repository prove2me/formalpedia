-- Prove2me | solution 1 for Auto.lintegral_plane_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:36:33.618294+00:00
-- url     : https://prove2.me/submissions/a6505b2c-fc37-4ca0-9479-b381bf6dbbc8

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_shiftMat_mulVec
public import Theorems.Thm_Auto_det_shiftMat

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
open Auto
noncomputable section
namespace Auto
theorem _root_.solution (v : Fin 3) {F : (Fin 3 → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ q : Fin 2 → ℝ, ∫⁻ d, F (Function.update (planePt q) v (planePt q v + d)) = ∫⁻ p, F p := by
  set L := Matrix.toLin' (shiftMat v)
  have hdet : (shiftMat v).det ≠ 0 := by rw [det_shiftMat]; norm_num
  have hmap : Measure.map L volume = (volume : Measure (Fin 3 → ℝ)) := by
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hdet, det_shiftMat]; simp
  have hLm : Measurable L := (LinearMap.continuous_on_pi L).measurable
  rw [← hmap, lintegral_map hF hLm]
  simp only [L, Matrix.toLin'_apply, shiftMat_mulVec]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have hmp : MeasurePreserving e.symm ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))
      volume := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
  set G : (Fin 3 → ℝ) → ℝ≥0∞ := fun x =>
    F (Function.update (planePt ![x 0, x 1]) v (planePt ![x 0, x 1] v + x 2))
  have hG : Measurable G := by
    refine hF.comp ?_
    have : (fun x : Fin 3 → ℝ => Function.update (planePt ![x 0, x 1]) v
        (planePt ![x 0, x 1] v + x 2)) = fun x => shiftMat v *ᵥ x := by
      funext x; rw [shiftMat_mulVec]
    rw [this]
    exact (Matrix.toLin' (shiftMat v)).continuous_on_pi.measurable
  change ∫⁻ q : Fin 2 → ℝ, ∫⁻ d, F (Function.update (planePt q) v (planePt q v + d)) = ∫⁻ x, G x
  rw [← hmp.lintegral_comp hG,
    lintegral_prod_symm (fun z => G (e.symm z)) (hG.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun q => lintegral_congr fun d => ?_
  simp only [G]
  have h0 : e.symm (d, q) 0 = q 0 := rfl
  have h1 : e.symm (d, q) 1 = q 1 := rfl
  have h2 : e.symm (d, q) 2 = d := rfl
  rw [h0, h1, h2]
  congr 3; ext i; fin_cases i <;> rfl
end Auto
