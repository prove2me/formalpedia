-- Prove2me | solution 1 for Auto.HeatData.plane_integral_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:32:24.374112+00:00
-- url     : https://prove2.me/submissions/683d018c-13ab-4db0-a601-291376ab93c9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_HeatData_fin3_ne_succ
public import Theorems.Thm_Auto_plane_integral_prod
public import Theorems.Thm_P2M_Auto_continuous_gaussian__66693ed17080
public import Theorems.Thm_Auto_integral_weight_line
public import Theorems.Thm_Auto_integrable_weight_line

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology Real
open Auto
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
omit [Fintype ι] [DecidableEq ι]
namespace Auto.HeatData
theorem _root_.solution (α : Fin 3 → ℝ) (hα : ∀ k, 0 < α k) {β s : ℝ} (hβ : 0 < β)
    (hs : 0 < s) (v : Fin 3) (i j : ι) :
    Integrable (fun p : Fin 3 → ℝ => Gm β 0 s p * (Hd.w p (HeatData.sig α s) v i * Hd.w p
      (HeatData.sig α s) (v + 1) j)) ∧ ∫ p : Fin 3 → ℝ, Gm β 0 s p * (Hd.w p (HeatData.sig α s) v
      i * Hd.w p (HeatData.sig α s) (v + 1) j) = Hd.h ^ 2 := by
  have hσ : ∀ k, 0 < HeatData.sig α s k := fun k => mul_pos (hα k) hs
  obtain ⟨hI, hV⟩ := plane_integral_prod (k := gaussian (β * s)) (f := fun t => Hd.h * gaussian
      (HeatData.sig α s v) (Hd.u i - t)) (g := fun t => Hd.h * gaussian (HeatData.sig α s (v + 1))
      (Hd.u j - t)) (continuous_gaussian' _) (continuous_const.mul ((continuous_gaussian' _).comp
      (continuous_const.sub continuous_id))) (continuous_const.mul ((continuous_gaussian' _).comp
      (continuous_const.sub continuous_id))) (integrable_gaussian' (mul_pos hβ hs))
      (integrable_weight_line _ _ _ (hσ v)) (integrable_weight_line _ _ _ (hσ _)) (fin3_ne_succ v)
  have hG : ∀ p, Gm β 0 s p = gaussian (β * s) (p 0 + p 1 + p 2) := fun p => by
    simp [Gm, gaussianD_zero]
  refine ⟨?_, ?_⟩
  · simp only [hG]; exact hI
  · simp only [hG]
    rw [show (fun p : Fin 3 → ℝ => gaussian (β * s) (p 0 + p 1 + p 2) * (Hd.w p (HeatData.sig α s) v
        i * Hd.w p (HeatData.sig α s) (v + 1) j)) =
        fun p => gaussian (β * s) (p 0 + p 1 + p 2) * ((fun t => Hd.h * gaussian (HeatData.sig α s
            v) (Hd.u i - t)) (p v) * (fun t => Hd.h * gaussian (HeatData.sig α s (v + 1)) (Hd.u j -
            t)) (p (v + 1)))
        from rfl, hV, integral_gaussian_eq_one (mul_pos hβ hs),
      integral_weight_line _ _ _ (hσ v), integral_weight_line _ _ _ (hσ _)]
    ring
end Auto.HeatData
