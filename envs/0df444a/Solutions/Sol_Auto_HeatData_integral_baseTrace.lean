-- Prove2me | solution 1 for Auto.HeatData.integral_baseTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:38:35.295141+00:00
-- url     : https://prove2.me/submissions/1cf425a4-8943-4ff4-bc05-55e7ff72eea4

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_plane_gaussD_three
public import Theorems.Thm_Auto_dexp_sum
public import Theorems.Thm_Auto_HeatData_baseTrace_eq

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Auto.HeatData
variable (Hd : HeatData ι)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 ≤ Hd.h) {m : ℕ} (hm : m = 3 ∨ m = 4) {s : ℝ} (hs : 0 < s) :
    Integrable (fun q : Fin 2 → ℝ => Hd.baseTrace m (planePt q) s) ∧ ∫ q : Fin 2 → ℝ,
      Hd.baseTrace m (planePt q) s = ((Hd.h ^ 3 * √s ^ m : ℝ) : ℂ) * ∑ i, ∑ j, ∑ k, Hd.A 0 i j *
      Hd.A 1 j k * Hd.A 2 k i * (gaussianD m (63 / 20 * s) (Hd.u i + Hd.u j + Hd.u k) : ℂ) := by
  have hq : (0 : ℝ) < 21 / 20 * s := by positivity
  have hpl : ∀ (i j k : ι), (fun q : Fin 2 → ℝ =>
      ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - planePt q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - planePt q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - planePt q 2) : ℝ) : ℂ)) =
      fun q => ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k + q 0 + q 1) : ℝ) : ℂ) := by
    intro i j k; funext q
    simp only [planePt, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    congr 3; ring
  have hint : ∀ i j k, Integrable (fun q : Fin 2 → ℝ => Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
      ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - planePt q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - planePt q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - planePt q 2) : ℝ) : ℂ)) := by
    intro i j k
    have := (plane_gaussD_three (dexp m 0) (dexp m 1) (dexp m 2) hq (Hd.u i) (Hd.u j)
      (Hd.u k)).1.const_mul (Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i)
    refine this.congr (Eventually.of_forall fun q => ?_)
    have h' := congrFun (hpl i j k) q
    simp only at h' ⊢
    rw [h']
  have hval : ∀ i j k, ∫ q : Fin 2 → ℝ, Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
      ((gaussianD (dexp m 0) (21 / 20 * s) (Hd.u i - planePt q 0) *
        gaussianD (dexp m 1) (21 / 20 * s) (Hd.u j - planePt q 1) *
        gaussianD (dexp m 2) (21 / 20 * s) (Hd.u k - planePt q 2) : ℝ) : ℂ) =
      Hd.A 0 i j * Hd.A 1 j k * Hd.A 2 k i *
        (gaussianD m (63 / 20 * s) (Hd.u i + Hd.u j + Hd.u k) : ℂ) := by
    intro i j k
    rw [integral_const_mul, hpl i j k, (plane_gaussD_three (dexp m 0) (dexp m 1) (dexp m 2) hq
      (Hd.u i) (Hd.u j) (Hd.u k)).2, dexp_sum hm,
      show 21 / 20 * s + 21 / 20 * s + 21 / 20 * s = 63 / 20 * s by ring]
  simp only [Hd.baseTrace_eq hh hm hs]
  refine ⟨(integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hint i j k).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hint i j k]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint i j k]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hint i j k]
  exact Finset.sum_congr rfl fun k _ => hval i j k
end Auto.HeatData
