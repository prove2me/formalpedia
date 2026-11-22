-- Prove2me | solution 1 for Auto.cyc_sq_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:50:36.252732+00:00
-- url     : https://prove2.me/submissions/65f8d11e-d443-4dd2-83ff-9fb75a877adc

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_blk3_mul
public import Theorems.Thm_Auto_blk3_one
public import Theorems.Thm_Auto_blk3_diag_eq
public import Theorems.Thm_Auto_blk3_smul

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (W0 W1 W2 D0 D1 D2 : Matrix ι ι ℂ)
namespace Auto
theorem _root_.solution {d : ℝ} (h0 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D0 * D0).PosSemidef)
    (h1 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D1 * D1).PosSemidef)
    (h2 : ((d ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - D2 * D2).PosSemidef) :
    ((d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) - blk3 (cycDb D0 D1 D2) * blk3 (cycDb
      D0 D1 D2)).PosSemidef := by
  have e : (d ^ 2 : ℝ) • (1 : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) -
      blk3 (cycDb D0 D1 D2) * blk3 (cycDb D0 D1 D2) =
      blk3 !![(d ^ 2 : ℝ) • 1 - D0 * D0, 0, 0; 0, (d ^ 2 : ℝ) • 1 - D1 * D1, 0;
        0, 0, (d ^ 2 : ℝ) • 1 - D2 * D2] := by
    rw [← blk3_mul, ← blk3_one, show ((d ^ 2 : ℝ) • blk3 (1 : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ))
        : Matrix (Fin 3 × ι) (Fin 3 × ι) ℂ) = blk3 (((d ^ 2 : ℝ) : ℂ) • 1) by
        rw [blk3_smul]; rfl]
    have sub (X Y : Matrix (Fin 3) (Fin 3) (Matrix ι ι ℂ)) :
        blk3 X - blk3 Y = blk3 (X - Y) :=
      ((Matrix.compRingEquiv (Fin 3) ι ℂ).map_sub X Y).symm
    rw [sub]
    congr 1
    apply Matrix.ext
    intro v w
    fin_cases v <;> fin_cases w <;>
      simp [cycDb, Matrix.mul_fin_three, Matrix.one_fin_three,
        Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]
    all_goals
      ext a b
      simp [Matrix.smul_apply, Complex.real_smul]
  rw [e, blk3_diag_eq]
  refine ((h0.mul_mul_conjTranspose_same _).add (h1.mul_mul_conjTranspose_same _)).add
      (h2.mul_mul_conjTranspose_same _)
end Auto
