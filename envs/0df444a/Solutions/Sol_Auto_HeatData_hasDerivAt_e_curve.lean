-- Prove2me | solution 1 for Auto.HeatData.hasDerivAt_e_curve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:18.689057+00:00
-- url     : https://prove2.me/submissions/7ab8fdb9-29a5-4c45-9887-8c28ca9cc5c9

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_hasDerivAt_energyReg
public import Theorems.Thm_Auto_hasDerivAt_wGram
public import Theorems.Thm_Auto_wGram_smul
public import Theorems.Thm_Auto_HeatData_tr32_add
public import Theorems.Thm_Auto_HeatData_tr32_smul
public import Theorems.Thm_Auto_HeatData_T_eq_DXD
public import Theorems.Thm_Auto_HeatData_rdiag_mul_mul_rdiag_apply
public import Theorems.Thm_Auto_HeatData_Mrow_eq
public import Theorems.Thm_Auto_HeatData_hasDerivAt_w_curve
public import Theorems.Thm_Auto_HeatData_hasDerivAt_sqw_curve

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
variable (Hd : HeatData ι) (p σ : Fin 3 → ℝ)
namespace Auto.HeatData
theorem _root_.solution (hh : 0 < Hd.h) {η : ℝ} (hη : 0 < η) {c : ℝ → Fin 3 → ℝ}
    {c' : Fin 3 → ℝ} {θ₀ : ℝ} (hc : ∀ k, HasDerivAt (fun θ => c θ k) (c' k) θ₀)
    (hσ : ∀ k, 0 < c θ₀ k) (v : Fin 3) :
    HasDerivAt (fun θ => Hd.e p (c θ) η v) (c' v * tr32 η (Hd.T p (c θ₀) v) (Hd.Mrow p (c θ₀) v)
      + c' (v + 1) * tr32 η (Hd.T p (c θ₀) v) (Hd.Mnext p (c θ₀) v) + c' (v - 1) * tr32 η (Hd.T p
      (c θ₀) v) (Hd.Mprev p (c θ₀) v)) θ₀ := by
  set σ₀ := c θ₀
  set P' : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ := (c' v : ℂ) • Hd.Mrow p σ₀ v + (c' (v + 1) : ℂ) • Hd.Mnext p
      σ₀ v + (c' (v - 1) : ℂ) • Hd.Mprev p σ₀ v
  have hT : ∀ θ, (Hd.T p (c θ) v).PosSemidef := fun θ =>
    Matrix.posSemidef_conjTranspose_mul_self _
  have hdv : ∀ a, HasDerivAt (fun θ => Hd.dv p (c θ) v a) (Sum.elim (fun i => c' (v + 1) * Hd.dsq p
      σ₀ (v + 1) i) (fun i => c' (v - 1) * Hd.dsq p σ₀ (v - 1) i) a) θ₀ := by
    rintro (i | i)
    · exact Hd.hasDerivAt_sqw_curve p hh hc hσ (v + 1) i
    · exact Hd.hasDerivAt_sqw_curve p hh hc hσ (v - 1) i
  have hX : ∀ a b, HasDerivAt (fun θ => Hd.X p (c θ) v a b) (wGram (rowMat (Hd.A v) (Hd.A (v - 1)))
      (fun i => c' v * (Hd.ddw p σ₀ v i / 2)) a b)
      θ₀ := fun a b =>
    hasDerivAt_wGram _ (f := fun θ => Hd.w p (c θ) v) (fun i => Hd.hasDerivAt_w_curve p hc hσ v i) a
        b
  have hd : ∀ a b, HasDerivAt (fun θ => Hd.T p (c θ) v a b) (P' a b) θ₀ := by
    intro a b
    have e1 : (fun θ => Hd.T p (c θ) v a b) = fun θ =>
        (Hd.dv p (c θ) v a : ℂ) * Hd.X p (c θ) v a b * (Hd.dv p (c θ) v b : ℂ) := by
      funext θ; rw [T_eq_DXD Hd p _ hh.le, rdiag_mul_mul_rdiag_apply]
    rw [e1]
    have := (((hdv a).ofReal_comp).fun_mul (hX a b)).fun_mul (hdv b).ofReal_comp
    convert this using 1 <;> try rfl
    have hw2 : (fun i => c' v * (Hd.ddw p σ₀ v i / 2)) = c' v • fun i => Hd.ddw p σ₀ v i / 2 := by
      funext i; simp
    simp only [P', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Mrow_eq, Mnext, Mprev,
      rdiag_mul_mul_rdiag_apply, hw2, wGram_smul]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [dv] <;> ring
  have hE := hasDerivAt_energyReg hη hT hd
  refine hE.congr_deriv ?_
  change tr32 η (Hd.T p σ₀ v) P' = _
  simp only [P', tr32_add, tr32_smul]
end Auto.HeatData
