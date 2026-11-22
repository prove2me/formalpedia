-- Prove2me | solution 1 for Auto.norm_wGram_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:22:20.365042+00:00
-- url     : https://prove2.me/submissions/e0638268-9fd6-4adb-8718-e3af0cb54b78

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_wGram_apply

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
namespace Auto
theorem _root_.solution {κ : Type*} (B : Matrix ι κ ℂ) (f : ι → ℝ) {β γ : ℝ}
    (hB : ∀ i a, ‖B i a‖ ≤ β) (hf : ∀ i, |f i| ≤ γ) (a b : κ) :
    ‖wGram B f a b‖ ≤ Fintype.card ι * (β * γ * β) := by
  rw [wGram_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖star (B i a) * (f i : ℂ) * B i b‖ ≤ ∑ _i : ι, β * γ * β := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
        have hγ : 0 ≤ γ := (abs_nonneg _).trans (hf i)
        have hβ : 0 ≤ β := (norm_nonneg _).trans (hB i a)
        gcongr
        · exact hB i a
        · exact hf i
        · exact hB i b
    _ = _ := by simp
end Auto
