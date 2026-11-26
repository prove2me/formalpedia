-- Prove2me | solution 1 for Auto.aux_CuboidNorm.measurable_cuboidEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:49:22.224686+00:00
-- url     : https://prove2.me/submissions/db48d0b9-3787-4d62-b071-bfbce301251f

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_measurableSet_latticeAxisCuboid
public import Theorems.Thm_Auto_aux_CuboidNorm_cuboidEmbed_eq_finiteLatticeStep_apply

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]
namespace Auto.aux_CuboidNorm
theorem _root_.solution {n : ℕ}
    {ε δ : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1) (hεδ : ε + δ < 1)
    (i : Fin n) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (hsupport : ∀ k, k ∉ A → a k = 0) :
    Measurable (aux_cuboidEmbed ε δ i a) := by
  have hEq : aux_cuboidEmbed ε δ i a = finiteLatticeStep ε δ i A a := by
    funext y
    exact cuboidEmbed_eq_finiteLatticeStep_apply hε0 hε hεδ i A a hsupport y
  rw [hEq]
  unfold finiteLatticeStep finiteStep
  apply Finset.measurable_sum A
  intro k hk
  exact measurable_const.indicator (measurableSet_latticeAxisCuboid ε δ i k)
end Auto.aux_CuboidNorm
