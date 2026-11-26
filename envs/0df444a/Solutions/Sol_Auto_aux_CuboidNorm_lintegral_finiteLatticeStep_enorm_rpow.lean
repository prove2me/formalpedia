-- Prove2me | solution 1 for Auto.aux_CuboidNorm.lintegral_finiteLatticeStep_enorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:49:46.824818+00:00
-- url     : https://prove2.me/submissions/879de749-d5f6-41b6-812b-1826d16bfd9b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_latticeAxisCuboid_pairwise_disjoint
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteStep_enorm_rpow
public import Theorems.Thm_Auto_aux_CuboidNorm_measurableSet_latticeAxisCuboid

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
    {ε δ : ℝ} (hε : ε ≤ 1) (hδ : δ ≤ 1) (i : Fin n)
    (A : Finset (ZVector n)) (a : ZVector n → ℝ) (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ‖finiteLatticeStep ε δ i A a x‖ₑ ^ q ∂volume) =
      ∑ k ∈ A, ‖a k‖ₑ ^ q * volume (latticeAxisCuboid ε δ i k) := by
  apply lintegral_finiteStep_enorm_rpow volume A
    (latticeAxisCuboid ε δ i) a q hq
  · intro k hk
    exact measurableSet_latticeAxisCuboid ε δ i k
  · intro k hk l hl hkl
    exact latticeAxisCuboid_pairwise_disjoint hε hδ i hkl
end Auto.aux_CuboidNorm
