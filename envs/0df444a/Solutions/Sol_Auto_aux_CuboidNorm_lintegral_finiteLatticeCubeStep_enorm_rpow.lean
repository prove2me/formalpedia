-- Prove2me | solution 1 for Auto.aux_CuboidNorm.lintegral_finiteLatticeCubeStep_enorm_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:49:48.529728+00:00
-- url     : https://prove2.me/submissions/39903601-ee08-4671-b987-837fd2969632

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_lintegral_finiteStep_enorm_rpow
public import Theorems.Thm_Auto_aux_CuboidNorm_measurableSet_latticeCuboid
public import Theorems.Thm_Auto_aux_CuboidNorm_latticeCuboid_pairwise_disjoint

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
    {ε : ℝ} (hε : ε ≤ 1) (A : Finset (ZVector n)) (a : ZVector n → ℝ)
    (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ‖finiteLatticeCubeStep ε A a x‖ₑ ^ q ∂volume) =
      ∑ k ∈ A, ‖a k‖ₑ ^ q * volume (latticeCuboid ε k) := by
  apply lintegral_finiteStep_enorm_rpow volume A (latticeCuboid ε) a q hq
  · intro k hk
    exact measurableSet_latticeCuboid ε k
  · intro k hk l hl hkl
    exact latticeCuboid_pairwise_disjoint hε hkl
end Auto.aux_CuboidNorm
