-- Prove2me | solution 1 for Auto.aux_CuboidNorm.raw_cuboid_jumpEnergy_eq_endpointEnergy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:48:40.898149+00:00
-- url     : https://prove2.me/submissions/30dd8d3a-6c8e-45b8-b0f2-8adabd97eb60

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_toLp_comp_eq

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
theorem _root_.solution {n J : ℕ}
    (N : Fin (J + 1) → ℕ) (a : Fin n → ZVector n → ℝ)
    (ε δ : ℝ) :
    (∑ j : Fin J, eLpNorm
      (fun x ↦ ctTwistedAverageAtScale (N j.succ : ℝ) ctUnitIntervalKernel
          (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
          (WithLp.toLp 2 x) -
        ctTwistedAverageAtScale (N j.castSucc : ℝ) ctUnitIntervalKernel
          (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i)))
          (WithLp.toLp 2 x)) 2 volume ^ 2) =
      ctEndpointEnergy J (fun q ↦ (N q : ℝ)) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i))) := by
  unfold ctEndpointEnergy
  apply Finset.sum_congr rfl
  intro j hj
  let H : ctRealVector n → ℝ := fun x ↦
    ctTwistedAverageAtScale (N j.succ : ℝ) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i))) x -
      ctTwistedAverageAtScale (N j.castSucc : ℝ) ctUnitIntervalKernel
        (fun i ↦ aux_liftRaw (aux_cuboidEmbed ε δ i (a i))) x
  change eLpNorm (fun x : RVector n ↦ H (WithLp.toLp 2 x)) 2 volume ^ 2 =
    eLpNorm H 2 volume ^ 2
  rw [eLpNorm_toLp_comp_eq H 2 (by norm_num) (by norm_num)]
end Auto.aux_CuboidNorm
