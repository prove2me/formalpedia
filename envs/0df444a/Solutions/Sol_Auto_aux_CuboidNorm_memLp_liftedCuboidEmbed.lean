-- Prove2me | solution 1 for Auto.aux_CuboidNorm.memLp_liftedCuboidEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:52.862097+00:00
-- url     : https://prove2.me/submissions/6ee21ba7-e8ef-4faf-b37f-28940ab245c4

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_CuboidNorm_measurable_cuboidEmbed
public import Theorems.Thm_Auto_aux_CuboidNorm_memLp_cuboidEmbed
public import Theorems.Thm_Auto_aux_CuboidNorm_measurable_liftRaw
public import Theorems.Thm_Auto_aux_CuboidNorm_eLpNorm_liftRaw_eq

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
    (hsupport : ∀ k, k ∉ A → a k = 0) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    MemLp (aux_liftRaw (aux_cuboidEmbed ε δ i a)) p volume := by
  refine ⟨(measurable_liftRaw
    (measurable_cuboidEmbed hε0 hε hεδ i A a hsupport)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_liftRaw_eq _ p
    (measurable_cuboidEmbed hε0 hε hεδ i A a hsupport)]
  exact (memLp_cuboidEmbed hε0 hε hεδ i A a hsupport p hp0 hptop).2
end Auto.aux_CuboidNorm
