-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_liftRaw_eq_any
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:02.89837+00:00
-- url     : https://prove2.me/submissions/6055560f-c280-49be-95f7-92f5a593281b

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_liftRaw_toLp

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
theorem _root_.solution {n : ℕ} (F : RVector n → ℝ)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (aux_liftRaw F) p volume = eLpNorm F p volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  congr 1
  have h := (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (fun x : ctRealVector n ↦ ‖aux_liftRaw F x‖ₑ ^ p.toReal)
  have hcomp : (fun x : Fin n → ℝ ↦
      ‖aux_liftRaw F (WithLp.toLp 2 x)‖ₑ ^ p.toReal) =
      fun x ↦ ‖F x‖ₑ ^ p.toReal := by
    funext x
    rw [aux_liftRaw_toLp]
  rw [hcomp] at h
  exact h.symm
end Auto.aux_CuboidNorm
