-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_toLp_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:47:43.143301+00:00
-- url     : https://prove2.me/submissions/236babf3-4791-4004-8eca-3214c783f4b3

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference

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
theorem _root_.solution {n : ℕ} {E : Type*}
    [TopologicalSpace E] [ENorm E] (F : ctRealVector n → E)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (fun x : RVector n ↦ F (WithLp.toLp 2 x)) p volume =
      eLpNorm F p volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
  congr 1
  exact (PiLp.volume_preserving_toLp (Fin n)).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
    (fun x ↦ ‖F x‖ₑ ^ p.toReal)
end Auto.aux_CuboidNorm
