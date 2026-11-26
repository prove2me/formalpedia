-- Prove2me | solution 1 for Auto.aux_CuboidNorm.measurable_liftRaw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:41:03.836318+00:00
-- url     : https://prove2.me/submissions/9aaa4589-ffd1-46e9-b229-b674c4dfc3fb

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
theorem _root_.solution {n : ℕ} {F : RVector n → ℝ}
    (hF : Measurable F) :
    Measurable (aux_liftRaw F) := by
  change Measurable (F ∘ WithLp.ofLp)
  exact hF.comp (PiLp.volume_preserving_ofLp (ι := Fin n)).measurable
end Auto.aux_CuboidNorm
