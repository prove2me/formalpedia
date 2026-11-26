-- Prove2me | solution 1 for Auto.aux_CuboidNorm.eLpNorm_liftRaw_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:42:18.104353+00:00
-- url     : https://prove2.me/submissions/4be6d490-3c29-4350-9c80-1f123016614c

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_liftRaw_toLp
public import Theorems.Thm_Auto_aux_CuboidNorm_measurable_liftRaw

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
    (p : ℝ≥0∞) (hF : Measurable F) :
    eLpNorm (aux_liftRaw F) p volume = eLpNorm F p volume := by
  have h := eLpNorm_comp_measurePreserving (p := p)
    (measurable_liftRaw hF).aestronglyMeasurable
    (PiLp.volume_preserving_toLp (Fin n))
  have hcomp : aux_liftRaw F ∘ WithLp.toLp 2 = F := by
    funext x
    exact aux_liftRaw_toLp F x
  rw [hcomp] at h
  exact h.symm
end Auto.aux_CuboidNorm
