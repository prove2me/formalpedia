-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:56:49.591327+00:00
-- url     : https://prove2.me/theorems/5e9984a2-bc5e-4331-9709-dc910566431c
-- title:
--   Unfold Abs
-- statement:
--   Definitions and structural lemmas for Unfold Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabS
open MeasureTheory Set
open scoped ENNReal Pointwise
section Abs
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
instance subMeasurableMul (H : Subgroup G) : MeasurableMul H where
  measurable_const_mul c := by
    exact (((measurable_const_mul (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(c : G) * x, H.mul_mem c.2 x.2⟩ : H))
  measurable_mul_const c := by
    exact (((measurable_mul_const (c : G)).comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G) * c, H.mul_mem x.2 c.2⟩ : H))
instance subMeasurableInv (H : Subgroup G) : MeasurableInv H where
  measurable_inv := by
    exact ((measurable_inv.comp measurable_subtype_coe).subtype_mk :
      Measurable fun x : H => (⟨(x : G)⁻¹, H.inv_mem x.2⟩ : H))
variable [MulAction G Y]
def orbS (Γ : Subgroup G) (y0 : Y) : Set Y := {x | ∃ γ ∈ Γ, γ • y0 = x}
def repO (Γ : Subgroup G) (y0 : Y) (x : orbS Γ y0) : G :=
  Classical.choose (x.2 : ∃ γ ∈ Γ, γ • y0 = (x : Y))
def cntN (Γ : Subgroup G) (A : Set G) (g : G) : ℝ≥0∞ :=
  ∑' γ : Γ, A.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g)
def cfun (Γ : Subgroup G) (A : Set G) (y0 : Y) (g : G) : ℝ≥0∞ :=
  ∑' x : orbS Γ y0, A.indicator (fun _ => (1 : ℝ≥0∞)) (repO Γ y0 x * g⁻¹)
end Abs
end PI.VolStabS


