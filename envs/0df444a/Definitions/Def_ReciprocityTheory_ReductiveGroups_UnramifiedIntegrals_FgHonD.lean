-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
-- name    : ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonD
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T22:06:47.116745+00:00
-- url     : https://prove2.me/theorems/99a709f6-93f8-4a9f-8488-a20e56784d6f
-- title:
--   Fg Hon D
-- statement:
--   Definitions and structural lemmas for Fg Hon D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/FgHonD.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgHonC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
section Tools
variable {R : Type} [CommRing R]
end Tools
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ} {σ : K →+* K}
variable {lam : PowerSeries K} {Φ : MvPowerSeries (Fin 2) K} {A : PowerSeries K} {a : K}
theorem LawD.map (hF : FrobField K l σ) (h : LawD lam Φ) :
    LawD (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.lam0,
      map_zero]
  · rw [coeff_map, h.lam1, map_one]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h.Φ0, map_zero]
  · have h1 := h.Φint
    unfold IntegralMv at h1 ⊢
    intro e
    rw [MvPowerSeries.coeff_map, hF.isom]
    exact h1 e
  · have h1 := congrArg (MvPowerSeries.map σ) h.log
    unfold atX atY at h1 ⊢
    rw [map_add] at h1
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.Φ0),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 0)),
      PowerSeries.map_subst (HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X 1)),
      MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
    exact h1
theorem HD.map (hF : FrobField K l σ) (h : HD σ lam Φ A a) :
    HD σ (PowerSeries.map σ lam) (MvPowerSeries.map σ Φ) (PowerSeries.map σ A) (σ a) := by
  refine ⟨h.toLawD.map hF, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h.A0,
      map_zero]
  · have h1 := h.Aint
    unfold IntegralPS at h1 ⊢
    intro n
    rw [coeff_map, hF.isom]
    exact h1 n
  · have h1 := congrArg (PowerSeries.map σ) h.Alog
    erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero h.A0)] at h1
    rw [map_mul, map_C] at h1
    exact h1
  · rw [h.a_sq, norm_sub_rev]
    exact h.a_ne
  · rw [h.a_sq]
end ReciprocityTheory.ChartRestriction.L1


