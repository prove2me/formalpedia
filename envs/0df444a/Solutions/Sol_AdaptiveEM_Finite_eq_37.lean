-- Prove2me | solution 1 for AdaptiveEM.Finite.eq_37
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:43:06.333335+00:00
-- url     : https://prove2.me/submissions/5e95716a-26a4-43ea-8634-d57d29b66058

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Finite_KScheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

open AdaptiveEM.Finite EthierKurtz in
theorem solution {m d : ℕ} (f : SDEState m → SDEState m)
    (g : SDEState m → SabanisEuler.Shared.Diffusion m d) (h : SDEState m → ℝ)
    (α β : ℝ) (hA2 : Assumption2 f h α β) (K : ℝ) (hK : 0 < K)
    (x : SDEState m) (w : SDEState d) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτh : τ ≤ h x) :
    ‖PK K (x + τ • f x + mulVec (g x) w)‖ ^ 2 ≤
      ‖x‖ ^ 2 + 2 * α * ‖x‖ ^ 2 * τ + 2 * β * τ
        + 2 * ⟪x + τ • f x, mulVec (g x) w⟫ + ‖mulVec (g x) w‖ ^ 2 := by
  set y := x + τ • f x + mulVec (g x) w with hy
  have hPK : ‖PK K y‖ ≤ ‖y‖ := by
    unfold PK
    rw [norm_smul]
    have h0 : 0 ≤ min 1 (K / ‖y‖) := le_min zero_le_one (div_nonneg hK.le (norm_nonneg _))
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    calc min 1 (K / ‖y‖) * ‖y‖ ≤ 1 * ‖y‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
      _ = ‖y‖ := one_mul _
  have hsq : ‖PK K y‖ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hPK 2
  have e1 : ‖y‖ ^ 2 = ‖x + τ • f x‖ ^ 2 + 2 * ⟪x + τ • f x, mulVec (g x) w⟫ +
      ‖mulVec (g x) w‖ ^ 2 := by
    rw [hy, norm_add_sq_real]
  have e2 : ‖x + τ • f x‖ ^ 2 = ‖x‖ ^ 2 + 2 * (τ * ⟪x, f x⟫) + τ ^ 2 * ‖f x‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hA := hA2.2.2.2.2 x
  have : τ * (⟪x, f x⟫ + 1 / 2 * h x * ‖f x‖ ^ 2) ≤ τ * (α * ‖x‖ ^ 2 + β) :=
    mul_le_mul_of_nonneg_left hA hτ0
  have hτ2 : τ ^ 2 * ‖f x‖ ^ 2 ≤ τ * h x * ‖f x‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    rw [sq]
    exact mul_le_mul_of_nonneg_left hτh hτ0
  nlinarith
