-- Prove2me | solution 1 for ALAVI.eq_43
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T20:49:07.933439+00:00
-- url     : https://prove2.me/submissions/7179b42f-6550-4d59-87c2-7690ffb164f2

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_solutionSet
import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_ALAVI_Standing
import Definitions.Def_ALAVI_Params
import Definitions.Def_ALAVI_IsALAVIRun
import Theorems.Thm_CalamaiMore_Convergence_proj_properties

open ALAVI
theorem solution {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (U : Set E) (C : ProperCone ℝ F) (G : E → E) (J : E → EReal) (Θ : E → F) (L τ η α γ : ℝ) (v u : ℕ → E) (p q : ℕ → F)
    (hA : Standing U C G J Θ L τ) (hP : Params η α γ L τ)
    (hrun : IsALAVIRun U C G J Θ η α γ v u p q)
    (k : ℕ) (hk : 2 ≤ k) (hk1 : u (k - 1) ∈ U) :
    inner ℝ (q k - q (k - 1)) (Θ (u k) - Θ (u (k + 1))) ≤
        ‖q k - q (k - 1)‖ * (τ * ‖u k - u (k + 1)‖) ∧
      ‖q k - q (k - 1)‖ * (τ * ‖u k - u (k + 1)‖) ≤
        (‖p (k - 1) - p k‖ + γ * τ * ‖u (k - 1) - u k‖) * (τ * ‖u k - u (k + 1)‖) ∧
      (‖p (k - 1) - p k‖ + γ * τ * ‖u (k - 1) - u k‖) * (τ * ‖u k - u (k + 1)‖) ≤
        τ / 2 * ‖p (k - 1) - p k‖ ^ 2 + γ * τ ^ 2 / 2 * ‖u (k - 1) - u k‖ ^ 2 +
          (γ * τ ^ 2 + τ) / 2 * ‖u k - u (k + 1)‖ ^ 2 := by
  have hτ : 0 < τ := hA.2.2.2.2.2.2.1
  have hΘLip : ∀ a ∈ U, ∀ b ∈ U, ‖Θ a - Θ b‖ ≤ τ * ‖a - b‖ := hA.2.2.2.2.2.2.2
  have hγ : 0 < γ := hP.2.2.1
  have hr_km1 := hrun (k - 1) (by omega)
  have hr_k := hrun k (by omega)
  have hk_eq : k - 1 + 1 = k := by omega
  have huk : u k ∈ U := by simpa [hk_eq] using hr_km1.2.2.1.1
  have huk1 : u (k + 1) ∈ U := hr_k.2.2.1.1
  have hlink1 : inner ℝ (q k - q (k - 1)) (Θ (u k) - Θ (u (k + 1))) ≤
      ‖q k - q (k - 1)‖ * (τ * ‖u k - u (k + 1)‖) := by
    calc inner ℝ (q k - q (k - 1)) (Θ (u k) - Θ (u (k + 1)))
        ≤ ‖q k - q (k - 1)‖ * ‖Θ (u k) - Θ (u (k + 1))‖ := real_inner_le_norm _ _
      _ ≤ ‖q k - q (k - 1)‖ * (τ * ‖u k - u (k + 1)‖) :=
          mul_le_mul_of_nonneg_left (hΘLip (u k) huk (u (k + 1)) huk1) (norm_nonneg _)
  have hlink2 : ‖q k - q (k - 1)‖ * (τ * ‖u k - u (k + 1)‖) ≤
      (‖p (k - 1) - p k‖ + γ * τ * ‖u (k - 1) - u k‖) * (τ * ‖u k - u (k + 1)‖) := by
    let Cstar : ProperCone ℝ F := ProperCone.innerDual (C : Set F)
    have hnonexp := (CalamaiMore.Convergence.proj_properties (Cstar : Set F)
      Cstar.nonempty Cstar.isClosed Cstar.convex).2.2
      (p (k - 1) + γ • Θ (u (k - 1))) (p k + γ • Θ (u k))
    have hq_diff : ‖q k - q (k - 1)‖ ≤ ‖p (k - 1) - p k‖ + γ * τ * ‖u (k - 1) - u k‖ := by
      rw [hr_k.2.1, hr_km1.2.1]
      have hsub : (p k + γ • Θ (u k)) - (p (k - 1) + γ • Θ (u (k - 1))) =
          (p k - p (k - 1)) + γ • (Θ (u k) - Θ (u (k - 1))) := by
        rw [smul_sub]
        abel
      calc ‖CalamaiMore.Convergence.proj (Cstar : Set F) (p k + γ • Θ (u k)) -
              CalamaiMore.Convergence.proj (Cstar : Set F) (p (k - 1) + γ • Θ (u (k - 1)))‖
          ≤ ‖(p k + γ • Θ (u k)) - (p (k - 1) + γ • Θ (u (k - 1)))‖ := hnonexp
        _ = ‖(p k - p (k - 1)) + γ • (Θ (u k) - Θ (u (k - 1)))‖ := by rw [hsub]
        _ ≤ ‖p k - p (k - 1)‖ + ‖γ • (Θ (u k) - Θ (u (k - 1)))‖ := norm_add_le _ _
        _ = ‖p (k - 1) - p k‖ + γ * ‖Θ (u (k - 1)) - Θ (u k)‖ := by
            rw [norm_sub_rev (p k), norm_smul, Real.norm_of_nonneg hγ.le, norm_sub_rev (Θ (u k))]
        _ ≤ ‖p (k - 1) - p k‖ + γ * (τ * ‖u (k - 1) - u k‖) := by
            linarith [mul_le_mul_of_nonneg_left (hΘLip (u (k - 1)) hk1 (u k) huk) hγ.le]
        _ = ‖p (k - 1) - p k‖ + γ * τ * ‖u (k - 1) - u k‖ := by ring
    exact mul_le_mul_of_nonneg_right hq_diff (mul_nonneg hτ.le (norm_nonneg _))
  have hlink3 : (‖p (k - 1) - p k‖ + γ * τ * ‖u (k - 1) - u k‖) * (τ * ‖u k - u (k + 1)‖) ≤
      τ / 2 * ‖p (k - 1) - p k‖ ^ 2 + γ * τ ^ 2 / 2 * ‖u (k - 1) - u k‖ ^ 2 +
        (γ * τ ^ 2 + τ) / 2 * ‖u k - u (k + 1)‖ ^ 2 := by
    set A := ‖p (k - 1) - p k‖
    set B := ‖u (k - 1) - u k‖
    set D := ‖u k - u (k + 1)‖
    have hsq1 : 0 ≤ τ / 2 * (A - D) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hsq2 : 0 ≤ γ * τ ^ 2 / 2 * (B - D) ^ 2 :=
      mul_nonneg (div_nonneg (mul_nonneg hγ.le (sq_nonneg _)) (by norm_num)) (sq_nonneg _)
    have hid : τ / 2 * A ^ 2 + γ * τ ^ 2 / 2 * B ^ 2 + (γ * τ ^ 2 + τ) / 2 * D ^ 2 -
        (A + γ * τ * B) * (τ * D) = τ / 2 * (A - D) ^ 2 + γ * τ ^ 2 / 2 * (B - D) ^ 2 := by ring
    linarith
  exact ⟨hlink1, hlink2, hlink3⟩
