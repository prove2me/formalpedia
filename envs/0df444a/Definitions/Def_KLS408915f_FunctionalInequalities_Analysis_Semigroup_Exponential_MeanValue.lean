-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:15:45.322992+00:00
-- url     : https://prove2.me/theorems/52dbf4a0-c76a-467c-b485-cad7ef517adc
-- title:
--   Mean-value estimate for an exponential orbit
-- statement:
--   `hasDerivAt_exp_neg_smul_path` gives the derivative of $\sigma\mapsto\exp(-\sigma A)f-f+\sigma Af$ as $-\exp(-\sigma A)(Af)+Af$. Consequently, if $A$ is a bounded operator on a complete real normed space, $t\ge0$, and $\|\exp(-\tau A)(Af)-Af\|\le C$ for every $\tau\in[0,t]$, then `norm_exp_neg_smul_sub_add_smul_le` gives $\|\exp(-tA)f-f+tAf\|\le Ct$. No inner-product, positivity, or symmetry assumption is required.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Exponential/MeanValue.lean#L64-L115 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Exponential.MeanValue`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_MeanValue`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
section MeanValue
variable {H₀ : Type*} [NormedAddCommGroup H₀] [NormedSpace ℝ H₀] [CompleteSpace H₀]
/-- The path `σ ↦ exp (-σ • A) f - f + σ • A f` used in the exponential mean-value bound is differentiable, with derivative
`-(exp (-τ • A) (A f)) + A f`.

This is `hasDerivAt_exp_smul_const` for the operator `-A`, evaluated at the fixed vector `f`,
plus the derivative `A f` of the linear term; the constant `-f` contributes nothing. -/
theorem hasDerivAt_exp_neg_smul_path (A : H₀ →L[ℝ] H₀) (f : H₀) (τ : ℝ) :
    HasDerivAt (fun σ : ℝ => NormedSpace.exp (-σ • A) f - f + σ • A f)
      (-(NormedSpace.exp (-τ • A) (A f)) + A f) τ := by
  have hswap : ∀ σ : ℝ, NormedSpace.exp (-σ • A) = NormedSpace.exp (σ • (-A)) := by
    intro σ
    rw [neg_smul, ← smul_neg]
  have hfun : (fun σ : ℝ => NormedSpace.exp (-σ • A) f - f + σ • A f) =
      fun σ : ℝ => NormedSpace.exp (σ • (-A)) f - f + σ • A f := by
    funext σ
    rw [hswap]
  have hc : HasDerivAt (fun σ : ℝ => NormedSpace.exp (σ • (-A)))
      (NormedSpace.exp (τ • (-A)) * (-A)) τ := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) τ
  have hu : HasDerivAt (fun σ : ℝ => NormedSpace.exp (σ • (-A)) f)
      (-(NormedSpace.exp (τ • (-A)) (A f))) τ := by
    have h := hc.clm_apply (hasDerivAt_const τ f)
    simpa using h
  have hs : HasDerivAt (fun σ : ℝ => σ • A f) (A f) τ := by
    have h := (hasDerivAt_id τ).smul_const (A f)
    simpa using h
  rw [hfun]
  refine ((hu.sub_const f).add hs).congr_deriv ?_
  rw [hswap]
/-- **the exponential mean-value bound, for an arbitrary complete normed space.** Let `A` be a bounded operator, `f` a vector,
`0 ≤ t` and `C : ℝ`. If `‖exp (-τ • A) (A f) - A f‖ ≤ C` for every `τ ∈ [0, t]`, then

`‖exp (-t • A) f - f + t • A f‖ ≤ C * t`.

No nonnegativity, symmetry or inner product is needed, and `C` is not assumed nonnegative (for
`t = 0` both sides vanish). See the module docstring for the proof. -/
theorem norm_exp_neg_smul_sub_add_smul_le (A : H₀ →L[ℝ] H₀) (f : H₀) {t : ℝ} (ht : 0 ≤ t)
    {C : ℝ} (hC : ∀ τ ∈ Set.Icc 0 t, ‖NormedSpace.exp (-τ • A) (A f) - A f‖ ≤ C) :
    ‖NormedSpace.exp (-t • A) f - f + t • A f‖ ≤ C * t := by
  have hbd : ∀ τ ∈ Set.Ico (0 : ℝ) t, ‖-(NormedSpace.exp (-τ • A) (A f)) + A f‖ ≤ C := by
    intro τ hτ
    have hrw : -(NormedSpace.exp (-τ • A) (A f)) + A f =
        -(NormedSpace.exp (-τ • A) (A f) - A f) := by abel
    rw [hrw, norm_neg]
    exact hC τ ⟨hτ.1, hτ.2.le⟩
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun σ : ℝ => NormedSpace.exp (-σ • A) f - f + σ • A f)
    (f' := fun τ : ℝ => -(NormedSpace.exp (-τ • A) (A f)) + A f)
    (C := C) (fun x _ => (hasDerivAt_exp_neg_smul_path A f x).hasDerivWithinAt) hbd t
    (Set.right_mem_Icc.mpr ht)
  simp only [neg_zero, zero_smul, NormedSpace.exp_zero, one_apply_eq_self, sub_self, add_zero,
    sub_zero] at hmvt
  exact hmvt
end MeanValue
end Semigroup
end Analysis
end FunctionalInequalities


