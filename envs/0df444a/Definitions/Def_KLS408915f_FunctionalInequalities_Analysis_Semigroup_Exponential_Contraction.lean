-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:10:13.934411+00:00
-- url     : https://prove2.me/theorems/87875fb8-aa40-4224-b774-adc6a5f27972
-- title:
--   Contraction of exponentials of bounded nonnegative operators
-- statement:
--   `hasDerivAt_exp_smul_apply` gives the derivative of $t\mapsto\exp(tA)f$ as $A\exp(tA)f$ for a bounded operator $A$ on a complete real Hilbert space. If $L$ satisfies $\langle Lf,f\rangle\ge0$ for every $f$, then `antitone_normSq_exp_smul_neg` states that $t\mapsto\|\exp(t(-L))f\|^2$ is antitone on all of $\mathbb R$, and `norm_exp_neg_smul_apply_le` gives $\|\exp(-tL)f\|\le\|f\|$ for $t\ge0$. Self-adjointness of $L$ is not assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Exponential/Contraction.lean#L58-L99 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Exponential.Contraction`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_Exponential_Contraction`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
section Orbit
variable {H₀ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
/-- The orbit `t ↦ exp (t • A) f` of a bounded operator is differentiable, with derivative
`A (exp (t • A) f)`. This is `hasDerivAt_exp_smul_const'` evaluated at the fixed vector `f`. -/
theorem hasDerivAt_exp_smul_apply (A : H₀ →L[ℝ] H₀) (f : H₀) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A) f) (A (NormedSpace.exp (t • A) f)) t := by
  have h := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).clm_apply (hasDerivAt_const t f)
  simpa using h
/-- Along the orbit `u t = exp (t • (-L)) f` of a nonnegative bounded operator `L`, the squared
norm `‖u t‖²` has derivative `-2 ⟪L (u t), u t⟫ ≤ 0` and is therefore antitone on all of `ℝ`.

Only nonnegativity of `L` and symmetry of the real inner product are used; self-adjointness of
`L` is not assumed. -/
theorem antitone_normSq_exp_smul_neg (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) (f : H₀) :
    Antitone fun t : ℝ => ‖NormedSpace.exp (t • (-L)) f‖ ^ 2 := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ‖NormedSpace.exp (s • (-L)) f‖ ^ 2)
      (-(2 * ⟪L (NormedSpace.exp (t • (-L)) f), NormedSpace.exp (t • (-L)) f⟫)) t := by
    intro t
    have h := (hasDerivAt_exp_smul_apply (-L) f t).inner ℝ (hasDerivAt_exp_smul_apply (-L) f t)
    have hfun : (fun s : ℝ => ‖NormedSpace.exp (s • (-L)) f‖ ^ 2) =
        fun s : ℝ => ⟪NormedSpace.exp (s • (-L)) f, NormedSpace.exp (s • (-L)) f⟫ := by
      funext s
      rw [real_inner_self_eq_norm_sq]
    rw [hfun]
    refine h.congr_deriv ?_
    rw [neg_apply, inner_neg_left, inner_neg_right,
      real_inner_comm (L (NormedSpace.exp (t • (-L)) f))]
    ring
  refine antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) fun t => ?_
  rw [(hderiv t).deriv]
  have := hL (NormedSpace.exp (t • (-L)) f)
  linarith
/-- **resolvent contraction, strengthened.** If `L` is a bounded nonnegative operator on a real Hilbert space, then
`exp (-t • L)` is a contraction for every `t ≥ 0`, pointwise: `‖exp (-t • L) f‖ ≤ ‖f‖`.

The route's self-adjointness hypothesis is not needed and not assumed. -/
theorem norm_exp_neg_smul_apply_le (L : H₀ →L[ℝ] H₀) (hL : ∀ f, 0 ≤ ⟪L f, f⟫) {t : ℝ}
    (ht : 0 ≤ t) (f : H₀) : ‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖ := by
  have h := antitone_normSq_exp_smul_neg L hL f ht
  simp only [zero_smul, NormedSpace.exp_zero, one_apply_eq_self] at h
  rw [neg_smul, ← smul_neg]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h
end Orbit
end Semigroup
end Analysis
end FunctionalInequalities


