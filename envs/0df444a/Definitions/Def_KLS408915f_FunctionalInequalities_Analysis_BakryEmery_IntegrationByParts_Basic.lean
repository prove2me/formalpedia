-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
-- name    : KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T04:59:12.447588+00:00
-- url     : https://prove2.me/theorems/8591cddc-a808-4ced-8919-8dc8b4f6ce07
-- title:
--   Weighted integration by parts
-- statement:
--   Against an additive Haar measure $m$, `integral_mul_fderiv_mul_fderiv` gives the one-directional integration-by-parts identity for a $C^1$ weight, a compactly supported $C^2$ function, and a $C^1$ test function, while `integral_mul_inner_gradient_eq_neg` sums these identities to obtain $\int w\langle\nabla f,\nabla g\rangle\,dm=-\int(w\Delta f+\langle\nabla w,\nabla f\rangle)g\,dm$. The identity `inner_gradient_tilted_weight` computes the gradient of $e^{-U}/Z$ as $-(e^{-U}/Z)\nabla U$. Consequently, `integral_inner_gradient_tilted` states for the tilted Haar measure $m.\mathrm{tilted}(-U)$ that $\int\langle\nabla f,\nabla g\rangle\,d\mu=\int(-\mathcal Lf)g\,d\mu$, with `weightedLaplacian` using the convention above.
-- source:
--   Source: Klartag, Logarithmic bounds for isoperimetry and slices of convex sets (arXiv:2303.14938v2), item E24. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Basic.lean#L74-L220 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
omit [FiniteDimensional ℝ E] in
/-- The gradient of the normalised tilted weight `exp (-U) / Z` is `-(exp (-U) / Z) ∇U`. -/
theorem inner_gradient_tilted_weight {U : E → ℝ} (hU : ContDiff ℝ 1 U) (Z : ℝ) (x y : E) :
    ⟪gradient (fun z => Real.exp ((-U) z) / Z) x, y⟫ =
      -(Real.exp ((-U) x) / Z) * ⟪gradient U x, y⟫ := by
  have hd : HasFDerivAt (fun z => Real.exp ((-U) z) / Z)
      (Z⁻¹ • (Real.exp ((-U) x) • -fderiv ℝ U x)) x := by
    have h1 : HasFDerivAt (fun z => Real.exp ((-U) z)) (Real.exp ((-U) x) • -fderiv ℝ U x) x :=
      ((hU.differentiable one_ne_zero x).hasFDerivAt.neg).exp
    have hfun : (fun z => Real.exp ((-U) z) / Z) = fun z => Real.exp ((-U) z) * Z⁻¹ :=
      funext fun z => div_eq_mul_inv _ _
    rw [hfun]
    exact h1.mul_const Z⁻¹
  rw [inner_gradient_left, hd.fderiv, inner_gradient_left]
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring
section Haar
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]
omit [CompleteSpace E] in
/-- One-directional weighted integration by parts against a Haar measure: for a `C¹` weight `w`, a
`C²` compactly supported `f` and a `C¹` function `g`,
`∫ w ∂ᵥf ∂ᵥg = -∫ (w ∂ᵥ∂ᵥf + ∂ᵥw ∂ᵥf) g`. -/
theorem integral_mul_fderiv_mul_fderiv {w f g : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) (v : E) :
    ∫ x, w x * (fderiv ℝ f x v * fderiv ℝ g x v) ∂m =
      -∫ x, (w x * fderiv ℝ (fderiv ℝ f) x v v + fderiv ℝ w x v * fderiv ℝ f x v) * g x ∂m := by
  set F : E → ℝ := fun x => w x * fderiv ℝ f x v with hF
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hF1 : ContDiff ℝ 1 F := hw.mul (hf1.clm_apply contDiff_const)
  have hFc : HasCompactSupport F := (hfc.fderiv_apply ℝ v).mul_left
  have hFd : ∀ x, HasFDerivAt F
      (w x • ((fderiv ℝ f x).comp (0 : E →L[ℝ] E) + (fderiv ℝ (fderiv ℝ f) x).flip v) +
        fderiv ℝ f x v • fderiv ℝ w x) x := fun x =>
    (hw.differentiable one_ne_zero x).hasFDerivAt.mul
      ((hf1.differentiable one_ne_zero x).hasFDerivAt.clm_apply (hasFDerivAt_const v x))
  have hFderiv : ∀ x, fderiv ℝ F x v =
      w x * fderiv ℝ (fderiv ℝ f) x v v + fderiv ℝ w x v * fderiv ℝ f x v := by
    intro x
    rw [(hFd x).fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.comp_zero, ContinuousLinearMap.flip_apply,
      smul_eq_mul, zero_add]
    ring
  have hFcont : Continuous F := hF1.continuous
  have hgcont : Continuous g := hg.continuous
  have hg'cont : Continuous fun x => fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF'cont : Continuous fun x => fderiv ℝ F x v :=
    (hF1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h1 : Integrable (fun x => fderiv ℝ F x v * g x) m :=
    (hF'cont.mul hgcont).integrable_of_hasCompactSupport (hFc.fderiv_apply ℝ v).mul_right
  have h2 : Integrable (fun x => F x * fderiv ℝ g x v) m :=
    (hFcont.mul hg'cont).integrable_of_hasCompactSupport hFc.mul_right
  have h3 : Integrable (fun x => F x * g x) m :=
    (hFcont.mul hgcont).integrable_of_hasCompactSupport hFc.mul_right
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := m) h1 h2 h3
    (fun x _ => (hFd x).differentiableAt) (fun x _ => hg.differentiable one_ne_zero x)
  calc ∫ x, w x * (fderiv ℝ f x v * fderiv ℝ g x v) ∂m
      = ∫ x, F x * fderiv ℝ g x v ∂m := by
        congr 1
        funext x
        simp only [hF]
        ring
    _ = -∫ x, fderiv ℝ F x v * g x ∂m := key
    _ = -∫ x, (w x * fderiv ℝ (fderiv ℝ f) x v v + fderiv ℝ w x v * fderiv ℝ f x v) * g x ∂m := by
        congr 2
        funext x
        rw [hFderiv x]
/-- **Weighted integration by parts** against a Haar measure: for a `C¹` weight `w`, a `C²`
compactly supported `f` and a `C¹` function `g`,
`∫ w ⟪∇f, ∇g⟫ dm = -∫ (w Δf + ⟪∇w, ∇f⟫) g dm`, i.e. `∫ ⟪w∇f, ∇g⟫ = -∫ div(w∇f) g`. -/
theorem integral_mul_inner_gradient_eq_neg {w f g : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    ∫ x, w x * ⟪gradient f x, gradient g x⟫ ∂m =
      -∫ x, (w x * Laplacian.laplacian f x + ⟪gradient w x, gradient f x⟫) * g x ∂m := by
  set b := stdOrthonormalBasis ℝ E with hb
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (m := 1) (by norm_num)
  have hf' : Continuous (fderiv ℝ f) := hf1.continuous
  have hf'' : Continuous (fderiv ℝ (fderiv ℝ f)) := hf1.continuous_fderiv one_ne_zero
  have hw' : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hg' : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  have hint : ∀ i, Integrable (fun x => w x * (fderiv ℝ f x (b i) * fderiv ℝ g x (b i))) m := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hw.continuous.mul ((hf'.clm_apply continuous_const).mul
        (hg'.clm_apply continuous_const))
    · exact ((hfc.fderiv_apply ℝ (b i)).mul_right).mul_left
  have hint' : ∀ i, Integrable (fun x =>
      (w x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) + fderiv ℝ w x (b i) * fderiv ℝ f x (b i)) * g x)
      m := by
    intro i
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hw.continuous.mul ((hf''.clm_apply continuous_const).clm_apply continuous_const)).add
        ((hw'.clm_apply continuous_const).mul (hf'.clm_apply continuous_const))).mul hg.continuous
    · refine HasCompactSupport.mul_right ?_
      exact ((((hfc.fderiv (𝕜 := ℝ)).fderiv_apply ℝ (b i)).comp_left (g := fun A : E →L[ℝ] ℝ => A (b i))
        (by simp)).mul_left).add ((hfc.fderiv_apply ℝ (b i)).mul_left)
  calc ∫ x, w x * ⟪gradient f x, gradient g x⟫ ∂m
      = ∫ x, ∑ i, w x * (fderiv ℝ f x (b i) * fderiv ℝ g x (b i)) ∂m := by
        congr 1
        funext x
        rw [inner_gradient_eq_sum_fderiv_mul_fderiv, Finset.mul_sum]
    _ = ∑ i, ∫ x, w x * (fderiv ℝ f x (b i) * fderiv ℝ g x (b i)) ∂m :=
        integral_finsetSum _ fun i _ => hint i
    _ = ∑ i, -∫ x, (w x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) +
          fderiv ℝ w x (b i) * fderiv ℝ f x (b i)) * g x ∂m :=
        Finset.sum_congr rfl fun i _ => integral_mul_fderiv_mul_fderiv m hw hf hfc hg (b i)
    _ = -∫ x, ∑ i, (w x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) +
          fderiv ℝ w x (b i) * fderiv ℝ f x (b i)) * g x ∂m := by
        rw [integral_finsetSum _ fun i _ => hint' i, Finset.sum_neg_distrib]
    _ = -∫ x, (w x * Laplacian.laplacian f x + ⟪gradient w x, gradient f x⟫) * g x ∂m := by
        congr 2
        funext x
        rw [laplacian_eq_sum_fderiv_fderiv, inner_gradient_eq_sum_fderiv_mul_fderiv, ← Finset.sum_mul,
          Finset.mul_sum, ← Finset.sum_add_distrib]
end Haar
section Tilted
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]
/-- **Weighted integration by parts for a tilted Haar measure** (property weighted integration by parts): with
`μ = m.tilted (-U)` the normalised law of density `exp (-U)`, a `C¹` potential `U`, a `C²`
compactly supported `f` and a `C¹` function `g`,
`∫ ⟪∇f, ∇g⟫ dμ = ∫ (-ℒf) g dμ` where `ℒf = Δf - ⟪∇U, ∇f⟫`. -/
theorem integral_inner_gradient_tilted {U f g : E → ℝ} (hU : ContDiff ℝ 1 U)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 1 g) :
    ∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-U)) =
      ∫ x, -weightedLaplacian U f x * g x ∂(m.tilted (-U)) := by
  rw [integral_tilted, integral_tilted]
  set Z : ℝ := ∫ x, Real.exp ((-U) x) ∂m with hZ
  have hw : ContDiff ℝ 1 fun z => Real.exp ((-U) z) / Z := by
    have : (fun z => Real.exp ((-U) z) / Z) = fun z => Real.exp ((-U) z) * Z⁻¹ :=
      funext fun z => div_eq_mul_inv _ _
    rw [this]
    exact (hU.neg.exp).mul contDiff_const
  have key := integral_mul_inner_gradient_eq_neg m hw hf hfc hg
  simp only [smul_eq_mul]
  rw [key, ← integral_neg]
  congr 1
  funext x
  rw [inner_gradient_tilted_weight hU Z, weightedLaplacian_apply]
  ring
end Tilted
end BakryEmery
end Analysis
end FunctionalInequalities


