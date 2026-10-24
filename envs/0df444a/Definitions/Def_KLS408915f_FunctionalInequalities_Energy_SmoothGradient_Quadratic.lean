-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
-- name    : KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:45:51.45542+00:00
-- url     : https://prove2.me/theorems/ec7e5cf0-c320-4a44-860e-4eac649867b5
-- title:
--   Quadratic structure of smooth-gradient tests
-- statement:
--   The test operations `SmoothGradient.Test.zero`, `add`, `neg`, `sub`, and `smul` equip the smooth-gradient tests with the relevant additive and real-module structures, with Borel assumptions where required for integrability and measurability. The auxiliary gradient identities show that the canonical gradient respects sums, differences, negation, and real scalar multiplication, while the squared-gradient integrability conditions are preserved. The resulting finite pre-energy has the algebraic ingredients for quadratic behavior, but this bundle does not assert closedness or density of the relaxed energy.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Quadratic.lean#L33-L289 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Quadratic`, definition bundle `KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Quadratic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_SmoothGradient_Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
open InnerProductSpace MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities
namespace Energy
namespace SmoothGradient
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]
namespace Test
variable {mu : ProbabilityMeasure E}
/-- The gradient of a sum is the sum of the gradients. -/
theorem gradient_add (f g : Test mu) (x : E) :
    gradient (f.toFun + g.toFun) x = gradient f.toFun x + gradient g.toFun x := by
  apply (toDual ℝ E).injective
  simpa only [toDual_gradient, map_add] using
    fderiv_add ((f.contDiff.differentiable (by simp)) x)
      ((g.contDiff.differentiable (by simp)) x)
/-- The gradient of a negated test is the negated gradient. -/
theorem gradient_neg (f : Test mu) (x : E) :
    gradient (-f.toFun) x = -gradient f.toFun x := by
  apply (toDual ℝ E).injective
  simp only [toDual_gradient, map_neg, fderiv_neg]
/-- The gradient of a difference is the difference of the gradients. -/
theorem gradient_sub (f g : Test mu) (x : E) :
    gradient (f.toFun - g.toFun) x = gradient f.toFun x - gradient g.toFun x := by
  apply (toDual ℝ E).injective
  simpa only [toDual_gradient, map_sub] using
    fderiv_sub ((f.contDiff.differentiable (by simp)) x)
      ((g.contDiff.differentiable (by simp)) x)
/-- The gradient commutes with real scalar multiplication. -/
theorem gradient_smul (c : ℝ) (f : Test mu) (x : E) :
    gradient (c • f.toFun) x = c • gradient f.toFun x := by
  apply (toDual ℝ E).injective
  simpa only [toDual_gradient, map_smul] using
    fderiv_const_smul ((f.contDiff.differentiable (by simp)) x) c
omit [MeasurableSpace E] in
 theorem continuous_gradient_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (gradient f) := by
  change Continuous (fun x ↦ (toDual ℝ E).symm (fderiv ℝ f x))
  exact (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv (by simp))
 theorem gradientSq_add_integrable [BorelSpace E]
    (f g : Test mu) :
    Integrable (fun x ↦ ‖gradient (f.toFun + g.toFun) x‖ ^ 2) (mu : Measure E) := by
  refine ((f.gradient_sq_integrable.add g.gradient_sq_integrable).const_mul 2).mono' ?_ ?_
  · exact
      ((FunctionalInequalities.Energy.SmoothGradient.Test.continuous_gradient_of_contDiff (f.contDiff.add g.contDiff)).norm.pow 2)
        |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), gradient_add]
    change ‖gradient f.toFun x + gradient g.toFun x‖ ^ 2 ≤
      2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2)
    calc
      ‖gradient f.toFun x + gradient g.toFun x‖ ^ 2 ≤
          (‖gradient f.toFun x‖ + ‖gradient g.toFun x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_add_le _ _)
      _ ≤ 2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2) := add_sq_le
 theorem gradientSq_sub_integrable [BorelSpace E]
    (f g : Test mu) :
    Integrable (fun x ↦ ‖gradient (f.toFun - g.toFun) x‖ ^ 2) (mu : Measure E) := by
  refine ((f.gradient_sq_integrable.add g.gradient_sq_integrable).const_mul 2).mono' ?_ ?_
  · exact
      ((FunctionalInequalities.Energy.SmoothGradient.Test.continuous_gradient_of_contDiff (f.contDiff.sub g.contDiff)).norm.pow 2)
        |>.aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), gradient_sub]
    change ‖gradient f.toFun x - gradient g.toFun x‖ ^ 2 ≤
      2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2)
    calc
      ‖gradient f.toFun x - gradient g.toFun x‖ ^ 2 ≤
          (‖gradient f.toFun x‖ + ‖gradient g.toFun x‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_sub_le _ _)
      _ ≤ 2 * (‖gradient f.toFun x‖ ^ 2 + ‖gradient g.toFun x‖ ^ 2) := add_sq_le
/-- The zero smooth-gradient test. -/
def zero (mu : ProbabilityMeasure E) : Test mu where
  toFun := 0
  contDiff := contDiff_const
  memLp_two := MemLp.zero
  gradient_sq_integrable := by
    change Integrable (fun x ↦ ‖gradient (fun _ : E ↦ (0 : ℝ)) x‖ ^ 2) (mu : Measure E)
    have hzero : (fun x ↦ ‖gradient (fun _ : E ↦ (0 : ℝ)) x‖ ^ 2) = (0 : E → ℝ) := by
      funext x
      simp only [gradient_fun_const, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Pi.zero_apply]
    rw [hzero]
    exact integrable_zero E ℝ (mu : Measure E)
/-- The sum of two smooth-gradient tests. -/
def add [BorelSpace E] (f g : Test mu) : Test mu where
  toFun := f.toFun + g.toFun
  contDiff := f.contDiff.add g.contDiff
  memLp_two := f.memLp_two.add g.memLp_two
  gradient_sq_integrable := FunctionalInequalities.Energy.SmoothGradient.Test.gradientSq_add_integrable f g
/-- The additive inverse of a smooth-gradient test. -/
def neg (f : Test mu) : Test mu where
  toFun := -f.toFun
  contDiff := f.contDiff.neg
  memLp_two := f.memLp_two.neg
  gradient_sq_integrable := by
    simpa only [gradient_neg, norm_neg] using f.gradient_sq_integrable
/-- The difference of two smooth-gradient tests. -/
def sub [BorelSpace E] (f g : Test mu) : Test mu where
  toFun := f.toFun - g.toFun
  contDiff := f.contDiff.sub g.contDiff
  memLp_two := f.memLp_two.sub g.memLp_two
  gradient_sq_integrable := FunctionalInequalities.Energy.SmoothGradient.Test.gradientSq_sub_integrable f g
/-- Real scalar multiplication of a smooth-gradient test. -/
def smul (c : ℝ) (f : Test mu) : Test mu where
  toFun := c • f.toFun
  contDiff := f.contDiff.const_smul c
  memLp_two := f.memLp_two.const_smul c
  gradient_sq_integrable := by
    simpa only [gradient_smul, norm_smul, mul_pow] using
      f.gradient_sq_integrable.const_mul (‖c‖ ^ 2)
/-- Smooth-gradient tests are determined by their underlying functions. -/
@[ext]
theorem ext {f g : Test mu} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl
/-- The underlying-function map on smooth-gradient tests is injective. -/
theorem toFun_injective : Function.Injective
    (toFun : Test mu → E → ℝ) :=
  fun _ _ ↦ ext
instance : Zero (Test mu) :=
  ⟨zero mu⟩
instance [BorelSpace E] : Add (Test mu) :=
  ⟨add⟩
instance : Neg (Test mu) :=
  ⟨neg⟩
instance [BorelSpace E] : Sub (Test mu) :=
  ⟨sub⟩
instance [BorelSpace E] : SMul ℕ (Test mu) :=
  ⟨fun n f ↦ smul (n : ℝ) f⟩
instance [BorelSpace E] : SMul ℤ (Test mu) :=
  ⟨fun n f ↦ smul (n : ℝ) f⟩
instance : SMul ℝ (Test mu) :=
  ⟨smul⟩
instance instAddCommGroup [BorelSpace E] : AddCommGroup (Test mu) :=
  Function.Injective.addCommGroup toFun toFun_injective
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun f n ↦ by
      funext x
      change (n : ℝ) * f.toFun x = n • f.toFun x
      simp)
    (fun f n ↦ by
      funext x
      change (n : ℝ) * f.toFun x = n • f.toFun x
      simp)
/-- The underlying-function map as an additive homomorphism. -/
def toFunAddMonoidHom [BorelSpace E] : Test mu →+ E → ℝ where
  toFun := toFun
  map_zero' := rfl
  map_add' _ _ := rfl
instance instModule [BorelSpace E] : Module ℝ (Test mu) :=
  Function.Injective.module ℝ toFunAddMonoidHom toFun_injective (fun _ _ ↦ rfl)
end Test
 instance smoothGradientPreEnergyTestAddCommGroup
    (mu : ProbabilityMeasure E) [FiniteDimensional ℝ E] [BorelSpace E]
    [SecondCountableTopology E] : AddCommGroup (preEnergy mu).Test := by
  change AddCommGroup (Test mu)
  infer_instance
 instance smoothGradientPreEnergyTestModule
    (mu : ProbabilityMeasure E) [FiniteDimensional ℝ E] [BorelSpace E]
    [SecondCountableTopology E] : Module ℝ (preEnergy mu).Test := by
  change Module ℝ (Test mu)
  infer_instance
end SmoothGradient
end Energy
end FunctionalInequalities


