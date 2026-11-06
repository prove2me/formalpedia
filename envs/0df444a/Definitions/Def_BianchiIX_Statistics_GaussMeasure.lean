-- Prove2me | Definitions.Def_BianchiIX_Statistics_GaussMeasure
-- name    : BianchiIX_Statistics_GaussMeasure
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T16:18:07.716965+00:00
-- url     : https://prove2.me/theorems/64b38c8c-b676-4b4e-97ee-31c864466104
-- title:
--   Normalized Gauss measure and its primitive
-- statement:
--   Let $\lambda$ be Lebesgue measure on $\mathbb R$, and let
--   $\lambda_0$ be its restriction to $(0,1)$. The Gauss measure is
--   $$d\mu_G(x)=\frac{1}{\log2\,(1+x)}\,d\lambda_0(x).$$
--   Write $w(x)=1/(\log2\,(1+x))$ and $P(x)=\log(1+x)/\log2$ for $x\geq0$.
--
--   The primitive satisfies $P'=w$ on the nonnegative half-line. Its values at
--   zero and one give total mass one. The definitions include the resulting
--   probability-measure instance and the fact that every singleton has measure zero.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussMeasure.lean

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity

namespace BianchiIX
end BianchiIX

section
open BianchiIX
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal

private theorem BianchiIX.volume_image_eq_lintegral_abs_deriv {F F' : ℝ → ℝ} {A : Set ℝ}
    (hA : MeasurableSet A) (hF : ∀ x ∈ A, HasDerivAt F (F' x) x) (hinj : InjOn F A) :
    volume (F '' A) = ∫⁻ x in A, ENNReal.ofReal |F' x| := by
  simpa using lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun x hx => (hF x hx).hasDerivWithinAt) hinj (fun _ => 1)

end
end


/-! The normalized Gauss density, its interval masses, and its equivalence to phase length. -/

open Set MeasureTheory
open scoped ENNReal

namespace BianchiIX

noncomputable section

def gaussWeight (x : ℝ) : ℝ := 1 / (Real.log 2 * (1 + x))

def gaussMeasure : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (gaussWeight x))

def gaussPrimitive (x : ℝ) : ℝ := Real.log (1 + x) / Real.log 2

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem gaussWeight_pos {x : ℝ} (hx : 0 ≤ x) : 0 < gaussWeight x := by
  unfold gaussWeight
  exact one_div_pos.mpr (mul_pos log_two_pos (by linarith))



theorem hasDerivAt_gaussPrimitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt gaussPrimitive (gaussWeight x) x := by
  have h := (((hasDerivAt_id x).const_add 1).log (by linarith : (1 : ℝ) + x ≠ 0)).div_const (Real.log 2)
  convert! h using 1
  dsimp only [id_eq]
  simp only [gaussWeight, div_eq_mul_inv, mul_inv_rev, one_mul]

theorem gaussPrimitive_strictMonoOn : StrictMonoOn gaussPrimitive (Ici 0) := by
  intro x hx y _ hxy
  apply (div_lt_div_iff_of_pos_right log_two_pos).mpr
  exact Real.log_lt_log (by change 0 ≤ x at hx; linarith) (by linarith)

theorem gaussWeight_lintegral_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ x in Ioo a b, ENNReal.ofReal (gaussWeight x)) =
      ENNReal.ofReal (gaussPrimitive b - gaussPrimitive a) := by
  have hcont : ContinuousOn gaussPrimitive (Icc a b) :=
    fun x hx => (hasDerivAt_gaussPrimitive (ha.trans hx.1)).continuousAt.continuousWithinAt
  have hsub : Icc a b ⊆ Ici (0 : ℝ) := fun _ hx => ha.trans hx.1
  have himg := hcont.image_Ioo_of_strictMonoOn hab (gaussPrimitive_strictMonoOn.mono hsub)
  have hchange := volume_image_eq_lintegral_abs_deriv measurableSet_Ioo
    (fun x (hx : x ∈ Ioo a b) => hasDerivAt_gaussPrimitive (ha.trans hx.1.le))
    (gaussPrimitive_strictMonoOn.injOn.mono (fun _ hx => ha.trans hx.1.le))
  have heq : (∫⁻ x in Ioo a b, ENNReal.ofReal (gaussWeight x)) =
      ∫⁻ x in Ioo a b, ENNReal.ofReal |gaussWeight x| := by
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    dsimp only
    rw [abs_of_pos (gaussWeight_pos (ha.trans hx.1.le))]
  rw [heq, ← hchange, himg, Real.volume_Ioo]





theorem gaussMeasure_univ : gaussMeasure univ = 1 := by
  rw [gaussMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    gaussWeight_lintegral_Ioo (a := 0) (b := 1) le_rfl zero_le_one]
  norm_num [gaussPrimitive]

instance _root_.BianchiIX.instIsProbabilityMeasureRealGaussMeasure : IsProbabilityMeasure gaussMeasure := ⟨gaussMeasure_univ⟩

instance _root_.BianchiIX.instNullSingletonClassRealGaussMeasure : NullSingletonClass gaussMeasure := by
  unfold gaussMeasure
  infer_instance





















end
end BianchiIX


