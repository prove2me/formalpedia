-- Prove2me | Definitions.Def_OAI_Analysis_Herglotz
-- name    : OAI_Analysis_Herglotz
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:47:54.926953+00:00
-- url     : https://prove2.me/theorems/5737fc09-d39e-4704-b5ba-f91f456bc88d
-- title:
--   Herglotz–Riesz kernels, radial boundary measures and resolvent densities on the circle
-- statement:
--   This file provides the measure-theoretic and complex-analytic ingredients of a Herglotz-type representation on the unit disk: finite measures on the circle obtained from densities and radial restrictions, the Herglotz–Riesz kernel, Cayley transforms between the disk and the upper half-plane, and explicit kernels and densities parametrised by the boundary angle.
--
--   Throughout, the circle is parametrised by the angle set $\Theta = [0,2\pi]$ with (restricted) Lebesgue measure, which is finite, and $\zeta(\theta) = e^{i\theta}$. The Herglotz–Riesz kernel (centred at $0$) is $H(w,\zeta) = (\zeta+w)/(\zeta-w)$.
--
--   1. **Density measures.** For a finite measure $\mu$ on a compact space $X$ and a continuous real function $f$, the measure $\max(f,0)\,d\mu$ is a finite measure.
--
--   2. **Radial measures and kernels.** For $v$ continuous on the open unit disk and $R\in(0,1)$, the radial density is $\theta\mapsto v(Re^{i\theta})/(2\pi)$ (continuous on $\Theta$) and the radial measure is its density measure. For $|w|<R$, the radial kernel $\theta\mapsto\operatorname{Re}H(w,Re^{i\theta})$ is continuous. The approach radii $R_m = 1-1/(m+2)$ lie in $(0,1)$; for $|w|<1$ the clipped radius $\max((|w|+1)/2, R) > |w|$ gives the clipped kernel; and for $v$ harmonic near every point of the open unit disk, the radial sequence is the sequence of radial measures at $R_m$.
--
--   3. **Disk integrals and Cayley maps.** For $|w|<1$, $\theta\mapsto H(w,e^{i\theta})$ is continuous, and for a finite measure $\mu$ on $\Theta$
--   $$
--   \mathcal H_\mu(w) = \int_\Theta\frac{e^{i\theta}+w}{e^{i\theta}-w}\,d\mu(\theta).
--   $$
--   The Cayley maps are $s\mapsto(s-i)/(s+i)$ (half-plane to disk) and $w\mapsto i(1+w)/(1-w)$ (disk to half-plane).
--
--   4. **Boundary parameters and compact kernels.** For $\theta\in\Theta$ put
--   $$
--   t(\theta) = \frac{1-\cos\theta+\max(0,\sin\theta)}{2\,(1+\max(0,\sin\theta))}\in[0,1],\qquad \omega(\theta) = \frac{1}{1+\max(0,\sin\theta)},
--   $$
--   both continuous. The compact kernel is $K(t,\omega,s) = \omega/(1+(s-1)t)$, and $\mathcal K_\mu(s) = \int_\Theta K(t(\theta),\omega(\theta),s)\,d\mu(\theta)$. For $t\in[0,1]$ and $x>0$ one has $1+(x-1)t>0$, so $\theta\mapsto(1+(x-1)t(\theta))^{-1}$ is a continuous function on $\Theta$ (the real resolvent); for $A>0$ the resolvent density $\theta\mapsto A\,\omega(\theta)/(1+A\,t(\theta))$ is continuous, and the resolvent measure is the corresponding density measure with respect to $\mu$.
--
--   These objects are the building blocks for representing functions on the upper half-plane by integrals of simple resolvent kernels $(1+(s-1)t)^{-1}$ against finite measures on the circle.
--
--   **Formalization Note** The kernel is Mathlib's `herglotzRieszKernel 0 w ζ`. Measures are `FiniteMeasure`s; `densityMeasure` uses `withDensity` with `ENNReal.ofReal ∘ f`, so negative values of $f$ contribute $0$. Integrals are Bochner integrals (zero for non-integrable integrands). $\Theta$ is `Angle := Icc 0 (2π)` with the subtype measure space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Herglotz.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Herglotz.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber.Herglotz

section Density
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

def densityMeasure (f : C(X, ℝ)) : FiniteMeasure X :=
  ⟨μ.withDensity (fun x => ENNReal.ofReal (f x)),
    isFiniteMeasure_withDensity
      (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace f)).lintegral_lt_top.ne⟩

end Density

section WeakIntegral
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

end WeakIntegral

abbrev Angle := Icc (0 : ℝ) (2 * Real.pi)

local instance instMeasureSpaceElemRealAngle : MeasureSpace Angle := Measure.Subtype.measureSpace

instance : IsFiniteMeasure (volume : Measure Angle) := by
  constructor
  rw [show (volume : Measure Angle) = Measure.comap Subtype.val volume from rfl,
    Measure.comap_apply _ Subtype.val_injective
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' _
      MeasurableSet.univ]
  simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).measure_lt_top

def RadialDensity (v : ℂ → ℝ) (R : ℝ)
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1) : C(Angle, ℝ) where
  toFun θ := (2 * Real.pi)⁻¹ * v (circleMap 0 R θ)
  continuous_toFun := by
    apply continuous_const.mul
    apply hv.comp_continuous ((continuous_circleMap 0 R).comp continuous_subtype_val)
    intro θ
    simp only [Function.comp_apply, mem_ball, dist_zero_right, norm_circleMap_zero,
      abs_of_pos hR.1]
    exact hR.2

def radialMeasure (v : ℂ → ℝ) (R : ℝ)
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1) : FiniteMeasure Angle :=
  densityMeasure volume (RadialDensity v R hv hR)

def radialKernel (w : ℂ) (R : ℝ) (hR : ‖w‖ < R) : C(Angle, ℝ) where
  toFun θ := (herglotzRieszKernel 0 w (circleMap 0 R θ)).re
  continuous_toFun := by
    have hn (θ : Angle) : circleMap 0 R θ - w ≠ 0 := by
      intro h
      have he := congrArg norm (sub_eq_zero.mp h)
      simp only [norm_circleMap_zero, abs_of_pos (lt_of_le_of_lt (norm_nonneg w) hR)] at he
      linarith
    simp only [herglotzRieszKernel, sub_zero]
    apply Complex.continuous_re.comp
    exact (continuous_circleMap 0 R |>.comp continuous_subtype_val |>.add continuous_const).div
      (continuous_circleMap 0 R |>.comp continuous_subtype_val |>.sub continuous_const) hn

def approachRadius (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

theorem approachRadius_mem (n : ℕ) : approachRadius n ∈ Ioo 0 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < (n : ℝ) + 2 := by linarith
  have hi := (inv_lt_one₀ hp).mpr (by linarith)
  have hi' := inv_pos.mpr hp
  exact ⟨by dsimp [approachRadius]; linarith, by dsimp [approachRadius]; linarith⟩

def clippedRadius (w : ℂ) (hw : ‖w‖ < 1) (R : ℝ) : Ioi ‖w‖ :=
  ⟨max ((‖w‖ + 1) / 2) R,
    show ‖w‖ < max ((‖w‖ + 1) / 2) R from
      lt_of_lt_of_le (show ‖w‖ < (‖w‖ + 1) / 2 by linarith) (le_max_left _ _)⟩

def clippedKernel (w : ℂ) (hw : ‖w‖ < 1) (R : ℝ) : C(Angle, ℝ) :=
  radialKernel w (clippedRadius w hw R) (clippedRadius w hw R).property

def radialSequence (v : ℂ → ℝ) (hv : HarmonicOnNhd v (ball 0 1))
    (n : ℕ) : FiniteMeasure Angle :=
  radialMeasure v (approachRadius n) hv.continuousOn (approachRadius_mem n)

def diskKernel (w : ℂ) (hw : ‖w‖ < 1) : C(Angle, ℂ) where
  toFun θ := herglotzRieszKernel 0 w (circleMap 0 1 θ)
  continuous_toFun := by
    have hn (θ : Angle) : circleMap 0 1 θ - w ≠ 0 := by
      intro h
      have he := congrArg norm (sub_eq_zero.mp h)
      simp only [norm_circleMap_zero, abs_one] at he
      linarith
    simp only [herglotzRieszKernel, sub_zero]
    exact (continuous_circleMap 0 1 |>.comp continuous_subtype_val |>.add continuous_const).div
      (continuous_circleMap 0 1 |>.comp continuous_subtype_val |>.sub continuous_const) hn

def diskIntegral (μ : FiniteMeasure Angle) (w : ℂ) : ℂ :=
  ∫ θ : Angle, herglotzRieszKernel 0 w (circleMap 0 1 θ) ∂(μ : Measure Angle)

def toDisk (s : ℂ) : ℂ := (s - I) / (s + I)
def toHalfPlane (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

def boundaryParameter (θ : Angle) : ℝ :=
  (1 - (circleMap 0 1 θ).re + max 0 (circleMap 0 1 θ).im) /
    (2 * (1 + max 0 (circleMap 0 1 θ).im))

def boundaryWeight (θ : Angle) : ℝ :=
  (1 + max 0 (circleMap 0 1 θ).im)⁻¹

theorem boundaryParameter_mem (θ : Angle) : boundaryParameter θ ∈ Icc 0 1 := by
  have hr : |(circleMap 0 1 θ).re| ≤ 1 := by
    simpa only [norm_circleMap_zero, abs_one] using Complex.abs_re_le_norm (circleMap 0 1 θ)
  have hm : 0 ≤ max 0 (circleMap 0 1 θ).im := le_max_left _ _
  have hd : 0 < 2 * (1 + max 0 (circleMap 0 1 θ).im) := by positivity
  rw [abs_le] at hr
  constructor
  · exact div_nonneg (by linarith) hd.le
  · rw [boundaryParameter, div_le_one hd]
    linarith

theorem continuous_boundaryParameter : Continuous boundaryParameter := by
  unfold boundaryParameter
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro θ
  positivity

theorem continuous_boundaryWeight : Continuous boundaryWeight := by
  unfold boundaryWeight
  apply Continuous.inv₀ (by fun_prop)
  intro θ
  positivity

def compactKernel (t w : ℝ) (s : ℂ) : ℂ := (w : ℂ) / (1 + (s - 1) * t)

def compactIntegral (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  ∫ θ : Angle, compactKernel (boundaryParameter θ) (boundaryWeight θ) s ∂(μ : Measure Angle)

theorem real_compactDen_pos {t : ℝ} (ht : t ∈ Icc 0 1) {x : ℝ} (hx : 0 < x) :
    0 < 1 + (x - 1) * t := by
  by_cases h : t = 0
  · simp [h]
  · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    nlinarith [mul_pos hx hp, ht.2]

def realResolvent (x : ℝ) (hx : 0 < x) : C(Angle, ℝ) where
  toFun θ := (1 + (x - 1) * boundaryParameter θ)⁻¹
  continuous_toFun :=
    (continuous_const.add (continuous_const.mul continuous_boundaryParameter)).inv₀
      (fun θ => (real_compactDen_pos (boundaryParameter_mem θ) hx).ne')

def resolventDensity (A : ℝ) (hA : 0 < A) : C(Angle, ℝ) where
  toFun θ := A * boundaryWeight θ / (1 + A * boundaryParameter θ)
  continuous_toFun :=
    (continuous_const.mul continuous_boundaryWeight).div
      (continuous_const.add (continuous_const.mul continuous_boundaryParameter))
      (fun θ => by nlinarith [(boundaryParameter_mem θ).1])

def resolventMeasure (μ : FiniteMeasure Angle) (A : ℝ) (hA : 0 < A) : FiniteMeasure Angle :=
  densityMeasure (μ : Measure Angle) (resolventDensity A hA)

end EntropyPhotonNumber.Herglotz

end

end

end OAI


