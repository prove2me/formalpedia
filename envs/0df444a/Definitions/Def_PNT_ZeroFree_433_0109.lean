-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0109
-- name    : PNT_ZeroFree_433_0109
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:17:27.90255+00:00
-- url     : https://prove2.me/theorems/67736f95-bb06-45ff-82f6-6cd9d09b9607
-- title:
--   Zero-free region foundations: QuadraticSieve.GreenIntegrals [0109]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.GreenIntegrals
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/GreenIntegrals.lean#L358-L639

import Definitions.Def_PNT_ZeroFree_433_0109_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/GreenIntegrals.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap


namespace ShortDraftLatticeCount
open ActualEisensteinCubic ActualEisensteinCoordinates ConcreteTraceCRT

theorem rowNormBall_norm_sq_le (H : ℕ) (k : ActualEisensteinCubic.O) (hk : k ∈ rowNormBall H) :
    ‖eisEmbedding k‖^2 ≤ 3*((H : ℝ)+1)^2 := by
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hv
  obtain ⟨haL,haU⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hbL,hbU⟩ := Finset.mem_Icc.mp hb
  have ha2 : v.1^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haU) (show 0 ≤ (H : ℤ)+1+v.1 by linarith)]
  have hb2 : v.2^2 ≤ ((H : ℤ)+1)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbU) (show 0 ≤ (H : ℤ)+1+v.2 by linarith)]
  have hq : v.1*v.1-v.1*v.2+v.2*v.2 ≤ 3*((H : ℤ)+1)^2 := by
    nlinarith [sq_nonneg (v.1+v.2)]
  rw [eisEmbedding_eval_norm_sq]
  exact_mod_cast hq

end ShortDraftLatticeCount
namespace SecondPassArithmetic
open ActualEisensteinCubic ConcreteTraceCRT

theorem secondFrequencyCutoff_norm_sq_le (scale H : ℝ) (k : ActualEisensteinCubic.O)
    (hk : k ∈ secondFrequencyCutoff scale H) :
    ‖eisEmbedding k‖^2 ≤ 3*((⌈H/scale⌉₊ : ℝ)+1)^2 :=
  ShortDraftLatticeCount.rowNormBall_norm_sq_le _ k hk

end SecondPassArithmetic

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma green_identity_interval (f g : ℝ → ℂ) (a b : ℝ)
    (hf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ f x)
    (hg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ g x)
    (hdf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv f) x)
    (hdg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv g) x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b) :
    (∫x in a..b,deriv (deriv f) x*star (g x)-f x*star (deriv (deriv g) x)) =
      (deriv f b*star (g b)-f b*star (deriv g b)) -
      (deriv f a*star (g a)-f a*star (deriv g a)) := by
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    convert! (((hdf x hx).hasDerivAt.mul (hg x hx).hasDerivAt.star).sub
      ((hf x hx).hasDerivAt.mul (hdg x hx).hasDerivAt.star)) using 1 ; ring
  · have hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b := by
      apply hig.mono_fun
        ((aestronglyMeasurable_deriv (deriv g) _).star)
      exact Filter.Eventually.of_forall (fun x => by simp only [Pi.star_apply,norm_star,le_refl])
    exact (hif.mul_continuousOn hgc.star).sub (hstar.continuousOn_mul hfc)

lemma axisSlice_update (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) :
    axisSlice f (Function.update p j t) j = axisSlice f p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

theorem actual_axis_local_regular (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε C : ℝ, 0<ε ∧ ∀t∈Metric.ball (p j) ε,
      0<(Function.update p j t) 2 ∧
      DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t ∧
      ‖deriv (deriv (axisSlice (upperEisensteinField s) p j)) t‖≤C := by
  obtain ⟨ε,hε,M₀,M₁,M₂,hM₀,hM₁,hM₂,hbound⟩ := axis_summable_derivative_bounds s hs p hv j
  refine ⟨ε,∑'r,M₂ r,hε,?_⟩
  intro t ht
  have hpos := (hbound t ht).1
  have hterms := eisenstein_axis_termwise s hs (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at hterms
  have heq := axisSlice_eventuallyEq_of_positive (upperEisensteinField s) (smoothEisenstein s)
    (fun q hq => upperEisensteinField_eq_smooth s q hq) (Function.update p j t) hpos j
  simp only [axisSlice_update,Function.update_self] at heq
  refine ⟨hpos,(hterms.2.2.1.congr_of_eventuallyEq heq).differentiableAt,
    (hterms.2.2.2.congr_of_eventuallyEq heq.deriv).differentiableAt,?_⟩
  rw [heq.deriv.deriv_eq,hterms.2.2.2.deriv]
  exact tsum_of_norm_bounded hM₂.hasSum (fun r => ((hbound t ht).2 r).2.2)

lemma intervalIntegrable_second_of_bound (f : ℝ → ℂ) (C a b : ℝ)
    (hbound : ∀x∈Set.uIcc a b, ‖deriv (deriv f) x‖≤C) :
    IntervalIntegrable (deriv (deriv f)) volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b).mono_fun
    (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  exact (hbound x (Set.uIoc_subset_uIcc hx)).trans (le_abs_self C)

theorem actual_eisenstein_local_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∀a b : ℝ, Set.uIcc a b ⊆ Metric.ball (p j) ε →
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  obtain ⟨εs,Cs,hεs,hregs⟩ := actual_axis_local_regular s hs p hv j
  obtain ⟨εt,Ct,hεt,hregt⟩ := actual_axis_local_regular t ht p hv j
  refine ⟨min εs εt,lt_min hεs hεt,?_⟩
  intro a b hab
  have hsa (x : ℝ) (hx : x∈Set.uIcc a b) := hregs x
    (Metric.ball_subset_ball (min_le_left _ _) (hab hx))
  have hta (x : ℝ) (hx : x∈Set.uIcc a b) := hregt x
    (Metric.ball_subset_ball (min_le_right _ _) (hab hx))
  apply green_identity_interval
  · exact fun x hx => (hsa x hx).2.1
  · exact fun x hx => (hta x hx).2.1
  · exact fun x hx => (hsa x hx).2.2.1
  · exact fun x hx => (hta x hx).2.2.1
  · exact intervalIntegrable_second_of_bound _ Cs a b (fun x hx => (hsa x hx).2.2.2)
  · exact intervalIntegrable_second_of_bound _ Ct a b (fun x hx => (hta x hx).2.2.2)

lemma actual_axis_differentiable_at (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (ht : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (upperEisensteinField s) p j) t ∧
      DifferentiableAt ℝ (deriv (axisSlice (upperEisensteinField s) p j)) t := by
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  have h := hreg t (by simpa only [Function.update_self] using Metric.mem_ball_self hε)
  simp only [axisSlice_update] at h
  exact ⟨h.2.1,h.2.2.1⟩

lemma actual_axis_second_locallyIntegrable (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (j : Fin 3) :
    LocallyIntegrableOn (deriv (deriv (axisSlice (upperEisensteinField s) p j)))
      {t : ℝ | 0<(Function.update p j t) 2} volume := by
  intro t ht
  obtain ⟨ε,C,hε,hreg⟩ := actual_axis_local_regular s hs (Function.update p j t) ht j
  simp only [axisSlice_update,Function.update_self,Function.update_idem] at hreg
  refine ⟨Metric.ball t ε,mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hε),?_⟩
  have hconst : IntegrableOn (fun _ : ℝ => C) (Metric.ball t ε) volume := integrableOn_const
  apply hconst.mono' (aestronglyMeasurable_deriv _ _)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (hreg x hx).2.2.2

theorem actual_eisenstein_green_interval (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (j : Fin 3) (a b : ℝ)
    (hheight : ∀x∈Set.uIcc a b,0<(Function.update p j x) 2) :
      (∫x in a..b,
        deriv (deriv (axisSlice (upperEisensteinField s) p j)) x *
          star (axisSlice (upperEisensteinField t) p j x) -
        axisSlice (upperEisensteinField s) p j x *
          star (deriv (deriv (axisSlice (upperEisensteinField t) p j)) x)) =
      (deriv (axisSlice (upperEisensteinField s) p j) b *
          star (axisSlice (upperEisensteinField t) p j b) -
        axisSlice (upperEisensteinField s) p j b *
          star (deriv (axisSlice (upperEisensteinField t) p j) b)) -
      (deriv (axisSlice (upperEisensteinField s) p j) a *
          star (axisSlice (upperEisensteinField t) p j a) -
        axisSlice (upperEisensteinField s) p j a *
          star (deriv (axisSlice (upperEisensteinField t) p j) a)) := by
  apply green_identity_interval
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p j x (hheight x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p j x (hheight x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p j).integrableOn_compact_subset hheight isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p j).integrableOn_compact_subset hheight isCompact_uIcc

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT

lemma periodic_deriv {f : ℝ → ℂ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  exact funext hf

lemma embedding_rectangular_period :
    3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) = (3*Real.sqrt 3:ℝ)*Complex.I := by
  rw [eisEmbedding_eval]
  norm_num only [Int.cast_one,Int.cast_ofNat]
  unfold EisensteinEmbedding.omega3
  push_cast
  ring

lemma actual_axis_periodic_zero (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 0) 3 := by
  intro x
  have h := upperEisenstein_periodic (1:O) ((x:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv s hs
  have hz : ((x+3:ℝ):ℂ)+(p 1:ℂ)*Complex.I =
      ((x:ℂ)+(p 1:ℂ)*Complex.I)+3*eisEmbedding (1:O) := by simp; ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    dite_false,dite_true]
  simp only [dif_pos hv]
  rw [hz]
  exact h

lemma actual_axis_periodic_one (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hv : 0<p 2) :
    Function.Periodic (axisSlice (upperEisensteinField s) p 1) (3*Real.sqrt 3) := by
  intro y
  have h := upperEisenstein_periodic (ActualEisensteinCoordinates.eval 1 2)
    ((p 0:ℂ)+(y:ℂ)*Complex.I) (p 2) hv s hs
  have hz : (p 0:ℂ)+((y+3*Real.sqrt 3:ℝ):ℂ)*Complex.I =
      ((p 0:ℂ)+(y:ℂ)*Complex.I)+3*eisEmbedding (ActualEisensteinCoordinates.eval 1 2) := by
    rw [embedding_rectangular_period]
    push_cast
    ring
  unfold axisSlice upperEisensteinField
  simp only [Function.update,show (0:Fin 3)≠1 by decide,show (2:Fin 3)≠1 by decide,
    dite_false,dite_true]
  simp only [dif_pos hv]
  rw [hz]
  exact h

lemma green_periodic_zero {f g : ℝ → ℂ} {T : ℝ}
    (hf : Function.Periodic f T) (hg : Function.Periodic g T) :
    (deriv f T*star (g T)-f T*star (deriv g T)) -
      (deriv f 0*star (g 0)-f 0*star (deriv g 0)) = 0 := by
  have hf0 : f T=f 0 := by simpa only [zero_add] using hf 0
  have hg0 : g T=g 0 := by simpa only [zero_add] using hg 0
  have hdf : deriv f T=deriv f 0 := by simpa only [zero_add] using periodic_deriv hf 0
  have hdg : deriv g T=deriv g 0 := by simpa only [zero_add] using periodic_deriv hg 0
  rw [hf0,hg0,hdf,hdg,sub_self]

theorem actual_green_real_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..3,
      deriv (deriv (axisSlice (upperEisensteinField s) p 0)) x *
        star (axisSlice (upperEisensteinField t) p 0 x) -
      axisSlice (upperEisensteinField s) p 0 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 0)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 0 0 3]
  · exact green_periodic_zero (actual_axis_periodic_zero s hs p hv) (actual_axis_periodic_zero t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠0 by decide)] using hv

theorem actual_green_imag_period_zero (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∫x in (0:ℝ)..(3*Real.sqrt 3),
      deriv (deriv (axisSlice (upperEisensteinField s) p 1)) x *
        star (axisSlice (upperEisensteinField t) p 1 x) -
      axisSlice (upperEisensteinField s) p 1 x *
        star (deriv (deriv (axisSlice (upperEisensteinField t) p 1)) x)) = 0 := by
  rw [actual_eisenstein_green_interval s t hs ht p 1 0 (3*Real.sqrt 3)]
  · exact green_periodic_zero (actual_axis_periodic_one s hs p hv) (actual_axis_periodic_one t ht p hv)
  · intro x hx
    simpa only [Function.update_of_ne (show (2:Fin 3)≠1 by decide)] using hv

def cuspRectangle : Set (ℝ × ℝ) := Set.Icc 0 3 ×ˢ Set.Icc 0 (3*Real.sqrt 3)

lemma cuspRectangle_volume : volume cuspRectangle = ENNReal.ofReal (9*Real.sqrt 3) := by
  rw [cuspRectangle,MeasureTheory.Measure.volume_eq_prod,MeasureTheory.Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
  norm_num only [sub_zero]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

lemma cuspRectangle_volume_twice_period : volume cuspRectangle = 2*volume periodDomain := by
  rw [cuspRectangle_volume,periodDomain_volume]
  have h2 : (2:ENNReal)=ENNReal.ofReal (2:ℝ) := by norm_num
  rw [h2,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  ring

lemma rectangular_period_change_of_basis :
    (3:ℂ)=periodBasis 0 ∧
    (3*Real.sqrt 3:ℝ)*Complex.I=periodBasis 0+2*periodBasis 1 := by
  constructor
  · exact periodBasis_zero.symm
  · rw [periodBasis_zero,periodBasis_one]
    unfold EisensteinEmbedding.omega3
    push_cast
    ring

lemma rectangular_period_matrix_det :
    Matrix.det (!![(1:ℤ),1;0,2]) = 2 := by norm_num [Matrix.det_fin_two]

end CubicEisenstein

end

end OAI

end


