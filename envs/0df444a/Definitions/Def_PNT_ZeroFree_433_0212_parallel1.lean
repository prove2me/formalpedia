-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0212_parallel1
-- name    : PNT_ZeroFree_433_0212_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:28:48.259075+00:00
-- url     : https://prove2.me/theorems/cc289b94-737b-495a-b505-566849f1c59d
-- title:
--   Zero-free region foundations: Eisenstein.CutoffApproximation [0212_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.CutoffApproximation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CutoffApproximation.lean#L85-L434

import Definitions.Def_PNT_ZeroFree_433_0104
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0117
import Definitions.Def_PNT_ZeroFree_433_0118
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0206_parallel1
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/CutoffApproximation.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace CubicEisenstein

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold

section BoundedConvergence
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] («μ» : Measure α)

omit [CompleteSpace E] in
lemma l2_norm_sq_integral (f : Lp E 2 «μ») : ‖f‖^2=∫a,‖f a‖^2∂«μ» := by
  calc
    ‖f‖^2=inner ℝ f f := (real_inner_self_eq_norm_sq f).symm
    _ = ∫a,inner ℝ (f a) (f a)∂«μ» := L2.inner_def _ _
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
lemma l2_toLp_sub_norm_sq (f g : α→E) (hf : MemLp f 2 «μ») (hg : MemLp g 2 «μ») :
    ‖hf.toLp f-hg.toLp g‖^2=∫a,‖f a-g a‖^2∂«μ» := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g),hf.coeFn_toLp,hg.coeFn_toLp] with a ha hf hg
  rw [ha]
  simp only [Pi.sub_apply,hf,hg]

omit [CompleteSpace E] in
theorem l2_tendsto_of_bounded_eventuallyEq [IsFiniteMeasure «μ»]
    (f : ℕ→α→E) (g : α→E) (hf : ∀n,MemLp (f n) 2 «μ») (hg : MemLp g 2 «μ»)
    (B C : ℝ) (hB : 0≤B) (hC : 0≤C)
    (hfB : ∀n a,‖f n a‖≤B) (hgC : ∀a,‖g a‖≤C)
    (hlim : ∀a,∀ᶠn : ℕ in atTop,f n a=g a) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hsq : Tendsto (fun n => ∫a,‖f n a-g a‖^2∂«μ») atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence («μ» := «μ»)
      (F := fun n a => ‖f n a-g a‖^2) (f := fun _ => (0:ℝ)) (fun _ => (B+C)^2)
      (fun n => ((hf n).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
      (integrable_const _) ?_ ?_
    · simpa only [integral_zero] using h
    · intro n
      exact Eventually.of_forall (fun a => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        apply (sq_le_sq₀ (norm_nonneg _) (add_nonneg hB hC)).mpr
        exact (norm_sub_le _ _).trans (add_le_add (hfB n a) (hgC a)))
    · exact Eventually.of_forall (fun a => by
        apply tendsto_const_nhds.congr'
        filter_upwards [hlim a] with n hn
        simp only [hn,sub_self,norm_zero,zero_pow (by decide : 2≠0)])
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) atTop (𝓝 0) := by
    simpa only [l2_toLp_sub_norm_sq] using hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hsqrt

end BoundedConvergence


lemma norm_three_vector_bound (v : EuclideanSpace ℂ (Fin 3)) (B : ℝ) (hB : 0≤B)
    (hv : ∀j,‖v j‖≤B) : ‖v‖≤3*B := by
  have hsq : ‖v‖^2≤3*B^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑j : Fin 3,B^2 := Finset.sum_le_sum (fun j hj =>
        (sq_le_sq₀ (norm_nonneg _) hB).mpr (hv j))
      _ = _ := by simp
  nlinarith [norm_nonneg v,sq_nonneg B]


section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold Matrix

lemma axis_update_contDiff (p : SpatialCoordinates) (j : Fin 3) :
    ContDiff ℝ ∞ (fun t => Function.update p j t) := by
  apply contDiff_pi.mpr
  intro k
  by_cases h : k=j
  · subst k
    simpa only [Function.update_self,id_eq] using! (contDiff_id : ContDiff ℝ ∞ (fun t : ℝ => t))
  · simpa only [Function.update_of_ne h] using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => p k))

lemma smooth_positive_axis_regular (f : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice f p j) (p j) ∧
      DifferentiableAt ℝ (deriv (axisSlice f p j)) (p j) := by
  have hh : ContDiffAt ℝ ∞ (axisSlice f p j) (p j) := by
    have hfp : ContDiffAt ℝ ∞ f (Function.update p j (p j)) := by
      simpa only [Function.update_eq_self] using hf p hp
    have h := hfp.comp (p j) (axis_update_contDiff p j).contDiffAt
    simpa only [axisSlice,Function.comp_def,Function.update_eq_self] using! h
  exact ⟨hh.differentiableAt (by simp),(hh.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma axisLaplacian_sub_smooth (f g : SpatialCoordinates→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (hg : ∀p,0<p 2→ContDiffAt ℝ ∞ g p)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => f q-g q) p=axisLaplacian f p-axisLaplacian g p := by
  let F : Fin 2→SpatialCoordinates→ℂ:=![f,fun q => (-1:ℂ)*g q]
  have hF : ∀i : Fin 2,∀q,0<q 2→ContDiffAt ℝ ∞ (F i) q := by
    intro i q hq
    fin_cases i
    · exact hf q hq
    · exact contDiffAt_const.mul (hg q hq)
  have hh := axisLaplacian_finset_sum Finset.univ F
    (fun i hi q hq j => smooth_positive_axis_regular (F i) (hF i) q hq j) p hp
  have he : (fun q => ∑i : Fin 2,F i q)=(fun q => f q-g q) := by
    funext q
    simp [F,Fin.sum_univ_two,sub_eq_add_neg]
  rw [he] at hh
  simp only [Fin.sum_univ_two,F,Matrix.cons_val_zero,Matrix.cons_val_one] at hh
  rw [axisLaplacian_const_mul] at hh
  simpa only [neg_one_mul,sub_eq_add_neg] using hh

lemma eisensteinRemainder_coordinate_equation (a b : ℝ) (ha : 1<a) (hab : a<b)
    (s : ℂ) (hs : 2<s.re) (p : SpatialCoordinates) (hp : 0<p 2) :
    -axisLaplacian (eisensteinRemainderField a b s) p=
      smoothCuspSeedDefectField a b s p+s*(2-s)*eisensteinRemainderField a b s p := by
  have hD := actual_smoothCuspSeed_laplace_defect a b s ha hab p hp
  unfold eisensteinRemainderField
  rw [axisLaplacian_sub_smooth _ _ (smoothEisenstein_contDiffAt s hs)
    (actual_smoothCuspSeed_contDiffAt a b s ha hab) p hp,smoothEisenstein_eigenfunction s hs p hp]
  linear_combination hD


end


end CubicEisenstein

end

end OAI

end


