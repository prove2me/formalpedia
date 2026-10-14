-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0117
-- name    : PNT_ZeroFree_433_0117
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:31:40.411321+00:00
-- url     : https://prove2.me/theorems/888551b4-e361-458b-bbb6-b5592f388286
-- title:
--   Zero-free region foundations: Eisenstein.SmoothCuspCutoffs [0117]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SmoothCuspCutoffs
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SmoothCuspCutoffs.lean#L365-L632

import Definitions.Def_PNT_ZeroFree_433_0117_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SmoothCuspCutoffs.lean
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

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff


open CubicKubota


lemma smoothCuspSeed_incoming (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (z : ℂ) (v : ℝ) (hv : 0<v) (hbv : b≤v) :
    smoothCuspSeed a b s (upperPoint z v hv)=(v:ℂ)^s := by
  rw [smoothCuspSeed,cuspCutoffCorrection_upperPoint _ z v hv (lt_of_lt_of_le (ha.trans hab) hbv)]
  exact cuspSeedProfile_incoming a b s v hab hbv hv

lemma smoothCuspSeedDefect_support (a b : ℝ) (s : ℂ) (hab : a<b) (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect a b s w≠0) :
    ∃r : CuspCosets, a≤cosetHeight r w ∧ cosetHeight r w≤b := by
  by_contra hn
  apply hw
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  calc
    _ = ∑'r : CuspCosets, (0:ℂ) := by
      apply tsum_congr
      intro r
      have hout : cosetHeight r w<a ∨ b<cosetHeight r w := by
        have h := not_exists.mp hn r
        simpa only [not_and_or,not_le] using h
      simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
    _ = 0 := tsum_zero

end

open Filter
open scoped BigOperators Classical Topology ContDiff

def rowLogHeight (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℝ :=
  Real.log (p 2)-Real.log (quadraticHeightDenominator (Complex.normSq (u 0))
    (u 0*star (u 1)).re (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2))

lemma exp_rowLogHeight (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    Real.exp (rowLogHeight u p)=rowHeight u p := by
  rw [rowLogHeight,Real.exp_sub,Real.exp_log hp,Real.exp_log (row_denominator_pos u hu p hp)]
  rfl

lemma hasDerivAt_deriv_log_ratio (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t,HasDerivAt f (df t) t) (hg : ∀t,HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x≠0) (hg0 : g x≠0) :
    HasDerivAt (deriv (fun t => Real.log (f t)-Real.log (g t)))
      ((ddf*f x-df x*df x)/(f x)^2-(ddg*g x-dg x*dg x)/(g x)^2) x := by
  have heq : deriv (fun t => Real.log (f t)-Real.log (g t)) =ᶠ[𝓝 x]
      (fun t => df t/f t-dg t/g t) := by
    filter_upwards [((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)] with t ht
    exact (((hf t).log ht.1).sub ((hg t).log ht.2)).deriv
  exact ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).congr_of_eventuallyEq heq

lemma rowLogHeight_hasDerivAt (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (fun t => rowLogHeight u (Function.update p j t)) (rowLogD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := ((hasDerivAt_const (p 0) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_const (p 1) (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := ((hasDerivAt_id (p 2)).log hp.ne').sub
      ((quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)).log hq)
    simpa [rowLogHeight,rowLogD,spatialLogD,heightLogDv,Function.update,A,B,C,D,Pi.sub_def] using! h

lemma rowLogHeight_hasDerivAt_deriv (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (fun t => rowLogHeight u (Function.update p j t))) (rowLogDD u p j) (p j) := by
  let A := Complex.normSq (u 0)
  let B := (u 0*star (u 1)).re
  let C := -(u 0*star (u 1)).im
  let D := Complex.normSq (u 1)
  have hq := (row_denominator_pos u hu p hp).ne'
  fin_cases j
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDxx,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDyy,Function.update,A,B,C,D,Pi.sub_def] using! h
  · have h := hasDerivAt_deriv_log_ratio id
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hp.ne' hq
    simpa [rowLogHeight,rowLogDD,spatialLogDD,heightLogDvv,Function.update,A,B,C,D,div_eq_mul_inv] using h

lemma complex_profile_second_chain (F : ℝ → ℂ) (g : ℝ → ℝ) (x dg ddg : ℝ) (dF ddF : ℂ)
    (hg : HasDerivAt g dg x) (hdg : HasDerivAt (deriv g) ddg x)
    (hF : HasDerivAt F dF (g x)) (hdF : HasDerivAt (deriv F) ddF (g x))
    (hlocal : ∀ᶠy in 𝓝 x,DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ F (g y)) :
    HasDerivAt (deriv (fun y => F (g y))) (ddF*(dg:ℂ)^2+dF*(ddg:ℂ)) x := by
  have heq : deriv (fun y => F (g y)) =ᶠ[𝓝 x]
      (fun y => (deriv g y:ℝ) • deriv F (g y)) := by
    filter_upwards [hlocal] with y hy
    exact (hy.2.hasDerivAt.scomp y hy.1.hasDerivAt).deriv
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert! hdg.smul (hdF.scomp x hg) using 1
  all_goals simp only [Function.comp_apply,hg.deriv,hF.deriv,Complex.real_smul]
  all_goals ring

lemma positiveProfile_differentiable (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (v : ℝ) (hv : 0<v) :
    DifferentiableAt ℝ F v ∧ DifferentiableAt ℝ (deriv F) v :=
  ⟨(hF v hv).differentiableAt (by simp),
    ((hF v hv).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)⟩

lemma positiveProfile_exp_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (t : ℝ) :
    HasDerivAt (fun y => F (Real.exp y))
      (deriv F (Real.exp t)*(Real.exp t:ℂ)) t ∧
    HasDerivAt (deriv (fun y => F (Real.exp y)))
      (deriv (deriv F) (Real.exp t)*(Real.exp t:ℂ)^2+
        deriv F (Real.exp t)*(Real.exp t:ℂ)) t := by
  have hdf := positiveProfile_differentiable F hF (Real.exp t) (Real.exp_pos t)
  constructor
  · simpa only [Complex.real_smul,mul_comm,Function.comp_def] using! hdf.1.hasDerivAt.scomp t (Real.hasDerivAt_exp t)
  · apply complex_profile_second_chain F Real.exp t (Real.exp t) (Real.exp t)
      (deriv F (Real.exp t)) (deriv (deriv F) (Real.exp t)) (Real.hasDerivAt_exp t)
      (by simpa only [Real.deriv_exp] using Real.hasDerivAt_exp t) hdf.1.hasDerivAt hdf.2.hasDerivAt
    exact Filter.Eventually.of_forall (fun y =>
      ⟨Real.differentiable_exp y,(positiveProfile_differentiable F hF _ (Real.exp_pos y)).1⟩)

lemma rowProfile_axis_derivatives (F : ℝ → ℂ)
    (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (fun q => F (rowHeight u q)) p j)
      (deriv F (rowHeight u p)*(rowHeight u p:ℂ)*(rowLogD u p j:ℂ)) (p j) ∧
    HasDerivAt (deriv (axisSlice (fun q => F (rowHeight u q)) p j))
      (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2*(rowLogD u p j:ℂ)^2+
       deriv F (rowHeight u p)*(rowHeight u p:ℂ)*
        ((rowLogD u p j:ℂ)^2+(rowLogDD u p j:ℂ))) (p j) := by
  let g : ℝ → ℝ := fun t => rowLogHeight u (Function.update p j t)
  let G : ℝ → ℂ := fun t => F (Real.exp t)
  have hg : HasDerivAt g (rowLogD u p j) (p j) := rowLogHeight_hasDerivAt u hu p hp j
  have hdg : HasDerivAt (deriv g) (rowLogDD u p j) (p j) := rowLogHeight_hasDerivAt_deriv u hu p hp j
  have hgval : g (p j)=rowLogHeight u p := by simp [g,Function.update_eq_self]
  have hexp : Real.exp (g (p j))=rowHeight u p := by rw [hgval,exp_rowLogHeight u hu p hp]
  have hG := positiveProfile_exp_derivatives F hF (g (p j))
  have hnear : ∀ᶠt in 𝓝 (p j),0<(Function.update p j t) 2 :=
    ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
      (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
  have heq : axisSlice (fun q => F (rowHeight u q)) p j =ᶠ[𝓝 (p j)] (fun t => G (g t)) := by
    filter_upwards [hnear] with t ht
    change F (rowHeight u (Function.update p j t))=F (Real.exp (rowLogHeight u (Function.update p j t)))
    rw [exp_rowLogHeight u hu _ ht]
  constructor
  · have hh := hG.1.scomp (p j) hg
    apply HasDerivAt.congr_of_eventuallyEq _ heq
    convert! hh using 1
    all_goals simp only [Complex.real_smul,hexp]
    all_goals ring
  · have hlocal : ∀ᶠy in 𝓝 (p j),DifferentiableAt ℝ g y ∧ DifferentiableAt ℝ G (g y) := by
      filter_upwards [hnear] with y hy
      constructor
      · have h := rowLogHeight_hasDerivAt u hu (Function.update p j y) hy j
        simpa only [Function.update_idem,Function.update_self] using h.differentiableAt
      · exact (positiveProfile_exp_derivatives F hF (g y)).1.differentiableAt
    have hh := complex_profile_second_chain G g (p j) (rowLogD u p j) (rowLogDD u p j)
      _ _ hg hdg hG.1 hG.2 hlocal
    apply HasDerivAt.congr_of_eventuallyEq _ heq.deriv
    convert! hh using 1
    · rw [hexp]
      ring

lemma rowLog_eikonal (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*((rowLogD u p 0)^2+(rowLogD u p 1)^2+(rowLogD u p 2)^2)=1 := by
  exact heightLog_eikonal _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'
lemma rowLog_laplacian (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    (p 2)^2*(rowLogDD u p 0+rowLogDD u p 1+rowLogDD u p 2)-(p 2)*rowLogD u p 2= -2 := by
  exact heightLog_laplacian _ _ _ _ _ _ _ (complex_row_quadratic_relation (u 0) (u 1)) hp.ne'
    (row_denominator_pos u hu p hp).ne'

theorem rowProfile_laplacian (F : ℝ → ℂ) (hF : ∀v,0<v→ContDiffAt ℝ ∞ F v)
    (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => F (rowHeight u q)) p=
      (rowHeight u p:ℂ)^2*deriv (deriv F) (rowHeight u p)-(rowHeight u p:ℂ)*deriv F (rowHeight u p) := by
  have hp0 := rowProfile_axis_derivatives F hF u hu p hp 0
  have hp1 := rowProfile_axis_derivatives F hF u hu p hp 1
  have hp2 := rowProfile_axis_derivatives F hF u hu p hp 2
  unfold axisLaplacian
  rw [Fin.sum_univ_three,hp0.2.deriv,hp1.2.deriv,hp2.2.deriv,hp2.1.deriv]
  have hE := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_eikonal u hu p hp)
  have hD := congrArg (fun r : ℝ => (r:ℂ)) (rowLog_laplacian u hu p hp)
  push_cast at hE hD
  linear_combination
    (deriv (deriv F) (rowHeight u p)*(rowHeight u p:ℂ)^2+
      deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hE+
    (deriv F (rowHeight u p)*(rowHeight u p:ℂ))*hD

open Filter
open scoped BigOperators Classical Topology ContDiff

lemma axisLaplacian_congr_eventuallyEq (f g : SpatialCoordinates → ℂ) (p : SpatialCoordinates)
    (heq : f =ᶠ[𝓝 p] g) : axisLaplacian f p=axisLaplacian g p := by
  have haxis (j : Fin 3) : axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
    have ht : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 p) := by
      have h : Tendsto (fun x => Function.update p j x) (𝓝 (p j)) (𝓝 (Function.update p j (p j))) :=
        (continuous_axis_update p j).continuousAt
      simpa only [Function.update_eq_self] using h
    exact heq.comp_tendsto ht
  unfold axisLaplacian
  congr 1
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => (haxis j).deriv.deriv_eq)
  · rw [(haxis 2).deriv_eq]

lemma axisLaplacian_const_mul (c : ℂ) (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) :
    axisLaplacian (fun q => c*f q) p=c*axisLaplacian f p := by
  unfold axisLaplacian
  simp only [Fin.sum_univ_three]
  unfold axisSlice
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

lemma axisLaplacian_finset_sum {ι : Type*} (S : Finset ι) (f : ι → SpatialCoordinates → ℂ)
    (hreg : ∀i∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f i) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f i) q j)) (q j))
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => ∑i∈S,f i q) p=∑i∈S,axisLaplacian (f i) p := by
  have hpair (j : Fin 3) :
      deriv (axisSlice (fun q => ∑i∈S,f i q) p j) (p j)=∑i∈S,deriv (axisSlice (f i) p j) (p j) ∧
      deriv (deriv (axisSlice (fun q => ∑i∈S,f i q) p j)) (p j)=
        ∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j) := by
    have hfirst (x : ℝ) (hx : 0<(Function.update p j x) 2) :
        HasDerivAt (axisSlice (fun q => ∑i∈S,f i q) p j)
          (∑i∈S,deriv (axisSlice (f i) p j) x) x := by
      have hi (i : ι) (hiS : i∈S) : DifferentiableAt ℝ (axisSlice (f i) p j) x := by
        simpa only [axisSlice_update,Function.update_self] using (hreg i hiS (Function.update p j x) hx j).1
      convert! HasDerivAt.sum (fun i hiS => (hi i hiS).hasDerivAt) using 1
      ext y
      simp only [axisSlice,Finset.sum_apply]
    have hnear : ∀ᶠx in 𝓝 (p j),0<(Function.update p j x) 2 :=
      ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
        (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)
    have heq : deriv (axisSlice (fun q => ∑i∈S,f i q) p j) =ᶠ[𝓝 (p j)]
        (fun x => ∑i∈S,deriv (axisSlice (f i) p j) x) := by
      filter_upwards [hnear] with x hx
      exact (hfirst x hx).deriv
    have hsecond : HasDerivAt (deriv (axisSlice (fun q => ∑i∈S,f i q) p j))
        (∑i∈S,deriv (deriv (axisSlice (f i) p j)) (p j)) (p j) := by
      apply (HasDerivAt.sum (fun i hiS => (hreg i hiS p hp j).2.hasDerivAt)).congr_of_eventuallyEq
      filter_upwards [heq] with x hx
      simpa only [Finset.sum_apply] using hx
    exact ⟨(hfirst (p j) (by simpa only [Function.comp_apply,Function.update_eq_self] using hp)).deriv,hsecond.deriv⟩
  unfold axisLaplacian
  simp_rw [(hpair _).1,(hpair _).2]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum,Finset.sum_sub_distrib]

end CubicEisenstein

end

end OAI

end


