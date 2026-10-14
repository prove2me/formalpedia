-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0110
-- name    : PNT_ZeroFree_433_0110
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:19:22.800287+00:00
-- url     : https://prove2.me/theorems/af323c6e-888a-4078-8d08-550141d1a534
-- title:
--   Zero-free region foundations: Eisenstein.GreenIdentity [0110]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/GreenIdentity.lean#L77-L694

import Definitions.Def_PNT_ZeroFree_433_0109

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/GreenIdentity.lean#L77-L694
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Eisenstein.GreenIdentity
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

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology

def greenWronskian (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x*star (g x)-f x*star (deriv g x)

def greenSecondTerm (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv (deriv f) x*star (g x)-f x*star (deriv (deriv g) x)

lemma hasDerivAt_greenWronskian (f g : ℝ → ℂ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hdf : DifferentiableAt ℝ (deriv f) x) (hdg : DifferentiableAt ℝ (deriv g) x) :
    HasDerivAt (greenWronskian f g) (greenSecondTerm f g x) x := by
  convert! ((hdf.hasDerivAt.mul hg.hasDerivAt.star).sub
    (hf.hasDerivAt.mul hdg.hasDerivAt.star)) using 1
  all_goals dsimp [greenSecondTerm, greenWronskian]
  all_goals ring

lemma weighted_vertical_green (f g : ℝ → ℂ) (a b : ℝ)
    (hpos : ∀x∈Set.uIcc a b,0<x)
    (hf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ f x)
    (hg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ g x)
    (hdf : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv f) x)
    (hdg : ∀x∈Set.uIcc a b,DifferentiableAt ℝ (deriv g) x)
    (hif : IntervalIntegrable (deriv (deriv f)) volume a b)
    (hig : IntervalIntegrable (deriv (deriv g)) volume a b) :
    (∫x in a..b, greenSecondTerm f g x/(x:ℂ)-greenWronskian f g x/(x:ℂ)^2) =
      greenWronskian f g b/(b:ℂ)-greenWronskian f g a/(a:ℂ) := by
  have hfc : ContinuousOn f (Set.uIcc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hgc : ContinuousOn g (Set.uIcc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hdfc : ContinuousOn (deriv f) (Set.uIcc a b) := fun x hx => (hdf x hx).continuousAt.continuousWithinAt
  have hdgc : ContinuousOn (deriv g) (Set.uIcc a b) := fun x hx => (hdg x hx).continuousAt.continuousWithinAt
  have hW : ContinuousOn (greenWronskian f g) (Set.uIcc a b) :=
    (hdfc.mul hgc.star).sub (hfc.mul hdgc.star)
  have hne : ∀x∈Set.uIcc a b,(x:ℂ)≠0 := fun x hx => Complex.ofReal_ne_zero.mpr (hpos x hx).ne'
  have hstar : IntervalIntegrable (fun x => star (deriv (deriv g) x)) volume a b := by
    apply hig.mono_fun ((aestronglyMeasurable_deriv (deriv g) _).star)
    exact Filter.Eventually.of_forall (fun x => by simp only [Pi.star_apply,norm_star,le_refl])
  have hG : IntervalIntegrable (greenSecondTerm f g) volume a b :=
    (hif.mul_continuousOn hgc.star).sub (hstar.continuousOn_mul hfc)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have h := (hasDerivAt_greenWronskian f g x (hf x hx) (hg x hx) (hdf x hx) (hdg x hx)).div
      ((hasDerivAt_id x).ofReal_comp) (hne x hx)
    convert! h using 1
    all_goals simp only [id_eq,Complex.ofReal_one,mul_one]
    all_goals field_simp [hne x hx]
    all_goals ring

  · have hi₁ := hG.mul_continuousOn (Complex.continuous_ofReal.continuousOn.inv₀ hne)
    have hi₂ : IntervalIntegrable (fun x : ℝ => greenWronskian f g x/(x:ℂ)^2) volume a b :=
      (hW.div (Complex.continuous_ofReal.continuousOn.pow 2)
        (fun x hx => pow_ne_zero 2 (hne x hx))).intervalIntegrable
    simpa only [div_eq_mul_inv,Pi.inv_apply] using hi₁.sub hi₂

theorem actual_eisenstein_vertical_green (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    (∫v in a..b,
      greenSecondTerm (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) v/(v:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) v/(v:ℂ)^2) =
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) b/(b:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) a/(a:ℂ) := by
  have hpos (x : ℝ) (hx : x∈Set.uIcc a b) : 0<x :=
    lt_of_lt_of_le (lt_min ha hb) hx.1
  have hsafe (x : ℝ) (hx : x∈Set.uIcc a b) : 0<(Function.update p 2 x) 2 := by
    simpa only [Function.update_self] using hpos x hx
  apply weighted_vertical_green _ _ a b hpos
  · exact fun x hx => (actual_axis_differentiable_at s hs p 2 x (hsafe x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at t ht p 2 x (hsafe x hx)).1
  · exact fun x hx => (actual_axis_differentiable_at s hs p 2 x (hsafe x hx)).2
  · exact fun x hx => (actual_axis_differentiable_at t ht p 2 x (hsafe x hx)).2
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable s hs p 2).integrableOn_compact_subset hsafe isCompact_uIcc
  · apply (intervalIntegrable_iff' (by finiteness)).mpr
    exact (actual_axis_second_locallyIntegrable t ht p 2).integrableOn_compact_subset hsafe isCompact_uIcc

lemma axisSlice_self (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) :
    axisSlice f p j (p j)=f p := by
  simp only [axisSlice,Function.update_eq_self]

theorem actual_eisenstein_green_density (s t : ℂ) (hs : 2<s.re) (ht : 2<t.re)
    (p : SpatialCoordinates) (hv : 0<p 2) :
    (∑j : Fin 3,greenSecondTerm (axisSlice (upperEisensteinField s) p j)
      (axisSlice (upperEisensteinField t) p j) (p j)) / (p 2:ℂ) -
      greenWronskian (axisSlice (upperEisensteinField s) p 2)
        (axisSlice (upperEisensteinField t) p 2) (p 2) / (p 2:ℂ)^2 =
    (s*(s-2)-star (t*(t-2))) * upperEisensteinField s p * star (upperEisensteinField t p) /
      (p 2:ℂ)^3 := by
  have hne : (p 2:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  calc
    _ = (axisLaplacian (upperEisensteinField s) p * star (upperEisensteinField t p) -
        upperEisensteinField s p * star (axisLaplacian (upperEisensteinField t) p)) / (p 2:ℂ)^3 := by
      simp only [greenSecondTerm,greenWronskian,axisSlice_self,axisLaplacian,
        Finset.sum_sub_distrib,← Finset.sum_mul,← Finset.mul_sum,map_sub,map_mul,map_pow,
        map_sum,Complex.star_def,Complex.conj_ofReal]
      field_simp [hne]
      ; ring
    _ = _ := by
      rw [upperEisenstein_eigenfunction s hs p hv,upperEisenstein_eigenfunction t ht p hv]
      simp only [star_mul]
      ring

end CubicEisenstein

namespace CanonicalQuadraticSieve

theorem symmetric_truncation_scales (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    0 < X ∧ 0 < X₀/T ∧ X₀/T ≤ X ∧ X ≤ T*X₀ ∧ 0 ≤ T^4 := by
  have hT0 : 0 < T := by linarith
  have hX : 0 < X := by linarith
  refine ⟨hX,div_pos hX₀ hT0,?_,?_,by positivity⟩
  · apply (div_le_iff₀ hT0).mpr
    nlinarith
  · nlinarith

theorem symmetric_truncation_scalar_bound (m : ℕ) (X₀ X T : ℝ) (hX₀ : 0 < X₀)
    (hlo : X₀/2 ≤ X) (hhi : X ≤ 2*X₀) (hT : 4 ≤ T) :
    ((X₀/T)/X)^(m+3) + 1/(1+(T*X₀)/X)^(m+3) +
      (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤
      (2 : ℝ)^(m+10)/T^m := by
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hX : 0 < X := by linarith
  have hY : 0 < X₀/T := div_pos hX₀ hT0
  have hratio : (X₀/T)/X ≤ 2/T := by
    apply (div_le_iff₀ hX).mpr
    calc
      X₀/T ≤ (2*X)/T := div_le_div_of_nonneg_right (by linarith) hT0.le
      _ = (2/T)*X := by ring
  have hinv : 1/(1+(T*X₀)/X) ≤ 2/T := by
    have hz : T/2 ≤ (T*X₀)/X := (le_div_iff₀ hX).mpr (by nlinarith)
    calc
      _ ≤ 1/(T/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = 2/T := by field_simp
  have hpow : (2/T)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hT0 m)
      (pow_le_pow_right₀ hT1 (by omega : m ≤ m+3))
  have h₁ : ((X₀/T)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m :=
    (pow_le_pow_left₀ (by positivity) hratio _).trans hpow
  have h₂ : 1/(1+(T*X₀)/X)^(m+3) ≤ (2 : ℝ)^(m+3)/T^m := by
    simpa only [div_pow,one_pow] using (pow_le_pow_left₀ (by positivity) hinv (m+3)).trans hpow
  have hnum : X/(X₀/T) ≤ 2*T := by
    apply (div_le_iff₀ hY).mpr
    have he : 2*T*(X₀/T) = 2*X₀ := by field_simp
    rw [he]
    exact hhi
  have hmin : 1/(2*T) ≤ min 1 (X/(T*X₀)) := by
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
      linarith
    · apply (le_div_iff₀ (mul_pos hT0 hX₀)).mpr
      have he : 1/(2*T)*(T*X₀)=X₀/2 := by field_simp
      rwa [he]
  have hfreq : T ≤ 1+X*T^4/(T*X₀) := by
    have ht2 : 2 ≤ T^2 := by nlinarith
    have ht4 : 2*T^2 ≤ T^4 := by nlinarith [sq_nonneg (T^2-2)]
    have hprod : T*(T*X₀) ≤ X*T^4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sq_nonneg (T^2))]
    have hh := (le_div_iff₀ (mul_pos hT0 hX₀)).mpr hprod
    linarith
  have hden : (1/(2*T))^2*T^(m+3) ≤
      (min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3) := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) hmin 2)
      (pow_le_pow_left₀ hT0.le hfreq (m+3)) (by positivity) (by positivity)
  have h₃ : (X/(X₀/T))/((min 1 (X/(T*X₀)))^2*(1+X*T^4/(T*X₀))^(m+3)) ≤ 8/T^m := by
    calc
      _ ≤ (2*T)/((1/(2*T))^2*T^(m+3)) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = _ := by rw [pow_add]; field_simp; ring
  have hc : 2*(2 : ℝ)^(m+3)+8 ≤ (2 : ℝ)^(m+10) := by
    have hm : 1 ≤ (2 : ℝ)^m := one_le_pow₀ (by norm_num)
    rw [pow_add,pow_add]
    norm_num
    nlinarith
  calc
    _ ≤ (2 : ℝ)^(m+3)/T^m + (2 : ℝ)^(m+3)/T^m + 8/T^m := add_le_add (add_le_add h₁ h₂) h₃
    _ = (2*(2 : ℝ)^(m+3)+8)/T^m := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)

def SecondSourceSupport {ι : Type*} [DecidableEq ι]
    (p : ι → O) (X M : ℝ) (x : SecondExpansionData ι) : Prop :=
  Disjoint x.sourceCommon x.overlap ∧
    primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in
theorem secondExpansionSource_singleton_zero_of_not_support
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (x : SecondExpansionData ι) (hE : x.divisor ⊆ x.sourceCommon)
    (hs : ¬ SecondSourceSupport p X M x) :
    secondExpansionSource p hp hcop hg F Ψ m c d z {x}
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y = 0 := by
  by_cases hd : Disjoint x.sourceCommon x.overlap
  · have hb : ¬ primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap ≤ X * Real.exp M :=
      fun hb => hs ⟨hd,hb⟩
    have hz (N : Finset ι) :
        normalizedColumn p (fun A => g (columnLog p X A))
          (x.sourceCommon ∪ (x.overlap ∪ N)) = 0 := by
      by_contra hn
      have h := normalizedColumn_subset_norm_bound p hp g M X hX hgM
        x.sourceCommon (x.overlap ∪ N) (x.sourceCommon ∪ x.overlap)
        (Finset.union_subset_union Finset.Subset.rfl Finset.subset_union_left) hn
      rw [FirstPassCubeLabels.primeProductNorm_union p _ _ hd] at h
      exact hb h
    simp only [secondExpansionSource, Finset.sum_singleton]
    have hk : secondChildKernelPair p hp hcop hg F x.overlap
        (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
        (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
        x.frequency (-x.frequency)
        (secondSourcePairKernel p
          (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S))
          (fun S => normalizedColumn p (fun A => g (columnLog p X A)) (x.sourceCommon ∪ S)) W Y) = 0 := by
      unfold secondChildKernelPair
      apply Finset.sum_eq_zero
      intro N hN
      apply Finset.sum_eq_zero
      intro Q hQ
      simp only [secondSourcePairKernel, hz N, star_zero, zero_mul, zero_div, mul_zero]
    rw [hk]
    ring
  · have hz := secondPreColumn_zero_of_common_overlap p hp hcop hg hinj
      (secondRayPlus Ψ z) m c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      (-x.frequency) (fun _ => 1) x.sourceCommon x.overlap (fun h => hd h.symm)
    rw [secondMaskQuotient_spec p x.divisor x.sourceCommon hE] at hz
    simp only [secondExpansionSource, Finset.sum_singleton,
      secondExpansionQuotient_of_subset p x hE, secondTotalWeight, secondCommonWeight, hz,
      mul_zero, zero_mul]

include hinj in

theorem secondExpansionSource_eq_supported
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (g W : 𝓢(ℝ, ℂ)) (X Y M : ℝ) (hX : 0 < X)
    (hgM : ∀ u, g u ≠ 0 → |u| ≤ M)
    (s : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ s, x.divisor ⊆ x.sourceCommon) :
    secondExpansionSource p hp hcop hg F Ψ m c d z s
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y =
    secondExpansionSource p hp hcop hg F Ψ m c d z
      (s.filter (SecondSourceSupport p X M))
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S)
      (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) W Y := by
  classical
  unfold secondExpansionSource
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p X M x
  · rw [if_pos hs]
  · rw [if_neg hs]
    have hz := secondExpansionSource_singleton_zero_of_not_support
      p hp hcop hg hinj F Ψ m c d z g W X Y M hX hgM x (hE x hx) hs
    simpa only [secondExpansionSource, Finset.sum_singleton] using hz

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def normLogBin (u : ℝ) : ℕ := ⌊Real.log u⌋₊
def normLogScale (j : ℕ) : ℝ := Real.exp (j : ℝ)

lemma normLogScale_pos (j : ℕ) : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one (j : ℕ) : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

lemma normLogBin_error (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ Real.log (u / normLogScale (normLogBin u)) ∧
      Real.log (u / normLogScale (normLogBin u)) ≤ 1 := by
  rw [Real.log_div (by linarith) (normLogScale_pos _).ne', normLogScale, Real.log_exp]
  exact ⟨sub_nonneg.mpr (Nat.floor_le (Real.log_nonneg hu)),
    by have h := Nat.lt_floor_add_one (Real.log u); dsimp [normLogBin]; linarith⟩

lemma normLogBin_scale_bounds (u : ℝ) (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

lemma normLogBin_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

abbrev SecondLogIndex := ℕ × ℕ × ℕ

def secondLogE (j : SecondLogIndex) : ℝ := normLogScale j.1
def secondLogV (j : SecondLogIndex) : ℝ := normLogScale j.2.1
def secondLogK (j : SecondLogIndex) : ℝ := normLogScale j.2.2

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondLogIndex (D : Finset ι) (x : SecondExpansionData ι) : SecondLogIndex :=
  (normLogBin (primeProductNorm p x.divisor), normLogBin (primeProductNorm p x.overlap),
    normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2))

def secondLogX (R : Finset ι) (X : ℝ) (j : SecondLogIndex) : ℝ :=
  X / (secondLogE j * secondLogV j * primeProductNorm p R)

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogX_pos (R : Finset ι) (X : ℝ) (hX : 0 < X) (j : SecondLogIndex) :
    0 < secondLogX p R X j := by
  exact div_pos hX (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp R))

omit [DecidableEq ι] in
lemma actualSecondRow_ne_zero (D E : Finset ι) (k : O) (hk : k ≠ 0) :
    actualSecondRow p D E k ≠ 0 :=
  mul_ne_zero (mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)) hk

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖eisEmbedding a‖^2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

include hp in

omit [DecidableEq ι] in
theorem secondLogIndex_coordinates (C D R : Finset ι) (X : ℝ) (hX : 0 < X)
    (x : SecondExpansionData ι) (hk : x.frequency ≠ 0) :
    let j := secondLogIndex p D x
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 := by
  dsimp only
  have hE := normLogBin_error (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)
  have hV := normLogBin_error (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)
  have hK := normLogBin_error (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)
    (element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk))
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hX0 := hX.ne'
  have hNE := (FirstPassCubeLabels.primeProductNorm_pos p hp x.divisor).ne'
  have he := (normLogScale_pos (normLogBin (primeProductNorm p x.divisor))).ne'
  have hv := (normLogScale_pos (normLogBin (primeProductNorm p x.overlap))).ne'
  have hratio :
      primeProductNorm p x.overlap * secondLogX p R X (secondLogIndex p D x) /
        secondExpansionScale p X (primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (expansionSupportData C D x) =
      (primeProductNorm p x.divisor / normLogScale (normLogBin (primeProductNorm p x.divisor))) *
        (primeProductNorm p x.overlap / normLogScale (normLogBin (primeProductNorm p x.overlap))) := by
    simp only [secondLogX, secondExpansionScale, expansionSupportData, secondLogIndex,
      secondLogE, secondLogV, primeSubsetGenerator_norm_eq_productNorm]
    field_simp

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change |Real.log (primeProductNorm p x.overlap * _ / _)| ≤ 2
    rw [hratio, Real.log_mul (div_ne_zero hNE he)
      (div_ne_zero (FirstPassCubeLabels.primeProductNorm_pos p hp x.overlap).ne' hv)]
    rw [abs_of_nonneg (add_nonneg hE.1 hV.1)]
    linarith [hE.2,hV.2]
  · simp only [secondSectorUd, expansionSupportData, primeSubsetGenerator_norm_eq_productNorm,
      div_self (FirstPassCubeLabels.primeProductNorm_pos p hp D).ne', Real.log_one, abs_zero]
    norm_num
  · change |Real.log (‖eisEmbedding _‖^2 / _)| ≤ 2
    rw [primeSubsetGenerator_norm_eq_productNorm]
    change |Real.log (primeProductNorm p x.divisor / normLogScale (normLogBin (primeProductNorm p x.divisor)))| ≤ 2
    rw [abs_of_nonneg hE.1]
    linarith [hE.2]
  · change |Real.log (primeProductNorm p x.overlap / normLogScale (normLogBin (primeProductNorm p x.overlap)))| ≤ 2
    rw [abs_of_nonneg hV.1]
    linarith [hV.2]
  · change |Real.log (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 /
      normLogScale (normLogBin (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)))| ≤ 2
    rw [abs_of_nonneg hK.1]
    linarith [hK.2]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_radial_scale (D R : Finset ι) (X Y : ℝ) (hX : X ≠ 0) (j : SecondLogIndex) :
    Y * secondLogK j / (primeProductNorm p D * (secondLogE j)^2 *
      (secondLogV j)^2 * (secondLogX p R X j)^2) =
    Y * secondLogK j * (primeProductNorm p R)^2 / (primeProductNorm p D * X^2) := by
  unfold secondLogX secondLogE secondLogV secondLogK normLogScale
  field_simp

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondBaseLabel (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : O :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂

include hp in
omit [DecidableEq ι] in
lemma secondBaseLabel_ne_zero (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    secondBaseLabel p B C v₁ v₂ ε₁ ε₂ ≠ 0 := by
  apply mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact pow_ne_zero _ (hp i)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSupportNewLabel_norm (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    (Ideal.absNorm (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x)) : ℝ) =
      ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 *
        primeProductNorm p x.divisor * primeProductNorm p x.overlap := by
  rw [← secondSupportLabel_span, ← eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [secondSupportLabel, expansionSupportData, secondBaseLabel,
    map_mul, norm_mul, mul_pow, primeSubsetGenerator_norm_eq_productNorm, primeProductNorm]

include hp in
omit [DecidableEq ι] in
lemma secondSupportNewLabel_ne_bot (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) :
    secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x) ≠ ⊥ := by
  rw [← secondSupportLabel_span, ne_eq, Ideal.span_singleton_eq_bot]
  exact mul_ne_zero (mul_ne_zero (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator_ne_zero _ _)) (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

def secondLogLabelBound (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (j : SecondLogIndex) : ℝ :=
  ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 * secondLogE j * secondLogV j * Real.exp 2

include hp in
omit [DecidableEq ι] in
lemma secondLogLabelBound_ge_one (B C : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (j : SecondLogIndex) : 1 ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))
        (normLogScale_ge_one _)) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

include hp in

omit [DecidableEq ι] in
theorem secondLogIndex_target_bounds (B C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) (hk : x.frequency ≠ 0) :
    (Ideal.absNorm (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x)) : ℝ) ≤
        secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ (secondLogIndex p D x) ∧
    ‖eisEmbedding (secondSupportRow p (expansionSupportData C D x))‖^2 ≤
        secondLogK (secondLogIndex p D x) * Real.exp 1 := by
  have hE := (normLogBin_scale_bounds (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)).2
  have hV := (normLogBin_scale_bounds (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)).2
  have hK := (normLogBin_scale_bounds (‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2)
    (element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk))).2
  refine ⟨?_, hK⟩
  rw [secondSupportNewLabel_norm]
  calc
    _ ≤ ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 *
        (normLogScale (normLogBin (primeProductNorm p x.divisor))*Real.exp 1) *
        (normLogScale (normLogBin (primeProductNorm p x.overlap))*Real.exp 1) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hE (sq_nonneg _)) hV
        (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
        (mul_nonneg (sq_nonneg _) (mul_pos (normLogScale_pos _) (Real.exp_pos _)).le)
    _ = _ := by
      simp only [secondLogLabelBound, secondLogIndex, secondLogE, secondLogV]
      rw [show (2:ℝ)=1+1 by norm_num, Real.exp_add]
      ring

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_label_cost (B C R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (X : ℝ) (j : SecondLogIndex) :
    secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j =
      X * ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2 * Real.exp 2 /
        primeProductNorm p R := by
  unfold secondLogX secondLogLabelBound secondLogE secondLogV normLogScale
  field_simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def secondLogBinBox (U K : ℝ) : Finset SecondLogIndex :=
  Finset.range (normLogBin U + 1) ×ˢ
    (Finset.range (normLogBin U + 1) ×ˢ Finset.range (normLogBin K + 1))

lemma secondLogBinBox_card (U K : ℝ) :
    (secondLogBinBox U K).card = (normLogBin U + 1)^2 * (normLogBin K + 1) := by
  simp only [secondLogBinBox, Finset.card_product, Finset.card_range]
  ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondSourceSupport_bounds (X M : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon) :
    primeProductNorm p x.sourceCommon ≤ X*Real.exp M ∧
    primeProductNorm p x.divisor ≤ X*Real.exp M ∧
    primeProductNorm p x.overlap ≤ X*Real.exp M := by
  have hG := (le_mul_of_one_le_right (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.overlap)).trans hx.2
  have hV := (le_mul_of_one_le_left (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
    (primeProductNorm_ge_one p hp x.sourceCommon)).trans hx.2
  exact ⟨hG, (primeProductNorm_mono p hp hE).trans hG, hV⟩

include hp in
lemma secondLogIndex_mem_box (D : Finset ι) (X M K : ℝ) (x : SecondExpansionData ι)
    (hx : SecondSourceSupport p X M x) (hE : x.divisor ⊆ x.sourceCommon)
    (hk : x.frequency ≠ 0)
    (hK : ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ K) :
    secondLogIndex p D x ∈ secondLogBinBox (X*Real.exp M) K := by
  obtain ⟨hG,hE',hV⟩ := secondSourceSupport_bounds p hp X M x hx hE
  simp only [secondLogBinBox, secondLogIndex, Finset.mem_product, Finset.mem_range,
    Nat.lt_succ_iff]
  exact ⟨normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hE',
    normLogBin_mono (FirstPassCubeLabels.primeProductNorm_pos p hp _) hV,
    normLogBin_mono (by have h := element_norm_ge_one _ (actualSecondRow_ne_zero p D x.divisor x.frequency hk); linarith) hK⟩

def secondSupportedSector (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) : Finset (SecondExpansionData ι) :=
  (secondExpansionSector F (fun G E => (K G E).erase 0) R).filter (SecondSourceSupport p X M)

def secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) : Finset (SecondExpansionData ι) :=
  (secondSupportedSector p F K R X M).filter (fun x => secondLogIndex p D x = j)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSupportedSector_mem (F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
      x.frequency ≠ 0 ∧ x.frequency ∈ K x.sourceCommon x.divisor ∧
      x.sourceCommon \ x.divisor = R ∧ SecondSourceSupport p X M x := by
  obtain ⟨hx,hs⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hr⟩ := Finset.mem_filter.mp hx
  obtain ⟨hG,hE,hV,hk⟩ := (mem_secondExpansionPool _ _ _).mp hx
  obtain ⟨hk0,hk⟩ := Finset.mem_erase.mp hk
  exact ⟨hG,hE,hV,hk0,hk,hr,hs⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondLogSector_subset (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondLogSector p D F K R X M j ⊆ secondExpansionSector F (fun G E => (K G E).erase 0) R :=
  (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

include hp in

theorem sum_secondLogSector (D F : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (R : Finset ι) (X M Kmax : ℝ)
    (hK : ∀ x ∈ secondSupportedSector p F K R X M,
      ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax)
    (H : SecondExpansionData ι → ℂ) :
    (∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
      ∑ x ∈ secondLogSector p D F K R X M j, H x) =
      ∑ x ∈ secondSupportedSector p F K R X M, H x := by
  simp only [secondLogSector, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have hj := secondLogIndex_mem_box p hp D X M Kmax x hs hE hk0 (hK x hx)
  rw [Finset.sum_eq_single_of_mem (secondLogIndex p D x) hj]
  · simp
  · intro j hj hne
    simp [Ne.symm hne]

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogX_lower (D F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hX : 0 < X) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    Real.exp (-M) ≤ secondLogX p R X (secondLogIndex p D x) := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have he := (normLogBin_scale_bounds (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)).1
  have hv := (normLogBin_scale_bounds (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)).1
  have hGR : primeProductNorm p x.sourceCommon = primeProductNorm p x.divisor * primeProductNorm p R := by
    rw [← hr, ← FirstPassCubeLabels.primeProductNorm_union p x.divisor (x.sourceCommon\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hE]
  have hprod : secondLogE (secondLogIndex p D x) * secondLogV (secondLogIndex p D x) * primeProductNorm p R ≤ X*Real.exp M := by
    calc
      _ ≤ primeProductNorm p x.divisor * primeProductNorm p x.overlap * primeProductNorm p R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul he hv (normLogScale_pos _).le
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le)
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
      _ = primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap := by rw [hGR]; ring
      _ ≤ _ := hs.2
  unfold secondLogX
  apply (le_div_iff₀ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp R))).mpr
  calc
    _ ≤ Real.exp (-M) * (X*Real.exp M) := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = X := by rw [Real.exp_neg]; field_simp

end SecondPassArithmetic

end

end OAI

end


