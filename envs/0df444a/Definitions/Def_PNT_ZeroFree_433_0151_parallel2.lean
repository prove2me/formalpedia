-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0151_parallel2
-- name    : PNT_ZeroFree_433_0151_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:19:13.043482+00:00
-- url     : https://prove2.me/theorems/7ff12944-7bfc-441b-9e77-f5399fd011f0
-- title:
--   Zero-free region foundations: Eisenstein.SmoothTests [0151_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Eisenstein.SmoothTests
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SmoothTests.lean#L307-L485

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0079
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0084
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0120_parallel1
import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0148_parallel1
import Definitions.Def_PNT_ZeroFree_433_0148_parallel2
import Definitions.Def_PNT_ZeroFree_433_0149_parallel1
import Definitions.Def_PNT_ZeroFree_433_0149_parallel2
import Definitions.Def_PNT_ZeroFree_433_0151_parallel1
import Definitions.Def_PNT_ZeroFree_433_0211_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1
import Definitions.Def_PNT_ZeroFree_433_0273_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Eisenstein/SmoothTests.lean
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
namespace InitialMeanSquare

section
open ActualEisensteinCubic SecondPassArithmetic
open SecondPassIntegration (elementNorm)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]


variable (hp : ∀i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem postCommonSmoothPair_fixed_mask (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (m r f y₁ y₂ : O)
    (x : SecondExpansionData ι) (hx : InSecondQuotientSector p r x)
    (A₁ A₂ W : 𝓢(ℝ,ℂ)) (V : Fin 7→ℝ→ℂ) (z ud ue uv kap X₁ X₂ R : ℝ) :
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*secondExpansionQuotient p x) f y₁ y₂
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R=
    postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r) f y₁ y₂
      A₁ A₂ W V z ud ue uv kap X₁ X₂ R := by
  have hm : Ideal.span {m*secondExpansionQuotient p x}=Ideal.span {m*r} := by
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      quotient_span_fixed p r x hx]
  simp only [postCommonSmoothPair,secondChildColumn,rowCoprimeMask_congr_span p _ hm]


end


end
section

open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open SecondPassIntegration (elementNorm)


theorem initial_sector_fixed_profiles
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU₁ : ∀t,g₁ t≠0→U t=1) (hU₂ : ∀t,g₂ t≠0→U t=1)
    (hg₁ : ∀t,g₁ t≠0→|t|≤A) (hg₂ : ∀t,g₂ t≠0→|t|≤A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7→ℝ→ℂ),
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      (∀i t,windows i t≠0→|t|≤A+2+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<E → 0<V → 0<X → 0<K →
        (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
          (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
          (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H =
        initialSourceSum p hp hcop hg s (sourceWeight p hp hcop hg Ψ m ray Z H)
          F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r) A₁ A₂ W windows
          (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K)
          X X (H*K/(E^2*V^2*X^2)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_source_fixed_profiles
    U hUc hUs g₁ g₂ W A 2 hA (by norm_num) hU₁ hU₂ hg₁ hg₂
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap
  calc
    _ = ∑x∈s,secondExpansionSource p hp hcop hg F Ψ m 1 1 ray {x}
        (fun S => normalizedColumn p (fun T => g₁ (columnLog p Z T)) S)
        (fun S => normalizedColumn p (fun T => g₂ (columnLog p Z T)) S) W H := by
          simp only [secondExpansionSource,Finset.sum_singleton]
    _ = _ := by
      unfold initialSourceSum
      apply Finset.sum_congr rfl
      intro x hx
      obtain ⟨hsubset,_⟩ := hs x hx
      have hh := hid p hp hcop hg hinj hpr F Ψ m ray x Z H E V X K
        hsubset (hk x hx) hZ hE hV hX hK (hz x hx) (he x hx) (hv x hx) (hkap x hx)
      rw [hh]
      rw [postCommonSmoothPair_fixed_mask p hp hcop hg F (secondRayMinus Ψ ray)
        (secondRayPlus Ψ ray) m r _ _ _ x (hs x hx)]
      rfl

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (normalizedColumn columnLog firstLogDensity)

theorem initial_sector_transfer
    (U : ℝ→ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0≤A)
    (hU : ∀t,g t≠0→U t=1) (hgA : ∀t,g t≠0→|t|≤A)
    (ε : ℝ) (hε : 0<ε) (N J : ℕ) :
    ∃ (windows : Fin 7→ℝ→ℂ) (C Cₛ : ℝ),0≤C ∧ 0≤Cₛ ∧
      (∀i,HasCompactSupport (windows i)) ∧ (∀i,ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀i,lambda∉Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
        (_hpr : ∀i,lambda^2∣p i-1)
        (F : Finset ι) (Ψ : O→*ℂ) (m r : O) (ray : SecondRayIndex)
        (s : Finset (SecondExpansionData ι)) (Z H E V X K : ℝ),
        0<Z → 0<H → 0<E → 0<V → 0<X → 0<K →
        (∀a,‖Ψ a‖≤1) → (∀x∈s,InSecondQuotientSector p r x) → (∀x∈s,x.frequency≠0) →
        (∀x∈s,|sourceLogZ p Z X x|≤2) → (∀x∈s,|sourceLogE p E x|≤2) →
        (∀x∈s,|sourceLogV p V x|≤2) → (∀x∈s,|sourceLogK p K x|≤2) →
        ∃ B : Frequency→ℝ,
          (∀q,0≤B q) ∧
          (∀q,(1+H*K/(E^2*V^2*X^2))^N*B q≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S)
            (fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S) W H‖≤
          (C*H*elementNorm r/Z^2*‖secondRayCoefficient ray‖*(K*Real.exp 2)^ε)*
            (∫t₁:ℝ,∫t₂:ℝ,∫t₃:ℝ,B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := initial_sector_fixed_profiles
    U hUc hUs g g W A hA hU hU hgA hgA
  obtain ⟨Cw,hCw,hwbound⟩ := outerWindow_global_bound windows hwc (fun i => (hws i).continuous)
  have hM : 0≤A+2+1 := by linarith
  obtain ⟨Cₐ,hCₐ,Cₛ,hCₛ,htrans⟩ := initial_source_uniform_transfer ε hε A₁ A₂ W windows
    (fun _ => A+2+1) (fun _ => hM) hwb N J
  refine ⟨windows,Cw*Cₐ,Cₛ,mul_nonneg hCw hCₐ.le,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m r ray s Z H E V X K hZ hH hE hV hX hK hΨ hs hk hz he hv hkap
  let R := H*K/(E^2*V^2*X^2)
  have hR : 0<R := by dsimp [R]; positivity
  obtain ⟨b,hpoint,hbound⟩ := htrans R hR
  let B : Frequency→ℝ := fun q => ‖tripleCoefficient (𝓕 A₁) (𝓕 A₂) b q‖
  refine ⟨B,fun q => norm_nonneg _,?_,?_⟩
  · intro q
    simpa only [B,R,tripleCoefficient,mul_assoc] using hpoint q.1 q.2.1 q.2.2
  · let T := s.image (sourceObservation p)
    have hT0 : ∀y∈T,y.1≠0 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact sourceRow_nonzero p x (hk x hx)
    have hTK : ∀y∈T,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K*Real.exp 2 := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hpos := elementNorm_pos _ (sourceRow_nonzero p x (hk x hx))
      have hl : Real.log (elementNorm (sourceObservation p x).1/K)≤2 :=
        (le_abs_self _).trans (hkap x hx)
      have hh := Real.exp_le_exp.mpr hl
      rw [Real.exp_log (div_pos hpos hK)] at hh
      have hh' := (div_le_iff₀ hK).mp hh
      simpa only [elementNorm,eisEmbedding_norm_sq_eq_absNorm_span,mul_comm] using hh'
    let D := H*elementNorm r/Z^2*‖secondRayCoefficient ray‖
    have hD : 0≤D := by dsimp [D,elementNorm]; positivity
    have hweights : ∀x∈s,‖sourceWeight p hp hcop hg Ψ m ray Z H x‖*
        ‖outerWindow windows (sourceLogZ p Z X x) 0 (sourceLogE p E x) (sourceLogV p V x) (sourceLogK p K x)‖≤D*Cw := by
      intro x hx
      exact mul_le_mul (sourceWeight_norm_fixed p hp hcop hg hinj hc Ψ m r ray Z H x
        (hs x hx) hZ hH.le (hΨ _) (hΨ _)) (hwbound _ _ _ _ _) (norm_nonneg _) hD
    have hh := hbound p hp hcop hg hinj r s T (sourceWeight p hp hcop hg Ψ m ray Z H) (D*Cw)
      (K*Real.exp 2) F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (m*r)
      (sourceLogZ p Z X) (fun _ => 0) (sourceLogE p E) (sourceLogV p V) (sourceLogK p K) X X
      (mul_nonneg hD hCw) (by positivity) hs (fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩) hT0 hTK hweights
    rw [hid p hp hcop hg hinj hpr F Ψ m r ray s Z H E V X K hZ hE hV hX hK hs hk hz he hv hkap]
    convert! hh using 1 ; dsimp [D,B,R,T] ; ring

end InitialMeanSquare


end

end OAI

end


