-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0173_parallel1
-- name    : PNT_ZeroFree_433_0173_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:22:35.095333+00:00
-- url     : https://prove2.me/theorems/5e6ec207-790b-4a61-9eec-298eb84581df
-- title:
--   Zero-free region foundations: MeanSquare.DiagonalDensity [0173_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.DiagonalDensity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean#L138-L608

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0109
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0133_parallel1
import Definitions.Def_PNT_ZeroFree_433_0140_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0145_parallel2
import Definitions.Def_PNT_ZeroFree_433_0160_parallel1
import Definitions.Def_PNT_ZeroFree_433_0213_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/DiagonalDensity.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
namespace OAI

noncomputable section

namespace InitialMeanSquare

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

section

open scoped BigOperators Classical SchwartzMap ContDiff


section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def initialFrequencyCutoff (Z Y M T : ℝ) : Finset O :=
  secondFrequencyCutoff (Y/(1+Z*Real.exp M)^3) T

theorem initialFrequencyCutoff_zero (Z Y M T : ℝ) :
    (0:O)∈initialFrequencyCutoff Z Y M T := secondFrequencyCutoff_zero _ _

theorem initialFrequencyCutoff_valid
    {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (m c d : O) (g : 𝓢(ℝ,ℂ)) (M Z Y T : ℝ)
    (hZ : 0<Z) (hY : 0<Y) (hgM : ∀t,g t≠0 → |t|≤M)
    (G E S R : Finset ι) (hEG : E⊆G) (hSR : Disjoint S R)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U)) S R≠0)
    (k : O) (hk : k∉initialFrequencyCutoff Z Y M T) :
    T≤(Y/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2))*‖eisEmbedding k‖^2 := by
  let lengthScale : ℝ := 1+Z*Real.exp M
  have hL : 0<lengthScale := by dsimp [lengthScale]; positivity
  obtain ⟨hG,hE,hS,hR⟩ := residualPairWeight_support_bounds p hp hg Ψ m c d g M Z hZ hgM G E S R hEG hw
  have hZL : Z*Real.exp M≤lengthScale := by dsimp [lengthScale]; linarith
  have hn : ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2=primeProductNorm p S*primeProductNorm p R :=
    active_norm_sq_disjoint p S R hSR
  have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2≤lengthScale^3 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    have hSRn := mul_le_mul (hS.trans hZL) (hR.trans hZL)
      (FirstPassCubeLabels.primeProductNorm_pos p hp R).le hL.le
    have hESR := mul_le_mul (hE.trans hZL) hSRn
      (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
        (FirstPassCubeLabels.primeProductNorm_pos p hp R).le) hL.le
    nlinarith
  have hden0 : 0<‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    exact mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp E)
      (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) (FirstPassCubeLabels.primeProductNorm_pos p hp R))
  have hout := (outside_secondFrequencyCutoff (Y/lengthScale^3) T (by positivity) k hk).le
  exact hout.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hY.le hden0 hden) (sq_nonneg _))

theorem initial_tail_polynomial (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) (A : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y T : ℝ),0<Z → 0<Y → 0≤T →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (normalizedColumn p (fun V => g (columnLog p Z V))) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M T)‖≤
        C*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by
  obtain ⟨s,C,hC,h⟩ := full_uniform_secondSourceTail_bound A
  let P : ℝ := C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C₀ : ℝ := 128^4*(SchwartzMap.seminorm ℝ 0 0 g)^2*P
  have hP : 0≤P := by dsimp [P]; positivity
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y T hZ hY hT
  have hb := h p hp hg hinj hc F Ψ m c d
    (normalizedColumn p (fun V => g (columnLog p Z V))) W Y T hY hT
    (fun _ _ => initialFrequencyCutoff Z Y M T)
    (fun G hG E S hS R hR hSR hw k hk => initialFrequencyCutoff_valid p hp hg Ψ m c d g M Z Y T
      hZ hY hgM G E.val S R (Finset.mem_powerset.mp E.property) hSR hw k hk)
  have hpoly := secondSourceTailCost_polynomial p hp hg hinj F Ψ hΨ m c d g M Z Y T
    (1+Z*Real.exp M) P A hZ hY hT hP (by linarith [mul_pos hZ (Real.exp_pos M)]) (by linarith) hgM
  apply (hb.trans hpoly).trans
  calc
    _ = C₀*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

def initialTailHeight (Z Y M : ℝ) : ℝ :=
  (1+Z*Real.exp M)^2*(1+(1+Z*Real.exp M)^3/Y)

theorem initialTailHeight_pos (Z Y M : ℝ) (hZ : 0<Z) (hY : 0<Y) :
    0 < initialTailHeight Z Y M := by unfold initialTailHeight; positivity

theorem initial_tail_fixed_profile (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (fun S => star (normalizedColumn p (fun V => g (columnLog p Z V)) S)) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M (initialTailHeight Z Y M))‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_tail_polynomial (conjugateProfile g) W M
    (conjugateProfile_support_bound g M hgM) 2
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y hZ hY
  simp_rw [star_normalizedColumn]
  apply (h p hp hg hinj hc F Ψ hΨ m c d Z Y (initialTailHeight Z Y M) hZ hY
    (initialTailHeight_pos Z Y M hZ hY).le).trans
  have hth := initialTailHeight_pos Z Y M hZ hY
  apply (div_le_iff₀ (by positivity : 0<(1+initialTailHeight Z Y M)^2)).mpr
  have hh : (1+Z*Real.exp M)^4*(1+(1+Z*Real.exp M)^3/Y)^2≤(1+initialTailHeight Z Y M)^2 := by
    have hp := initialTailHeight_pos Z Y M hZ hY
    calc
      _ = (initialTailHeight Z Y M)^2 := by unfold initialTailHeight; ring
      _ ≤ _ := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hh (show 0≤C*Y by positivity)
  nlinarith

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

def initialErrorWindow (a b : ℝ) : ℝ := |Real.log a|+|Real.log b|+1

def initialErrorCutoff (a b Z Y : ℝ) : Finset O :=
  initialFrequencyCutoff Z Y (initialErrorWindow a b)
    (initialTailHeight Z Y (initialErrorWindow a b))

theorem initialErrorCutoff_zero (a b Z Y : ℝ) : (0:O)∈initialErrorCutoff a b Z Y :=
  initialFrequencyCutoff_zero _ _ _ _

def initialErrorFrequencyBound (a b Z Y : ℝ) : ℝ :=
  3*(initialTailHeight Z Y (initialErrorWindow a b)*
    (1+Z*Real.exp (initialErrorWindow a b))^3/Y+2)^2

theorem initialErrorCutoff_norm_bound (a b Z Y : ℝ) (hZ : 0<Z) (hY : 0<Y)
    (k : O) (hk : k∈initialErrorCutoff a b Z Y) :
    ‖eisEmbedding k‖^2≤ initialErrorFrequencyBound a b Z Y := by
  let M := initialErrorWindow a b
  let v : ℝ := initialTailHeight Z Y M/(Y/(1+Z*Real.exp M)^3)
  have hv : 0≤v := by
    dsimp [v]
    exact div_nonneg (initialTailHeight_pos Z Y M hZ hY).le (by positivity)
  have hb := secondFrequencyCutoff_norm_sq_le (Y/(1+Z*Real.exp M)^3)
    (initialTailHeight Z Y M) k hk
  have hc : (⌈v⌉₊:ℝ)+1≤v+2 := by
    have hh := (Nat.ceil_lt_add_one hv).le
    linarith
  apply hb.trans
  change 3*((⌈v⌉₊:ℝ)+1)^2≤_
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2) (by norm_num : (0:ℝ)≤3)
  convert! hsq using 1
  dsimp [initialErrorFrequencyBound,v,M]
  congr 2
  field_simp


end

open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)


end


open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels


open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem positive_nested_density_transfer (f G : Frequency → ℝ) (J : ℕ)
    (hG : Continuous G) (M : ℝ) (hGM : ∀ q, ‖G q‖ ≤ M)
    (C : ℝ) (hf : ∀ q, 0 ≤ f q)
    (hbound : ∀ q, f q ≤ C*tripleLogDensity J q*G q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,f (x,y,z)) ≤
      C*(∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,tripleLogDensity J (x,y,z)*G (x,y,z)) := by
  let u : Frequency → ℝ := fun q => C*(tripleLogDensity J q*G q)
  have hu : Integrable u := (tripleLogDensity_bounded_integrable J G hG M hGM).const_mul C
  have hux (x : ℝ) : Integrable (fun yz : ℝ × ℝ => u (x,yz)) :=
    (tripleLogDensity_slice_integrable J G hG M hGM x).const_mul C
  have huxy (x y : ℝ) : Integrable (fun z : ℝ => u (x,y,z)) := by
    have hd : Integrable (fun z : ℝ =>
        C*firstLogDensity J x*firstLogDensity J y*firstLogDensity J z) :=
      (firstLogDensity_integrable J).const_mul _
    have hgxy : Continuous (fun z : ℝ => G (x,y,z)) :=
      hG.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hi := hd.mul_bdd hgxy.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z : ℝ => hGM (x,y,z)))
    convert! hi using 1
    funext z
    dsimp [u,tripleLogDensity]
    ring
  have hz (x y : ℝ) : (∫ z : ℝ,f (x,y,z)) ≤ ∫ z : ℝ,u (x,y,z) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z : ℝ => hf (x,y,z))) (huxy x y)
    exact Filter.Eventually.of_forall (fun z : ℝ => by simpa only [u,mul_assoc] using hbound (x,y,z))
  have hy (x : ℝ) : (∫ y : ℝ,∫ z : ℝ,f (x,y,z)) ≤ ∫ y : ℝ,∫ z : ℝ,u (x,y,z) := by
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))
      (hux x).integral_prod_left (Filter.Eventually.of_forall (hz x))
  have hui : Integrable (fun x : ℝ => ∫ y : ℝ, ∫ z : ℝ,u (x,y,z)) := by
    apply hu.integral_prod_left.congr
    filter_upwards [] with x
    exact integral_prod _ (hux x)
  have hx := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => integral_nonneg
      (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))) hui
    (Filter.Eventually.of_forall hy)
  simpa only [u,integral_const_mul] using hx


end InitialMeanSquare

end

end OAI

end


