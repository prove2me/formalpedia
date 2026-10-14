-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0178_parallel1
-- name    : PNT_ZeroFree_433_0178_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:27:52.546257+00:00
-- url     : https://prove2.me/theorems/ea1bf2f5-f85a-4771-a503-cff19ab9c5c9
-- title:
--   Zero-free region foundations: MeanSquare.CanonicalDensity [0178_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.CanonicalDensity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/CanonicalDensity.lean#L80-L606

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0130
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0142_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel2
import Definitions.Def_PNT_ZeroFree_433_0158_parallel2_1
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0174_parallel1
import Definitions.Def_PNT_ZeroFree_433_0223_parallel1
import Definitions.Def_PNT_ZeroFree_433_0244_parallel2
import Definitions.Def_PNT_ZeroFree_433_0246_parallel1
import Definitions.Def_PNT_ZeroFree_433_0249_parallel1
import Definitions.Def_PNT_ZeroFree_433_0255_parallel1
import Definitions.Def_PNT_ZeroFree_433_0259_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel2
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/CanonicalDensity.lean
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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve

theorem outsideIdealsUpTo_mono (S : Finset (Ideal O)) {D E : ℕ} (hDE : D ≤ E) :
    outsideIdealsUpTo S D ⊆ outsideIdealsUpTo S E := by
  intro I hI
  obtain ⟨hpos,hn,hS⟩ := mem_outsideIdealsUpTo.mp hI
  exact mem_outsideIdealsUpTo.mpr ⟨hpos,hn.trans hDE,hS⟩


end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def canonicalCubeDualFinite (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑h∈(T D).erase 0,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

def canonicalCubeDualTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val


end

section

open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})


def canonicalSourceTotal (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc


end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)


end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (firstLogDensity)

theorem initial_subunit_row_le_label (Z X lengthScale K R κ : ℝ)
    (hZ : 1 ≤ Z) (hX : X ≤ 1) (hL : 0 ≤ lengthScale) (hK : 0 ≤ K)
    (hR : 1 ≤ R) (hκ : 0 ≤ κ) (hinv : K*R ≤ X*lengthScale*Z^(-κ)) : K ≤ lengthScale := by
  have hpow : Z^(-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
  have hpow0 : 0 ≤ Z^(-κ) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  calc
    K ≤ K*R := le_mul_of_one_le_right hK hR
    _ ≤ X*lengthScale*Z^(-κ) := hinv
    _ ≤ 1*lengthScale*Z^(-κ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hL) hpow0
    _ ≤ lengthScale := by simpa only [one_mul,mul_one] using mul_le_mul_of_nonneg_left hpow hL

theorem initial_subunit_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hKL : K ≤ lengthScale) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      (initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3)*(X*lengthScale)^2 := by
  let C := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hd := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X lengthScale K A Vmax J hX hL hK hA hVmax hV₁ hV₂ hs₁ hs₂ hT
  change _/(X*lengthScale) ≤ C*K*X at hd
  have hraw := (div_le_iff₀ (mul_pos hX (zero_lt_one.trans_le hL))).mp hd
  calc
    _ ≤ (C*K*X)*(X*lengthScale) := hraw
    _ ≤ (C*lengthScale*X)*(X*lengthScale) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKL hC) hX.le)
      (mul_nonneg hX.le (zero_le_one.trans hL))
    _ = _ := by dsimp only [C]; ring

lemma initialErrorFrequencyBound_ge_one (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H) :
    1 ≤ initialErrorFrequencyBound a b Z H := by
  have ht := initialTailHeight_pos Z H (initialErrorWindow a b) hZ hH
  have hv : 0 ≤ initialTailHeight Z H (initialErrorWindow a b)*
      (1+Z*Real.exp (initialErrorWindow a b))^3/H := by positivity
  unfold initialErrorFrequencyBound
  nlinarith [sq_nonneg (initialTailHeight Z H (initialErrorWindow a b)*
      (1+Z*Real.exp (initialErrorWindow a b))^3/H)]


end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)


def initialExcludedNorm (S : Finset (Ideal ActualEisensteinCubic.O)) : ℝ :=
  max 1 (∏ P ∈ S,(Ideal.absNorm P : ℝ))

lemma initialExcludedNorm_ge_one (S : Finset (Ideal ActualEisensteinCubic.O)) : 1 ≤ initialExcludedNorm S :=
  le_max_left _ _


end InitialMeanSquare

end

end OAI

end


