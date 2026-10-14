-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0129_parallel2
-- name    : PNT_ZeroFree_433_0129_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:05:38.235985+00:00
-- url     : https://prove2.me/theorems/758b9632-56cf-4c7d-995e-2dc4ef8e7860
-- title:
--   Zero-free region foundations: QuadraticSieve.PoissonComparison [0129_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean#L156-L590

import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0060
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0071
import Definitions.Def_PNT_ZeroFree_433_0082
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0093
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0099
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0106
import Definitions.Def_PNT_ZeroFree_433_0107
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0121_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0125_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0128_parallel2
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0152_parallel1
import Definitions.Def_PNT_ZeroFree_433_0153_parallel2
import Definitions.Def_PNT_ZeroFree_433_0210
import Definitions.Def_PNT_ZeroFree_433_0235_parallel1
import Definitions.Def_PNT_ZeroFree_433_0271_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean
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

namespace CanonicalQuadraticSieve

section


section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson


def centeredRetainedDual {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) (q : Ideal O) : ℂ :=
  (6:ℂ)*retainedDualPrincipalSum (quadraticTransformedSquareProfile W)
    (fun I : squarefreeIdealRange K => I.val) cols (divisorTwist cols a q) M (Ideal.absNorm q:ℝ) -
  paperRadialFourier (quadraticTransformedSquareProfile W) 0 *
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (divisorTwist cols a q) (divisorTwist cols a q) (M/(Ideal.absNorm q:ℝ))


def maskedPoissonDifference {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedDualFamily G cols a W M - (6:ℂ)⁻¹ *
    maskedPrincipalSourceSum G (quadraticSquareProfile W)
      (fun I : coprimeSquarefreeRange G K => I.val) cols a M


open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator


theorem retainedDualMajorant_coefficient_scale_le {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a a' : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0<N) (hM : 0≤M) (hF : 1≤F) (hT : 0≤T)
    (ha : ∀j, ‖a' j‖≤‖a j‖) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a' W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M 1 T a W := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' a a' ha ha
  have he0 := divisorEnergyFactor_nonneg ε hε N a' a'
  have he1 := divisorEnergyFactor_nonneg ε hε N a a
  have hea : (∑j, ‖a' j‖^2)≤∑j, ‖a j‖^2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) 2)
  have hs := (supportConstant_pos ε hε).le
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have hF0 : 0<F := by linarith
  have hMF : M/F≤M := div_le_self hM hF
  have hNF : N≤F*N := by nlinarith
  have hMN : 2*M/(F*N)≤2*M/N :=
    div_le_div_of_nonneg_left (by positivity) hN hNF
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  simp only [div_one,one_mul]
  gcongr

theorem centeredRetainedDual_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        (∑q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) ≤
          (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
            retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_global l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT cols hc hcols hray a W
  classical
  have hqbound (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖centeredRetainedDual W cols a M K q‖ ≤
        (columnDyadicLength K+1:ℕ)*
          retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) := by
    have hqd := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqd; exact hG hqd
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hh := hbound hexp hα deltaLoss hδ ε hε K N M (Ideal.absNorm q:ℝ) T hK hN hM
      (by linarith) hT cols hc hcols hray (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact retainedDualMajorant_coefficient_scale_le s C hC.le l hexp deltaLoss hδ ε hε
      (2*K) N M (Ideal.absNorm q:ℝ) T a (divisorTwist cols a q) (quadraticTransformedSquareProfile W)
      (by linarith) (by linarith) hM.le hq1 (by linarith) (divisorTwist_norm_le cols a q)
  calc
    _ ≤ ∑_q∈idealDivisors G, (columnDyadicLength K+1:ℕ)*
        retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) :=
      Finset.sum_le_sum hqbound
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator

def poissonComparisonMajorant {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  (idealDivisors G).card*(columnDyadicLength K+1:ℕ)*
    retainedDualMajorant sD CD l hexp deltaLoss hδ ε hε (2*K) N M 1 T a (quadraticTransformedSquareProfile W) +
  6*(256*M*(idealDivisors G).card*
    ((CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
      ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
        (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A))*∑j, ‖a j‖^2) +
  (columnDyadicLength K+1:ℕ)*
    sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a (quadraticSquareProfile W) +
  ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
    (((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
      (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2)


end


open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy


theorem poissonComparisonMajorant_energy_factor {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W =
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
        (fun _ : Unit => (1:ℂ)) W * ∑j, ‖a j‖^2 := by
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,mul_one]
  ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondOuterWeight (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let b0 := b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    (secondNormalizedExpansionWeight p hp hcop hg Ψ (m*b0) c d z X Y x.source *
      (secondExpansionScale p X r (expansionSupportData x.common x.firstDivisor x.source) : ℂ)⁻¹)

theorem globalSecondOuterWeight_squarefree
    (Ψ : O →* ℂ) (m : O) (z : SecondRayIndex) (ell Y : ℝ) (side : Bool)
    (x : GlobalSecondData ι) (hx : GlobalSecondAdmissible x)
    (h : globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x ≠ 0) :
    Squarefree (SecondPassFiber.newLabel (globalSecondTuple p x)) := by
  apply actualSecondLabel_squarefree_of_weight p hp hcop hg x.cube.support x.common
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit hx.2.2.1 Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor) z x.source hx.2.1
  intro hw
  unfold secondArithmeticWeight at hw
  rcases mul_eq_zero.mp hw with hA|hB
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hA,mul_zero,zero_mul]
  · apply h
    simp only [globalSecondOuterWeight,secondNormalizedExpansionWeight,secondBaseLabel,hB,mul_zero,zero_mul]

theorem globalSecondOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      (Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
        (globalFirstColumnScale p ell x side)^2)*‖secondRayCoefficient z‖ := by
  have ht := FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon
  have hX := globalFirstColumnScale_pos p hp ell hell x side
  have hh := secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc x.common x.firstDivisor
    Ψ (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
    (secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
    z (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) Y (div_pos hX ht) hY x.source (hΨ _) (hΨ _)
  rw [primeSubsetGenerator_norm_eq_productNorm] at hh
  unfold globalSecondOuterWeight
  dsimp only
  rw [norm_mul,norm_inv,Complex.norm_of_nonneg ht.le]
  apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ht.le)).trans_eq
  field_simp

def globalPooledOuterBound (z : SecondRayIndex) (ell Y : ℝ) (j : GlobalLogIndex) : ℝ :=
  (Y*(Real.exp 1)^6*globalLogRep j 2*globalLogRep j 3*(globalLogRep j 0)^2*(globalLogRep j 1)^2/ell^2)*
    ‖secondRayCoefficient z‖

theorem globalSecondOuterWeight_bin_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (z : SecondRayIndex)
    (ell Y : ℝ) (hell : 0 < ell) (hY : 0 ≤ Y) (side : Bool) (x : GlobalSecondData ι)
    (hk : x.source.frequency ≠ 0) :
    ‖globalSecondOuterWeight p hp hcop hg Ψ m z ell Y side x‖ ≤
      globalPooledOuterBound z ell Y (globalScaleIndex p side x) := by
  apply (globalSecondOuterWeight_norm_le p hp hcop hg hinj hc Ψ hΨ m z ell Y hell hY side x).trans
  let j := globalScaleIndex p side x
  have ha := (globalScaleIndex_bounds p hp side x hk 0).2
  have hc' := (globalScaleIndex_bounds p hp side x hk 1).2
  have ht := (globalScaleIndex_bounds p hp side x hk 2).2
  have hr := (globalScaleIndex_bounds p hp side x hk 3).2
  change primeProductNorm p (x.cube.sideDivisor side) ≤ globalLogRep j 0*Real.exp 1 at ha
  change primeProductNorm p x.common ≤ globalLogRep j 1*Real.exp 1 at hc'
  change primeProductNorm p x.firstCommon ≤ globalLogRep j 2*Real.exp 1 at ht
  change primeProductNorm p (x.source.sourceCommon\x.source.divisor) ≤ globalLogRep j 3*Real.exp 1 at hr
  have hn : Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)/
      (globalFirstColumnScale p ell x side)^2 =
      Y*primeProductNorm p x.firstCommon*primeProductNorm p (x.source.sourceCommon\x.source.divisor)*
        (primeProductNorm p (x.cube.sideDivisor side))^2*(primeProductNorm p x.common)^2/ell^2 := by
    have hA := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).ne'
    have hC := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).ne'
    unfold globalFirstColumnScale
    field_simp

  rw [hn]
  have h0 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.cube.sideDivisor side)).le
  have h1 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.common).le
  have h2 := (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon).le
  have h3 := (FirstPassCubeLabels.primeProductNorm_pos p hp (x.source.sourceCommon\x.source.divisor)).le
  have hr0 := (globalLogRep_pos j 0).le
  have hr1 := (globalLogRep_pos j 1).le
  have hr2 := (globalLogRep_pos j 2).le
  have hr3 := (globalLogRep_pos j 3).le
  calc
    _ ≤ (Y*(globalLogRep j 2*Real.exp 1)*(globalLogRep j 3*Real.exp 1)*
      (globalLogRep j 0*Real.exp 1)^2*(globalLogRep j 1*Real.exp 1)^2/ell^2)*‖secondRayCoefficient z‖ := by gcongr
    _ = _ := by unfold globalPooledOuterBound;ring

end SecondPassArithmetic

end

end OAI

end


