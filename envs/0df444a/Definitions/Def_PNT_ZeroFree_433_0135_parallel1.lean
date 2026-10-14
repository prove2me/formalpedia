-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0135_parallel1
-- name    : PNT_ZeroFree_433_0135_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:38:15.761971+00:00
-- url     : https://prove2.me/theorems/29770d1e-fdfa-414a-a31e-d87b9b2d8655
-- title:
--   Zero-free region foundations: GaussSum.GlobalScales [0135_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.GaussSum.GlobalScales
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/GlobalScales.lean#L92-L739

import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0006
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0014
import Definitions.Def_PNT_ZeroFree_433_0015
import Definitions.Def_PNT_ZeroFree_433_0024
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0056_1
import Definitions.Def_PNT_ZeroFree_433_0063
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0066
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0073
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0078
import Definitions.Def_PNT_ZeroFree_433_0080
import Definitions.Def_PNT_ZeroFree_433_0081
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0096
import Definitions.Def_PNT_ZeroFree_433_0101
import Definitions.Def_PNT_ZeroFree_433_0102
import Definitions.Def_PNT_ZeroFree_433_0116
import Definitions.Def_PNT_ZeroFree_433_0117
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0123_parallel2
import Definitions.Def_PNT_ZeroFree_433_0125_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126_parallel2
import Definitions.Def_PNT_ZeroFree_433_0245_parallel1
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/GaussSum/GlobalScales.lean
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


open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def globalRowScaleFloor (K ell B F M : ℝ) : ℝ :=
  ell^2*B^2*F^2/(K*(ell*Real.exp M)^2)

theorem globalRowScaleFloor_pos (K ell B F M : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) : 0 < globalRowScaleFloor K ell B F M := by
  unfold globalRowScaleFloor
  positivity


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]


end


open MeasureTheory
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)


end SecondPassArithmetic

section

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog primeProductNorm)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem fixedSecondTest_subunit (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative : Bool) (S : Finset ι) : fixedSecondTest p V X a b negative S=0 := by
  have hz : V (columnLog p X S)=0 := by
    by_contra hn
    have hh := columnLog_norm_upper p hp X A hX S ((le_abs_self _).trans (hV _ hn))
    have h1 := primeProductNorm_ge_one p hp S
    linarith
  cases negative <;> simp [fixedSecondTest,JointLogSeparation.fixedColumnTest,hz]

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem childEnergy_subunit (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X A : ℝ) (hX : 0 < X)
    (hV : ∀ s,V s ≠ 0 → |s| ≤ A) (hsmall : X*Real.exp A < 1)
    (a b : ℝ) (negative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X negative rowNegative a b=0 := by
  have hrow (f y : O) : fixedChildRow p hp hcop hg pool Ψ m (fixedSecondTest p V X a b negative) f y=0 := by
    unfold fixedChildRow
    apply Finset.sum_eq_zero
    intro S hS
    simp only [secondChildColumn,fixedSecondTest_subunit p hp V X A hX hV hsmall a b negative S,mul_zero]
  simp [childEnergy,idealChildRow,hrow]

theorem densityChildEnergy_subunit (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ A : ℝ) (J : ℕ) (hX : 0 < X₁)
    (hV : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hsmall : X₁*Real.exp A < 1) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J=0 := by
  unfold densityChildEnergy childGeometricMean
  simp only [childEnergy_subunit p hp hcop hg pool Ψ₁ m T V₁ X₁ A hX hV hsmall,
    Real.sqrt_zero,zero_mul,mul_zero,integral_zero]

theorem childDensity_elementary_all_scales
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3)*K*X := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · exact childDensity_elementary_supported p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂ m T V₁ V₂
      X F K A M J hX hF hK hA hM hscale hV₁ hV₂ hVs₁ hVs₂ hT
  · rw [densityChildEnergy_subunit p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X A (2*J) hX hVs₁ (lt_of_not_ge hscale),zero_div]
    have hI : 0 ≤ ∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t :=
      integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
    positivity

end SecondPassIntegration
end

namespace SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassIntegration (densityChildEnergy)

def globalTerminalConstant (A M : ℝ) : ℝ :=
  6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3

def globalRayTripleConstant : ℝ := 128^3*(Real.exp 1)^18*(512*32^2)

theorem globalTerminalConstant_nonneg (A M : ℝ) : 0 ≤ globalTerminalConstant A M := by
  have hI : 0 ≤ ∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  unfold globalTerminalConstant
  positivity

theorem radial_decay_step (R : ℝ) (hR : 0 ≤ R) (N : ℕ) :
    R/(1+R)^(N+1) ≤ 1/(1+R)^N := by
  have h1 : 0 < 1+R := by linarith
  have hr : R/(1+R) ≤ 1 := (div_le_iff₀ h1).mpr (by linarith)
  calc
    R/(1+R)^(N+1) = (R/(1+R))/(1+R)^N := by rw [pow_succ];field_simp
    _ ≤ _ := div_le_div_of_nonneg_right hr (pow_nonneg h1.le _)


end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum CompletedGauss
open QuadraticSquarefreeKernel

def liftingPrimeElement : O := ActualEisensteinCoordinates.eval 1 3
def liftingPrime : Ideal O := Ideal.span {liftingPrimeElement}

theorem liftingPrimeElement_norm : ShortDraftLatticeCount.qNat liftingPrimeElement=7 := by
  unfold ShortDraftLatticeCount.qNat liftingPrimeElement
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q] <;> decide

theorem liftingPrime_norm : Ideal.absNorm liftingPrime=7 := by
  rw [liftingPrime,←qNat_eq_absNorm_span,liftingPrimeElement_norm]

theorem liftingPrime_prime : Prime liftingPrime := by
  apply Ideal.prime_of_isPrime
  · intro h
    have hh := Ideal.absNorm_eq_zero_iff.mpr h
    rw [liftingPrime_norm] at hh
    norm_num at hh
  · exact Ideal.isPrime_of_irreducible_absNorm (by
      rw [liftingPrime_norm,Nat.irreducible_iff_nat_prime]
      exact (by decide : Nat.Prime 7))

theorem liftingPrime_supported : Supported liftingPrime := by
  apply (supported_span_iff liftingPrimeElement).mpr
  have hlam : ShortDraftLatticeCount.qNat lambda=3 := by
    have he : lambda=ActualEisensteinCoordinates.eval (-1) 1 := theta_counter_lambda_eq
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q] <;> decide
  have htwo : ShortDraftLatticeCount.qNat (2:O)=4 := by
    have he : (2:O)=ActualEisensteinCoordinates.eval 2 0 := by simp [ActualEisensteinCoordinates.eval]
    rw [he]
    unfold ShortDraftLatticeCount.qNat
    rw [ShortDraftLatticeCount.coords_eval]
    norm_num [ShortDraftLatticeCount.q] <;> decide
  constructor
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,hlam] at h
    omega
  · rintro ⟨z,hz⟩
    have h := congrArg ShortDraftLatticeCount.qNat hz
    rw [liftingPrimeElement_norm,ShortDraftLatticeCount.qNat_mul,htwo] at h
    omega

theorem liftingPrime_admissible : Admissible liftingPrime :=
  ⟨liftingPrime_prime.ne_zero,liftingPrime_prime.squarefree,liftingPrime_supported.2⟩

theorem supported_pow {I : Ideal O} (hI : Supported I) (k : ℕ) : Supported (I^k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    change P∈UniqueFactorizationMonoid.normalizedFactors (1:Ideal O) at hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | succ k hk =>
    rw [pow_succ]
    exact (supported_mul_iff _ _).mpr ⟨hk,hI⟩

theorem exists_lifting_exponent (M : ℝ) (I : Ideal O) (hI : I≠0)
    (hIM : (Ideal.absNorm I:ℝ)≤M) :
    ∃k : ℕ, M<(49:ℝ)^k*(Ideal.absNorm I:ℝ) ∧
      (49:ℝ)^k*(Ideal.absNorm I:ℝ)≤49*M := by
  have hN : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((le_div_iff₀ hN).mpr (by simpa using hIM))
    (by norm_num : (1:ℝ)<49)
  refine ⟨k+1,?_,?_⟩
  · exact (div_lt_iff₀ hN).mp hhi
  · have h := (le_div_iff₀ hN).mp hlo
    rw [pow_succ]
    nlinarith

def liftingExponent (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : ℕ :=
  (exists_lifting_exponent M I hI hIM).choose

def liftedRow (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) : Ideal O :=
  (liftingPrime^liftingExponent M I hI hIM)^2*I

theorem liftedRow_norm (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    (Ideal.absNorm (liftedRow M I hI hIM):ℝ)=(49:ℝ)^liftingExponent M I hI hIM*(Ideal.absNorm I:ℝ) := by
  simp only [liftedRow,map_mul,map_pow,liftingPrime_norm,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [←pow_mul, Nat.mul_comm, pow_mul]
  norm_num

theorem liftedRow_bounds (M : ℝ) (I : Ideal O) (hI : I≠0) (hIM : (Ideal.absNorm I:ℝ)≤M) :
    M<(Ideal.absNorm (liftedRow M I hI hIM):ℝ) ∧
      (Ideal.absNorm (liftedRow M I hI hIM):ℝ)≤49*M := by
  rw [liftedRow_norm]
  exact (exists_lifting_exponent M I hI hIM).choose_spec

theorem liftedRow_squarefreePart (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : squarefreePart (liftedRow M I hI.1 hIM)=I :=
  (squarePart_mul_squarefree (pow_ne_zero _ liftingPrime_prime.ne_zero) hI.2.1).2

theorem liftedRow_supported (M : ℝ) (I : Ideal O) (hI : Admissible I)
    (hIM : (Ideal.absNorm I:ℝ)≤M) : Supported (liftedRow M I hI.1 hIM) := by
  exact (supported_mul_iff _ _).mpr
    ⟨supported_pow (supported_pow liftingPrime_supported _) _,admissible_supported hI⟩


theorem liftedRow_injective (M : ℝ) :
    Function.Injective (fun I : idealRange M =>
      liftedRow M I.val (mem_idealRange.mp I.property).1.1 (mem_idealRange.mp I.property).2) := by
  intro I J h
  apply Subtype.ext
  have he := congrArg squarefreePart h
  simpa only [liftedRow_squarefreePart M I.val (mem_idealRange.mp I.property).1,
    liftedRow_squarefreePart M J.val (mem_idealRange.mp J.property).1] using he

end CanonicalQuadraticSieve

end

end OAI

end


