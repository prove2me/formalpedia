-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0128_parallel1
-- name    : PNT_ZeroFree_433_0128_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:41:18.270803+00:00
-- url     : https://prove2.me/theorems/56ab9e92-9753-433c-b97e-d2eef5e3dee6
-- title:
--   Zero-free region foundations: CubicSieve.ScaleCaps [0128_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.ScaleCaps
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ScaleCaps.lean#L83-L752

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0054
import Definitions.Def_PNT_ZeroFree_433_0054_1
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0070
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0087
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0110
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0115
import Definitions.Def_PNT_ZeroFree_433_0119_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel1
import Definitions.Def_PNT_ZeroFree_433_0168_parallel1
import Definitions.Def_PNT_ZeroFree_433_0195_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1_1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/ScaleCaps.lean
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
open FirstPassCubeLabels (primeProduct bit parity retained b0Exponent aLabel jLabel j2Label squarefreeLabel b0Label)

variable {ι : Type*} [DecidableEq ι]

def finiteBlockExponent (B : Finset ι) (v : ι → ℕ) : ι →₀ ℕ :=
  Finsupp.onFinset B (fun i => if i∈B then v i else 0) (by
    intro i hi
    by_contra hn
    exact hi (if_neg hn))

def cubeCoordinatesOfBlock (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : CubeCoordinates ι where
  leftExponent := finiteBlockExponent B v₁
  rightExponent := finiteBlockExponent B v₂
  leftDivisor := B.filter (fun i => ε₁ i)
  rightDivisor := B.filter (fun i => ε₂ i)

theorem cubeCoordinatesOfBlock_support (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈B,0 < v₁ i+v₂ i) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).support=B := by
  ext i
  simp only [CubeCoordinates.support,cubeCoordinatesOfBlock,Finset.mem_union,
    Finsupp.mem_support_iff,finiteBlockExponent,Finsupp.onFinset_apply]
  by_cases hi : i∈B
  · simp only [hi,ite_true,iff_true]
    have h := hv i hi
    omega
  · simp [hi]

theorem cubeCoordinatesOfBlock_leftBit (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (i : ι) (hi : i∈B) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).leftBit i=ε₁ i := by
  cases h : ε₁ i <;> simp [CubeCoordinates.leftBit,cubeCoordinatesOfBlock,hi,h]

theorem cubeCoordinatesOfBlock_rightBit (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (i : ι) (hi : i∈B) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).rightBit i=ε₂ i := by
  cases h : ε₂ i <;> simp [CubeCoordinates.rightBit,cubeCoordinatesOfBlock,hi,h]

theorem cubeCoordinatesOfBlock_admissible (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈B,0 < v₁ i+v₂ i) : (cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂).Admissible := by
  unfold CubeCoordinates.Admissible
  rw [cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv]
  exact ⟨Finset.filter_subset _ _,Finset.filter_subset _ _⟩

theorem cubeCoordinatesOfBlock_primeProduct (p : ι → O)
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i)
    (f : ℕ → ℕ → Bool → Bool → ℕ) :
    let x := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
    primeProduct p x.support (fun i => f (x.leftExponent i) (x.rightExponent i) (x.leftBit i) (x.rightBit i)) =
      primeProduct p B (fun i => f (v₁ i) (v₂ i) (ε₁ i) (ε₂ i)) := by
  dsimp only
  rw [cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv]
  unfold primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only
  rw [cubeCoordinatesOfBlock_leftBit B v₁ v₂ ε₁ ε₂ i hi,
    cubeCoordinatesOfBlock_rightBit B v₁ v₂ ε₁ ε₂ i hi]
  simp only [cubeCoordinatesOfBlock,finiteBlockExponent,Finsupp.onFinset_apply,if_pos hi]

def globalSecondOfBlock (B A₀ C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (x : SecondExpansionData ι) : GlobalSecondData ι where
  cube := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  firstCommon := A₀
  common := C
  firstDivisor := D
  source := x

theorem globalSecondOfBlock_injective (B A₀ C D : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Function.Injective (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂) := by
  intro x y h
  exact congrArg GlobalSecondData.source h

theorem globalSecondOfBlock_admissible (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i)
    (hCB : Disjoint C B) (hD : D⊆C∪B) (x : SecondExpansionData ι) (hE : x.divisor⊆x.sourceCommon) :
    GlobalSecondAdmissible (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) := by
  refine ⟨cubeCoordinatesOfBlock_admissible B v₁ v₂ ε₁ ε₂ hv,hE,?_,?_⟩
  · simpa only [globalSecondOfBlock,cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv] using hCB
  · simpa only [globalSecondOfBlock,cubeCoordinatesOfBlock_support B v₁ v₂ ε₁ ε₂ hv] using hD

variable (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_tuple (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondTuple p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
      actualSecondTuple p B C D x.divisor x.overlap v₁ v₂ ε₁ ε₂ x.frequency := by
  have hpoly := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
  have hspan (f : ℕ → ℕ → Bool → Bool → ℕ) := congrArg (fun a : O => (Ideal.span {a} : Ideal O)) (hpoly f)
  let c := cubeCoordinatesOfBlock B v₁ v₂ ε₁ ε₂
  have hJ : jLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (retained (parity (a+b)) e₁ e₂))
  have hS : squarefreeLabel p c.support (fun i => c.leftExponent i+c.rightExponent i) =
      squarefreeLabel p B (fun i => v₁ i+v₂ i) := hpoly (fun a b _ _ => bit (parity (a+b)))
  have hP₁ : primeProduct p c.support c.leftExponent = primeProduct p B v₁ := hpoly (fun a _ _ _ => a)
  have hP₂ : primeProduct p c.support c.rightExponent = primeProduct p B v₂ := hpoly (fun _ b _ _ => b)
  have hA₁ : aLabel p c.support c.leftBit = aLabel p B ε₁ := hpoly (fun _ _ e₁ _ => bit e₁)
  have hA₂ : aLabel p c.support c.rightBit = aLabel p B ε₂ := hpoly (fun _ _ _ e₂ => bit e₂)
  have hJ₂ : j2Label p c.support (fun i => c.leftExponent i+c.rightExponent i) c.leftBit c.rightBit =
      j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ := hpoly (fun a b e₁ e₂ => bit (FirstPassCubeLabels.evenDouble (a+b) e₁ e₂))
  change actualSecondTuple p c.support C D x.divisor x.overlap c.leftExponent c.rightExponent c.leftBit c.rightBit x.frequency = _
  unfold actualSecondTuple
  rw [hJ,hS,hP₁,hA₁,hA₂,hJ₂,hP₂]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalSecondOfBlock_triple (B A₀ C D : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i∈B,0 < v₁ i+v₂ i) (x : SecondExpansionData ι) :
    globalSecondFixedTriple p (globalSecondOfBlock B A₀ C D v₁ v₂ ε₁ ε₂ x) =
    (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂},
      ∏ i∈A₀,Ideal.span {p i},∏ i∈x.sourceCommon\x.divisor,Ideal.span {p i}) := by
  have h := cubeCoordinatesOfBlock_primeProduct p B v₁ v₂ ε₁ ε₂ hv
    (fun a b e₁ e₂ => b0Exponent (a+b) e₁ e₂)
  apply Prod.ext
  · exact congrArg (fun a : O => (Ideal.span {a} : Ideal O)) h
  · rfl


end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

abbrev GlobalLogIndex := Fin 10 → ℕ

def globalLogRep (j : GlobalLogIndex) (i : Fin 10) : ℝ := normLogScale (j i)

theorem globalLogRep_pos (j : GlobalLogIndex) (i : Fin 10) : 0 < globalLogRep j i := normLogScale_pos _

theorem globalLogRep_ge_one (j : GlobalLogIndex) (i : Fin 10) : 1 ≤ globalLogRep j i := normLogScale_ge_one _


def globalLogBox (U : Fin 10 → ℝ) : Finset GlobalLogIndex :=
  Fintype.piFinset (fun i => Finset.range (normLogBin (U i)+1))

theorem globalLogBox_card (U : Fin 10 → ℝ) :
    (globalLogBox U).card=∏ i : Fin 10,(normLogBin (U i)+1) := by
  simp only [globalLogBox,Fintype.card_piFinset,Finset.card_range]


def globalPooledColumnScale (ell : ℝ) (j : GlobalLogIndex) : ℝ :=
  ell/(globalLogRep j 0*globalLogRep j 1*globalLogRep j 2*globalLogRep j 3*globalLogRep j 6*globalLogRep j 7)

def globalPooledLabelScale (j : GlobalLogIndex) : ℝ :=
  globalLogRep j 1*globalLogRep j 4*globalLogRep j 6*globalLogRep j 7*Real.exp 4

def globalPooledRowScale (K ell B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)

def globalPooledDelta (B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  B*F*globalLogRep j 0*globalLogRep j 2*globalLogRep j 3

def globalPooledNaturalRow (K B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  K*globalLogRep j 4/((globalPooledDelta B F j)^2*B^2)

theorem globalPooledColumnScale_pos (ell : ℝ) (hell : 0 < ell) (j : GlobalLogIndex) :
    0 < globalPooledColumnScale ell j := by
  unfold globalPooledColumnScale
  apply div_pos hell
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (globalLogRep_pos j 0)
    (globalLogRep_pos j 1)) (globalLogRep_pos j 2)) (globalLogRep_pos j 3))
    (globalLogRep_pos j 6)) (globalLogRep_pos j 7)

theorem globalPooledLabelScale_ge_one (j : GlobalLogIndex) : 1 ≤ globalPooledLabelScale j := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 1) (globalLogRep_ge_one j 4))
        (globalLogRep_ge_one j 6)) (globalLogRep_ge_one j 7)) (Real.one_le_exp (by norm_num))

theorem globalPooled_mass (ell B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledColumnScale ell j*globalPooledLabelScale j =
      Real.exp 4*((ell*B^3)*F)*globalLogRep j 4/(globalPooledDelta B F j*B^2) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledColumnScale globalPooledLabelScale globalPooledDelta
  field_simp [h]

theorem globalPooled_radial_ratio (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledRowScale K ell B F j*globalLogRep j 8/
      (globalLogRep j 5*(globalLogRep j 6)^2*(globalLogRep j 7)^2*(globalPooledColumnScale ell j)^2) =
    Real.exp 1*(globalLogRep j 8/globalPooledNaturalRow K B F j) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledRowScale globalPooledColumnScale globalPooledNaturalRow globalPooledDelta
  field_simp [h]

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson

theorem maskedPairDualTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M N K : ℝ),
      G≠0 → I≠0 → J≠0 → 0<M → 1≤N → 0≤K →
      N/2≤(Ideal.absNorm I:ℝ) → (Ideal.absNorm I:ℝ)≤N →
      N/2≤(Ideal.absNorm J:ℝ) → (Ideal.absNorm J:ℝ)≤N →
      ‖maskedPairDualTail G I J W M K‖ ≤
        (2*M/N)*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := dualSquarefreeTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro G I J W M N K hG hI hJ hM hN hK hIl hIu hJl hJu
  have hNG : 0<(Ideal.absNorm G:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hG (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNI : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hNJ : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hN0 : 0<N := by linarith
  let t0 := M/((Ideal.absNorm G:ℝ)*N*N)
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 t0)^2*(1+t0*K)^A)
  have ht0 : 0<t0 := by dsimp only [t0]; positivity
  have hT : 0≤T := by dsimp only [T]; positivity
  have hterm (q : Ideal O) (hq : q∈idealDivisors G) :
      ‖((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖ ≤ T := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q≠0 := by intro hz; rw [hz,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1≤(Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hq0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hqN : (Ideal.absNorm q:ℝ)≤(Ideal.absNorm G:ℝ) := by
      exact_mod_cast Nat.le_of_dvd (by exact_mod_cast hNG) (map_dvd Ideal.absNorm hqG)
    have ht : 0<M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by positivity
    have htlo : t0≤M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)) := by
      apply div_le_div_of_nonneg_left hM.le (by positivity)
      gcongr
    have hc : ‖(UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ)‖≤1 := by
      rw [norm_div,norm_mul,Complex.norm_natCast]
      have hp : ‖unrestrictedPairCharacter I J q‖≤1 := by
        rw [unrestrictedPairCharacter,norm_mul]
        exact (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      calc
        _ ≤ (1*1)/(Ideal.absNorm q:ℝ) := by
          gcongr
          exact QuadraticInitialBound.norm_ideal_moebius_le_one q
        _ ≤ 1 := by simpa only [one_mul,div_one] using (one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hq1)
    have hb : ‖dualSquarefreeTail I J W
        (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K‖≤T := by
      apply (hbound I J W _ K ht hK).trans
      dsimp only [T]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    rw [norm_mul]
    exact (mul_le_mul hc hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hpref : ‖(M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ)‖≤2*M/N := by
    simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hM.le,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    simpa only [mul_one,one_mul] using
      dual_truncation_prefactor_bound M 1 N (Ideal.absNorm I) (Ideal.absNorm J)
        hM (by norm_num) hN0 ⟨hIl,hIu⟩ ⟨hJl,hJu⟩
  rw [maskedPairDualTail,norm_mul]
  calc
    _ ≤ (2*M/N)*(∑ q ∈ idealDivisors G, T) := mul_le_mul hpref
      ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,T,t0]; ring

theorem coprime_pair_error_energy {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (E : ℝ) (hE : 0≤E)
    (error : n → n → ℂ) (herr : ∀ j k, ‖error j k‖≤E) :
    ‖∑ j, ∑ k, if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ ≤
      (Fintype.card n:ℝ)*E*∑ j, ‖a j‖^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1:ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖*‖a k‖*E) = (∑ j, ‖a j‖)^2*E := by
    simp only [pow_two,Finset.sum_mul,Finset.mul_sum,mul_assoc]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ ≤ ∑ j, ∑ k, ‖if IsCoprime (cols j) (cols k) then star (a j)*a k*error j k else 0‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ k, ‖a j‖*‖a k‖*E := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      split_ifs
      · simp only [norm_mul,norm_star]
        exact mul_le_mul_of_nonneg_left (herr j k) (by positivity)
      · simp only [norm_zero]
        positivity
    _ = (∑ j, ‖a j‖)^2*E := hs
    _ ≤ ((∑ j, ‖a j‖^2)*(Fintype.card n:ℝ))*E := mul_le_mul_of_nonneg_right hcs hE
    _ = _ := by ring

theorem maskedDualTailFamily_bound (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ)
      (W : 𝓢(ℝ,ℂ)) (M N K : ℝ), G≠0 → Function.Injective cols →
      0<M → 1≤N → 0≤K →
      (∀ j, cols j≠0 ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
      ‖maskedDualTailFamily G cols a W M K‖ ≤
        256*M*(idealDivisors G).card*
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
            ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*
              (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)) * ∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := maskedPairDualTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro n _ G cols a W M N K hG hinj hM hN hK hcols
  let T := (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (M/((Ideal.absNorm G:ℝ)*N*N)))^2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K)^A)
  have hT : 0≤T := by dsimp only [T]; positivity
  have hn := finite_ideal_family_card_bound cols hinj N hN
    (fun j => (hcols j).1) (fun j => (hcols j).2.2)
  have herr (j k : n) : ‖maskedPairDualTail G (cols j) (cols k) W M K‖≤
      (2*M/N)*(idealDivisors G).card*T :=
    hbound G (cols j) (cols k) W M N K hG (hcols j).1 (hcols k).1 hM hN hK
      (hcols j).2.1 (hcols j).2.2 (hcols k).2.1 (hcols k).2.2
  calc
    _ ≤ (Fintype.card n:ℝ)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 :=
      coprime_pair_error_energy cols a _ (by positivity) _ herr
    _ ≤ (128*N)*((2*M/N)*(idealDivisors G).card*T)*∑ j, ‖a j‖^2 := by gcongr
    _ = _ := by dsimp only [T]; field_simp; ring

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic


open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)


variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]


def globalNormCaps (ell B Y M Z : ℝ) : Fin 10 → ℝ :=
  let lengthScale := ell*Real.exp M
  ![lengthScale,lengthScale,lengthScale,lengthScale,B^2,lengthScale*B^2,lengthScale,lengthScale,3*lengthScale^2*B^2*((⌈Z*lengthScale^2/Y⌉₊ : ℝ)+1)^2,B^2]


end SecondPassArithmetic

end

end OAI

end


