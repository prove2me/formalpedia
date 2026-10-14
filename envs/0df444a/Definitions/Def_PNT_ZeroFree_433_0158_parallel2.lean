-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0158_parallel2
-- name    : PNT_ZeroFree_433_0158_parallel2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:43:32.205139+00:00
-- url     : https://prove2.me/theorems/9f0460cd-4188-495a-aff7-0fa6304d83bb
-- title:
--   Zero-free region foundations: MeanSquare.PoissonSource [0158_parallel2]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.MeanSquare.PoissonSource
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean#L607-L759

import Definitions.Def_PNT_ZeroFree_433_0158_parallel2_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/MeanSquare/PoissonSource.lean
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

open scoped BigOperators Classical SchwartzMap ContDiff


open scoped BigOperators


open scoped BigOperators Classical


open scoped BigOperators Classical SchwartzMap


open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels
open MixedCrossSeparation (columnCoefficient)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})


def canonicalCubeBeforePoisson (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    disjointCanonicalSource p hp hcop hg (pool\(b.support∪C))
      (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
      b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
      W (fun _=>1) (fun _=>1) 1 1 K

lemma cube_filter_left (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.leftBit i)=b.leftDivisor := by
  ext i
  simp only [CubeCoordinates.leftBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.1 hi)

lemma cube_filter_right (b : CubeCoordinates ι) (hb : b.Admissible) :
    b.support.filter (fun i=>b.rightBit i)=b.rightDivisor := by
  ext i
  simp only [CubeCoordinates.rightBit,Finset.mem_filter,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi=>hb.2 hi)

theorem canonicalCubeSourcePair_factor
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1)
    (b : CubeCoordinates ι) (hb : b.Admissible) (C N P : Finset ι)
    (hCB : Disjoint C b.support) (hNC : Disjoint N C) (hPC : Disjoint P C)
    (hNB : Disjoint N b.support) (hPB : Disjoint P b.support) (hNP : Disjoint N P)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeSourcePair p hp hcop hg b.support ((b.rightDivisor∪C)∪N) ((b.leftDivisor∪C)∪P)
      b.leftExponent b.rightExponent Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
      (star (columnCoefficient p hp hcop hg N*canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ N)*
        (columnCoefficient p hp hcop hg P*canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂ P))*
      ∑'z:O,rowCoprimeMask (fun i=>Ideal.span {p i})
        (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit) z*
        blockRow p hg ((N∪P)∪cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
          (threeBlockExponent N P (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) z*
        W (‖eisEmbedding z‖^2/K) := by
  have hN := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₁ m₁ f H₁
    b.support C N b.leftBit b.rightBit true hCB hNC hNB
  have hP := canonicalSourceCoefficient_cube_split p hp hcop hg hinj hpr Ψ₂ m₂ f H₂
    b.support C P b.leftBit b.rightBit false hCB hPC hPB
  simp only [Bool.false_eq_true,ite_true,ite_false,cube_filter_left b hb,cube_filter_right b hb] at hN hP
  have hz (z : O) := canonicalCube_pair_row p hg b.support C N P b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos hCB hNC hPC hNB hPB hNP z
  simp only [cube_filter_left b hb,cube_filter_right b hb] at hz
  simp only [canonicalCubeSourcePair,hN,hP,star_mul,canonicalCubeOuter,canonicalCubeResidual]
  simp only [Bool.false_eq_true,ite_true,ite_false]
  simp_rw [hz]
  ring


theorem canonicalCubeCorrelation_eq_blocks
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1) (pool : Finset ι) (v₁ v₂ : ι→₀ℕ)
    (hB : v₁.support∪v₂.support⊆pool)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂ Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      ∑A₂∈(v₁.support∪v₂.support).powerset,∑A₁∈(v₁.support∪v₂.support).powerset,
        ∑C∈(pool\(v₁.support∪v₂.support)).powerset,
          canonicalCubeBeforePoisson p hp hcop hg pool ⟨v₁,v₂,A₁,A₂⟩ C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K := by
  unfold canonicalCubeCorrelation
  rw [FiniteOverlapDecomposition.sum_pair_split_cube pool _ hB]
  apply Finset.sum_congr rfl
  intro A₂ hA₂
  apply Finset.sum_congr rfl
  intro A₁ hA₁
  apply Finset.sum_congr rfl
  intro C hC
  let b : CubeCoordinates ι:=⟨v₁,v₂,A₁,A₂⟩
  have hb : b.Admissible:=⟨Finset.mem_powerset.mp hA₁,Finset.mem_powerset.mp hA₂⟩
  have hCB : Disjoint C b.support := Finset.disjoint_left.mpr (fun i hiC hiB =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hiC)).2 hiB)
  have hpool : (pool\(v₁.support∪v₂.support))\C=pool\(b.support∪C) := by
    ext i
    simp only [CubeCoordinates.support,b,Finset.mem_sdiff,Finset.mem_union]
    tauto
  rw [hpool]
  change _=canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  simp only [canonicalCubeBeforePoisson,disjointCanonicalSource,Finset.mul_sum,one_mul]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · simp only [hNP,ite_true]
    have hNC : Disjoint N C:=Finset.disjoint_left.mpr (fun i hiN hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_right _ hiC))
    have hPC : Disjoint P C:=Finset.disjoint_left.mpr (fun i hiP hiC =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_right _ hiC))
    have hNB : Disjoint N b.support:=Finset.disjoint_left.mpr (fun i hiN hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 (Finset.mem_union_left _ hiB))
    have hPB : Disjoint P b.support:=Finset.disjoint_left.mpr (fun i hiP hiB =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hP) hiP)).2 (Finset.mem_union_left _ hiB))
    simpa only [mul_assoc,b,CubeCoordinates.support] using canonicalCubeSourcePair_factor p hp hcop hg hinj hpr b hb C N P
      hCB hNC hPC hNB hPB hNP Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K
  · simp only [hNP,ite_false,mul_zero]

theorem canonicalCubeBeforePoisson_eq_all_modes
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) :
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K =
      canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
        ∑'h:O,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
          W (fun _=>1) (fun _=>1) 1 1 K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  unfold canonicalCubeBeforePoisson
  rw [disjointCanonicalSource_poisson p hp hcop hg hinj hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ hK]


lemma canonicalCubeOuter_norm_le_one
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (b:CubeCoordinates ι) (C:Finset ι) (Ψ₁ Ψ₂:O→*ℂ)
    (hΨ₁:∀u,‖Ψ₁ u‖≤1) (hΨ₂:∀u,‖Ψ₂ u‖≤1) (m₁ m₂ f:O) :
    ‖canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f‖≤1 := by
  simp only [canonicalCubeOuter,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (canonicalSourceCoefficient_norm_le_one p hp hcop hg hc Ψ₁ hΨ₁ m₁ f _)).trans
    (canonicalSourceCoefficient_norm_le_one p hp hcop hg hc Ψ₂ hΨ₂ m₂ f _)

end SecondPassArithmetic

end

end OAI

end


