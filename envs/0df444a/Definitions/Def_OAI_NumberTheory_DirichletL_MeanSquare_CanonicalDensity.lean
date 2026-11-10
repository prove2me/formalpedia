-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
-- name    : OAI_NumberTheory_DirichletL_MeanSquare_CanonicalDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T23:41:35.40845+00:00
-- url     : https://prove2.me/theorems/15cb44f8-0b2f-424d-88c0-c0b179a6ccfd
-- title:
--   Canonical Density
-- statement:
--   Definitions and structural lemmas for Canonical Density, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/CanonicalDensity.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DualZeroMode
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poolPrimary_coprime

set_option autoImplicit false
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
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels
variable {ι:Type*} [DecidableEq ι]
  (p:ι→OAI.SecondPassArithmetic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
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
def canonicalSourceBlocks (pool:Finset ι) (bs:Finset (CubeCoordinates ι)):Finset (GlobalCubeBlock ι):=
  bs.biUnion (fun b=>(pool\b.support).powerset.biUnion (fun C=>
    (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.image
      (sourceGlobalBlock b C)))
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels
variable {ι:Type*} [DecidableEq ι]
  (p:ι→OAI.SecondPassArithmetic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})
def canonicalSourceCutoff (K ell:ℝ) (b:CubeCoordinates ι) (C D:Finset ι):Finset O:=
  firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
def canonicalSourceTotal (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc
def canonicalSourceZero (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc
def canonicalSourceFinite (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)
def canonicalSourceTail (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)
def canonicalBlockFrequencies (K ell:ℝ) (labels:Finset (Ideal O)) (q:GlobalCubeBlock ι):Finset (Ideal O×O):=
  labels.product ((firstFrequencyDisk (globalFirstFrequencyScale p K ell q)).erase 0)
def canonicalBlockCoefficient (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (q:GlobalCubeBlock ι) (x:Ideal O×O):ℂ:=
  a q.cube.swap q.common x.1*canonicalCubeOuter p hp hcop hg q.cube.swap q.common
    Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)
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
end InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)
abbrev OutsidePrimeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) :=
  primePool (outsideSquarefreeIdeals S D)
def outsidePrime (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) : OutsidePrimeIndex S D → ActualEisensteinCubic.O :=
  poolPrimary (outsideSquarefreeIdeals S D)
lemma outsidePrime_ne_zero (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,outsidePrime S D i ≠ 0 :=
  poolPrimary_ne_zero _ (outsideSquarefree_admissible S D hbad)
lemma outsidePrime_maximal (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,(Ideal.span {outsidePrime S D i}).IsMaximal := by
  intro i
  rw [show Ideal.span {outsidePrime S D i}=i.val from
    poolPrimary_span _ (outsideSquarefree_admissible S D hbad) i]
  infer_instance
lemma outsidePrime_coprime (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {outsidePrime S D i})) :=
  poolPrimary_coprime _ (outsideSquarefree_admissible S D hbad)
lemma outsidePrime_good (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,lambda ∉ Ideal.span {outsidePrime S D i} :=
  poolPrimary_good _ (outsideSquarefree_admissible S D hbad)
def initialExcludedNorm (S : Finset (Ideal ActualEisensteinCubic.O)) : ℝ :=
  max 1 (∏ P ∈ S,(Ideal.absNorm P : ℝ))
def outsideCanonicalDensity {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ)
    (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ) (X : ℝ) (J : ℕ) : ℝ :=
  letI := outsidePrime_maximal S hbad D
  densityChildEnergy (outsidePrime S D) (outsidePrime_ne_zero S hbad D)
    (outsidePrime_coprime S hbad D) (outsidePrime_good S hbad D) Finset.univ
    (secondRayMinus (conjugateMonoid (normCharacter χ)) ray)
    (secondRayPlus (conjugateMonoid (normCharacter χ)) ray)
    (primeSubsetGenerator (fun i => Ideal.span {outsidePrime S D i}) R) T V₁ V₂ X X (2*J)
def HasInitialCanonicalDensity {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) : Prop :=
  ∀ deltaLoss : ℝ,0 < deltaLoss → ∀ P : ℕ,∃ J : ℕ,
    ∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
    ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ P ≤ E ∧ ∀ (D : ℕ) (Z X lengthScale K : ℝ)
      (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
      1 ≤ Z → Cpool*Z^E ≤ D → 1 ≤ X → 1 ≤ lengthScale → 1 ≤ K →
      X ≤ Z^P → lengthScale ≤ Z^P → K ≤ Z^P →
      initialExcludedNorm S*primeProductNorm (outsidePrime S D) R ≤ Z^P →
      X*lengthScale ≤ Z^2 →
      K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) →
      (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
        z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) →
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^deltaLoss*(X*lengthScale)^2
end InitialMeanSquare
end
end OAI


