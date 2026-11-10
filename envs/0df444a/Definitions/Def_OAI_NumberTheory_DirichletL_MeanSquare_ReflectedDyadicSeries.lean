-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
-- name    : OAI_NumberTheory_DirichletL_MeanSquare_ReflectedDyadicSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T13:50:23.222944+00:00
-- url     : https://prove2.me/theorems/24281940-5dae-402f-b52f-4e9c95ce8b40
-- title:
--   Reflected Dyadic Series
-- statement:
--   Definitions and structural lemmas for Reflected Dyadic Series, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/ReflectedDyadicSeries.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_DyadicKernel
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
namespace InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
end
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
def initialBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃))
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap ContDiff
namespace CompletedGauss
section
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
end
open ActualEisensteinCubic
def completedShellWindow (x : ℝ) : ℂ :=
  if -Real.log 2≤x ∧ x≤0 then 1 else 0
def reflectedDyadicCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r : ℝ)
    (n v : Ideal O) : ℂ :=
  η n v*reflectedBranch P hg j e
    (primaryGenerator (reflectionExtractedDivisor P j e 1*n))
    (primaryGenerator (reflectionExtractedDivisor P j e 2*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2*v):ℝ):ℝ):ℂ)
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedDyadic
def reflectedBranchBlock {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ)
    (σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  σ i k*completedSmoothDyadicBlock completedShellWindow completedShellWindow completedShellWindow
    W K Y ρ q S T (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1)) i k
end CompletedGauss
end
end OAI


