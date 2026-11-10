-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
-- name    : OAI_NumberTheory_DirichletL_GaussSum_CompletedDyadicRows
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T19:23:06.79331+00:00
-- url     : https://prove2.me/theorems/eb5b3c9f-e448-42b3-afaf-6fd84a864908
-- title:
--   Completed Dyadic Rows
-- statement:
--   Definitions and structural lemmas for Completed Dyadic Rows, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/CompletedDyadicRows.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_LocalCutoffs
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
namespace CompletedGauss
section
open ActualEisensteinCubic
def completedRowDyad (rows : Finset (Ideal O)) (j : ℕ) : Finset (Ideal O) :=
  rows.filter (fun I => Nat.clog 2 (Ideal.absNorm I)=j)
def completedRowDyadicLength (K : ℝ) : ℕ := Nat.clog 2 ⌊K⌋₊
open ActualEisensteinCubic CanonicalQuadraticSieve
def HasExactCompletedDyadicModels (rays : ℕ) (rows : Finset (Ideal O))
    (K X ρ q levelBound : ℝ) (F Q : Ideal O) (W : ℝ→ℂ) (Ψ : Ideal O→O→*ℂ) (lengthScale : ℂ) : Prop :=
  ∀j∈Finset.range (completedRowDyadicLength K+1),
    HasExactCompletedModels rays (completedRowDyad rows j) ((2:ℝ)^j) X ρ q levelBound F Q W Ψ lengthScale
end
section
open CompletedDyadic
def completedRamifiedInitial : ℝ := (3:ℝ)^(-(4/3:ℝ))
def completedRamifiedStep : ℝ := (3:ℝ)^(1/3:ℝ)
def normalizedCuspAmplitude (d : ℂ) (m b : ℝ) : ℂ :=
  d/((27*(3:ℝ)^(m/6)*Real.sqrt b:ℝ):ℂ)
end
open ActualEisensteinCubic CanonicalQuadraticSieve
end CompletedGauss
open scoped BigOperators Classical SchwartzMap
namespace InitialMeanSquare
section
open ActualEisensteinCubic SecondPassArithmetic
open CanonicalQuadraticSieve (Admissible)
variable {ι : Type*} [DecidableEq ι] (p : ι → OAI.InitialMeanSquare.O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def initialSquarefreeSector (s : Finset (SecondExpansionData ι)) : Finset (SecondExpansionData ι) :=
  s.filter (fun x => Squarefree (Ideal.span {(sourceObservation p x).2}))
end
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
end InitialMeanSquare
open MeasureTheory
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels
end InitialMeanSquare
end
end OAI


