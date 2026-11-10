-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
-- name    : OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-09T11:52:04.349871+00:00
-- url     : https://prove2.me/theorems/d56d8d33-1170-432e-8a10-98dad0a2b211
-- title:
--   Input Energy
-- statement:
--   Definitions and structural lemmas for Input Energy, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/MeanSquare/InputEnergy.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
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
open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
end InitialMeanSquare
open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
open RayFourExpansion (RayCharacter)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
end
section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)
def globalFirstTailFactor (K ell B F U H : ℝ) (N : ℕ) : ℝ :=
  (1+U)^4*(1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2)))^2/(1+H)^N
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
end
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)
end SecondPassArithmetic
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
def globalFirstRayChildBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C Γ ε K ell B F M H U : ℝ) (A J : ℕ) (side : Bool) : ℝ :=
  let family := (globalFirstFamilySet pool blocks).filter
    (fun b => primeProductNorm p b.common≤U ∧ primeProductNorm p b.firstCommon≤U)
  let source := globalFirstSupportedPool p pool family
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  ∑a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑r : FirstCoreIndex,
    (∫t : ℝ,firstLogDensity 0 t)*globalChildBudget p hp hcop hg pool source
      (firstCoreTwist side (if side then a.1 else a.2) Ψ r) m windows (Γ*firstCoreUniformWeight r*C)
      ε 0 0 K ell B F M H A J side
def globalFirstQuantitativeBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C Cd Ct Γ ε K ell B F M H U : ℝ) (A J N : ℕ) (side : Bool) : ℝ :=
  (∫t : ℝ,firstLogDensity 0 t)*(512*(512*32))*Γ*(ell*B^3*F)*(B*U)^ε*
      (Cd+Ct*globalFirstTailFactor K ell B F U H N) +
    globalFirstRayChildBudget p hp hcop hg pool blocks Ψ m windows C Γ ε K ell B F M H U A J side
end
end SecondPassArithmetic
end
end OAI


