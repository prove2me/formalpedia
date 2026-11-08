-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
-- name    : OAI_NumberTheory_DirichletL_CubicSieve_PrincipalDensity
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-08T00:40:16.786439+00:00
-- url     : https://prove2.me/theorems/2714f97f-44d3-4072-8a58-df955dbf4d89
-- title:
--   Principal Density
-- statement:
--   Definitions and structural lemmas for Principal Density, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/PrincipalDensity.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_RetainedDualBounds
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
namespace SecondPassIntegration
open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic SecondPassArithmetic
end SecondPassIntegration
open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum
def sourcePrincipalScale (M : ℝ) (I : Ideal O) : ℝ := Real.sqrt (M/(Ideal.absNorm I:ℝ))
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def maskedSourceDensity (G : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ((sourcePrincipalScale M (rows i):ℝ):ℂ)*primePoolDensity (G*(cols j*cols k))
def maskedPrincipalSourceSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ z *
      (if z=0 then 0 else W (‖eisEmbedding z‖^2/sourcePrincipalScale M (rows i)))
def maskedSourcePrincipalTruncation (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    principalTruncation (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i)) (Z i)
def maskedSourceErrorSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    truncationError (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i))
      (sourcePrincipalScale M (rows i)/T)
      (T*sourcePrincipalScale M (rows i)) (T^4)
end
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator IdealMobiusDivisorSum
def sourcePrincipalMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*((idealDivisors G).card *
    (((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (4*N/T+Real.sqrt M*B^(α-1/2))))) +
  (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
    ((2*nonzeroLatticeEnvelopeConstant*originalMiddleDecayConstant W)*
      divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (N+(2*T)*Real.sqrt M*B^(α-1/2)))) +
  16384*B*N*((supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2
end
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator
end
section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
end
open ActualEisensteinCubic
def densityColumn {n : Type*} (cols : n → Ideal O) (a : n → ℂ) : n → ℂ :=
  fun j => primePoolDensity (cols j) * a j
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum
def densityPairSum {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (P : Ideal O → Ideal O → ℂ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*primePoolDensity (cols j*cols k)*P (cols j) (cols k) else 0
end CanonicalQuadraticSieve
end
end OAI


