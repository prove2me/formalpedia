-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-08T19:35:19.715457+00:00
-- url     : https://prove2.me/theorems/50563eed-ef7f-459d-b1be-baea742d4071
-- title:
--   Common Masks
-- statement:
--   Definitions and structural lemmas for Common Masks, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/CommonMasks.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
set_option autoImplicit false
namespace OAI
noncomputable section
namespace CanonicalQuadraticSieve
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
section
open scoped BigOperators Classical SchwartzMap
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex IdealMobiusDivisorSum
def maskedPairDualTail (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ((M:ℂ)/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)):ℂ))*
    ∑ q ∈ idealDivisors G,
      ((UniqueFactorizationMonoid.moebius q:ℂ)*unrestrictedPairCharacter I J q/(Ideal.absNorm q:ℂ))*
        dualSquarefreeTail I J W
          (M/((Ideal.absNorm q:ℝ)*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))) K
def retainedDualPair (I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M F K : ℝ) : ℂ :=
  ∑ B : squarefreeIdealRange K, unrestrictedPairCharacter I J B.val*
    (((M/(Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ))*F):ℝ):ℂ)*
      dualPrincipalIdeal I J W
        (Real.sqrt (F*(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)/(M*(Ideal.absNorm B.val:ℝ)))))
end
section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
def maskedDualFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairIdealDualKernel G (cols j) (cols k) W M else 0
def maskedDualTailFamily {n : Type} [Fintype n]
    (G : Ideal O) (cols : n → Ideal O) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*maskedPairDualTail G (cols j) (cols k) W M K else 0
end
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum
def pairMaskedSquareSource (G I J : Ideal O) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (B : Ideal O) : ℂ :=
  (quadraticRow I (primaryGenerator B)*quadraticRow J (primaryGenerator B))*
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(I*J)} => P.val) Finset.univ z *
      (if z=0 then 0 else quadraticSquareProfile W (‖eisEmbedding z‖^2/sourcePrincipalScale M B))
end
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
end
section
open scoped BigOperators Classical
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
end
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
def gcdRaySupport {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : Finset n :=
  Finset.univ.filter (fun j => D ∣ cols j ∧ columnRay (cols j)=c ∧ a j≠0)
end CanonicalQuadraticSieve
end
end OAI


