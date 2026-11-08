-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularRecursion
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T08:02:27.232614+00:00
-- url     : https://prove2.me/theorems/ccef8a16-8e8f-49e2-8711-bec8ccd024a3
-- title:
--   Annular Recursion
-- statement:
--   Definitions and structural lemmas for Annular Recursion, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularRecursion.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GcdReduction
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
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction
def weightedRayGramMatrix {m n : Type*} [Fintype m]
    (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) (rows : m → Ideal O) (cols : n → Ideal O)
    (v : m → ℝ) : Matrix n n ℂ :=
  fun j k => ∑ i, (v i : ℂ) *
    (if gcd (cols j) (cols k) = D ∧ columnRay (cols j) = c ∧ columnRay (cols k) = c then
      star (quadraticRow (cols j) (primaryGenerator (rows i))) *
        quadraticRow (cols k) (primaryGenerator (rows i)) else 0)
def smoothRayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖smoothRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2)))
def smoothThirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, smoothRayThirdNorm M N K D c
end
section
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel
def rayPairValue (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) : ℂ :=
  ∑ J : idealRange N, ∑ lengthScale : idealRange N,
    gcdTerm D (fun _ : Unit => I) (fun J : idealRange N => J.val)
      (sectorCoefficient (fun J : idealRange N => columnRay J.val) c a) () J lengthScale
end
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
def highKernelShellRange (M K : ℝ) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => M / 2 < (Ideal.absNorm I : ℝ))
def highKernelShellMatrix (M N K : ℝ) : Matrix (highKernelShellRange M K) (idealRange N) ℂ :=
  fun I J => quadraticRow J.val (primaryGenerator I.val)
def highKernelShellNorm (M N K : ℝ) : ℝ := ‖operator (highKernelShellMatrix M N K)‖ ^ 2
end CanonicalQuadraticSieve
open scoped SchwartzMap ContDiff
namespace QuadraticInitialBound
def annularSieveBump : ContDiffBump (3 / 4 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num
def annularSieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    annularSieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp annularSieveBump.contDiff
  exact hc.toSchwartzMap hs
end QuadraticInitialBound
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy
def annularHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.annularSieveBump ((Ideal.absNorm I : ℝ) / M)
def annularHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2
def annularRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val) a
end
section
open ActualEisensteinCubic CompletedGauss FiniteSieveOperator
open IdealCoprimeSieveOperator DivisorBlockCauchy FiniteSieveRestriction
def annularRayThirdNorm (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord) : ℝ :=
  sSup (Set.range (fun a : idealRange N → ℂ =>
    ‖annularRayGcdBlock M N K D c a‖ / (∑ J, ‖a J‖ ^ 2)))
def annularThirdNorm (M N K : ℝ) (D : Ideal O) : ℝ :=
  ∑ c : EisensteinEPrimaryPhase.Coord, annularRayThirdNorm M N K D c
end
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel
end CanonicalQuadraticSieve
namespace FiniteSieveOperator
end FiniteSieveOperator
namespace CanonicalQuadraticSieve
section
open FiniteSieveOperator
end
open IdealCoprimeSieveOperator DivisorBlockCauchy
end CanonicalQuadraticSieve
end
end OAI


