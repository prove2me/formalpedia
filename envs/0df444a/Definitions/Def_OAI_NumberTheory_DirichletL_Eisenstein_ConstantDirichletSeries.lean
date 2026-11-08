-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
-- name    : OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:52:32.196193+00:00
-- url     : https://prove2.me/theorems/2a1960a5-3ef3-45dd-94ee-1527cf549427
-- title:
--   Constant Dirichlet Series
-- statement:
--   Definitions and structural lemmas for Constant Dirichlet Series, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Eisenstein/ConstantDirichletSeries.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyCutoffs
import Theorems.Thm_OAI_CanonicalQuadraticSieve_exists_dyadic_shell

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
namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
end CubicEisenstein
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge
end
section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson GaussGeneratorTransport UnrestrictedIdealReindex
open TruncatedPrincipalPoisson QuadraticSquarefreeKernel
def dualPrincipalIdeal (I J : Ideal O) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' A : NonzeroIdeal,
    (idealZeroMask I (idealGenerator A.val) * idealZeroMask J (idealGenerator A.val)) *
      V ((Ideal.absNorm A.val : ℝ) / X)
def dualPrincipalLattice (I J : Ideal O) (V : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, rowCoprimeMask (fun P : primePool {I * J} => P.val) Finset.univ z *
    V (‖eisEmbedding z‖ ^ 2 / X)
end
section
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum
open QuadraticMainOperatorBound IdealCoprimeSieveOperator DivisorBlockCauchy
def canonicalMainBoundary (H : Finset (Ideal O)) (G : Ideal O) (K N : ℝ)
    (a : idealRange N → ℂ) : ℂ :=
  ∑ D ∈ idealDivisors G, ∑ E ∈ idealDivisors G,
    (UniqueFactorizationMonoid.moebius E : ℂ) *
    (∑ B : H, mainWeight K B.val D E *
      (∑ J : idealRange N, ∑ lengthScale : idealRange N, if IsCoprime J.val lengthScale.val then
        star (quadraticRow J.val (primaryGenerator B.val) *
          (a J * quadraticRow J.val (primaryGenerator D * primaryGenerator E))) *
        (quadraticRow lengthScale.val (primaryGenerator B.val) *
          (a lengthScale * quadraticRow lengthScale.val (primaryGenerator D * primaryGenerator E))) else 0))
end
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
def CoefficientOnShell (N X : ℝ) (a : idealRange N → ℂ) : Prop :=
  ∀ J, a J ≠ 0 → X / 2 < (Ideal.absNorm J.val : ℝ) ∧ (Ideal.absNorm J.val : ℝ) ≤ X
theorem column_dyadic_exists (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : idealRange N) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < (Ideal.absNorm J.val : ℝ) ∧
      (Ideal.absNorm J.val : ℝ) ≤ (2 : ℝ) ^ j := by
  have hn : 1 ≤ Ideal.absNorm J.val := Nat.one_le_iff_ne_zero.mpr
    (fun hz => (mem_idealRange.mp J.property).1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  exact exists_dyadic_shell (Ideal.absNorm J.val) lengthScale hn ((mem_idealRange.mp J.property).2.trans hNL)
def columnDyadicSector (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : idealRange N) : Fin (lengthScale + 1) :=
  ⟨(column_dyadic_exists N lengthScale hNL J).choose,
    Finset.mem_range.mp (column_dyadic_exists N lengthScale hNL J).choose_spec.1⟩
def dyadicColumnCoefficient (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  sectorCoefficient (columnDyadicSector N lengthScale hNL) j a
def coefficientAtScale (N X : ℝ) (a : idealRange N → ℂ) (J : idealRange X) : ℂ :=
  if h : J.val ∈ idealRange N then a ⟨J.val, h⟩ else 0
end CanonicalQuadraticSieve
end
end OAI


