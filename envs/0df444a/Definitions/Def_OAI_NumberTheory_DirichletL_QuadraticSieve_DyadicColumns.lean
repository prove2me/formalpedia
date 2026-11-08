-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
-- name    : OAI_NumberTheory_DirichletL_QuadraticSieve_DyadicColumns
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T09:54:58.248125+00:00
-- url     : https://prove2.me/theorems/e0e31cd7-9c2a-4a04-b5b1-0f53a2ab00a6
-- title:
--   Dyadic Columns
-- statement:
--   Definitions and structural lemmas for Dyadic Columns, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/QuadraticSieve/DyadicColumns.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ConstantDirichletSeries
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
def columnDyadicLength (N : ℝ) : ℕ := ⌈Real.log N / Real.log 2⌉₊
theorem columnDyadicLength_cover (N : ℝ) : N ≤ (2 : ℝ) ^ columnDyadicLength N := by
  apply Real.pow_le_of_le_log (by norm_num : (0 : ℝ) < 2)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact (div_le_iff₀ hlog).mp (Nat.le_ceil (Real.log N / Real.log 2))
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel
def dualSquarefreeTail (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : {lengthScale : Ideal O // lengthScale ≠ 0 ∧ K < (Ideal.absNorm (squarefreePart lengthScale) : ℝ)},
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ))
end CanonicalQuadraticSieve
open scoped BigOperators Classical
namespace CubicEisenstein
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
def fullIdealWeight (s : ℂ) (I : Ideal O) : ℂ :=
  if I=0 then 0 else (Ideal.absNorm I:ℂ)^(-s)
def fullIdealZeta (s : ℂ) : ℂ := ∑' I : Ideal O,fullIdealWeight s I
end
section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
end
open Filter
open scoped BigOperators Classical Topology
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
def unramifiedZetaResidue : ℂ :=
  (2/3:ℂ)*(NumberField.dedekindZeta_residue ActualEisensteinCubic.K:ℂ)
def constantArithmeticResidue : ℂ := unramifiedZetaResidue /
  (3*((9*Real.sqrt 3/2:ℝ):ℂ)*unramifiedIdealZeta 2)
end CubicEisenstein
open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
section
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss
end
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel
def dualSquarefreeLow (I J : Ideal O) (W : ℝ → ℂ) (t K : ℝ) : ℂ :=
  ∑' lengthScale : NonzeroIdeal, if (Ideal.absNorm (squarefreePart lengthScale.val) : ℝ) ≤ K then
    unrestrictedPairCharacter I J lengthScale.val * paperRadialFourier W (t * (Ideal.absNorm lengthScale.val : ℝ)) else 0
end CanonicalQuadraticSieve
end
end OAI


