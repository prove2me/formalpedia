-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0123
-- name    : PNT_ZeroFree_433_0123
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:46:35.323817+00:00
-- url     : https://prove2.me/theorems/46dc4c42-c05e-48ee-9992-ba636f5499e2
-- title:
--   Zero-free region foundations: QuadraticSieve.HighKernelGeometry [0123]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.HighKernelGeometry
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/HighKernelGeometry.lean#L77-L644

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0058
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0103
import Definitions.Def_PNT_ZeroFree_433_0118_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0123_parallel2
import Definitions.Def_PNT_ZeroFree_433_0124_parallel1
import Definitions.Def_PNT_ZeroFree_433_0127_parallel2
import Definitions.Def_PNT_ZeroFree_433_0128_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0135_parallel1
import Definitions.Def_PNT_ZeroFree_433_0137_parallel2
import Definitions.Def_PNT_ZeroFree_433_0181_parallel1
import Definitions.Def_PNT_ZeroFree_433_0208_parallel1
import Definitions.Def_PNT_ZeroFree_433_0264_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/HighKernelGeometry.lean
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic


theorem highSquareParts_card_le (M K : ℝ) (_hM : 0 ≤ M) (hK : 0 < K) :
    ((highSquareParts M K).card : ℝ) ≤ 128 * Real.sqrt (M/K) := by
  by_cases hempty : highSquareParts M K = ∅
  · simp only [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨A,hA⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hb := highSquareParts_bounds M K hK A hA
    apply DescentFiberCost.finite_ideal_count_real _ _ (hb.2.1.trans hb.2.2.1)
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).1.1
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).2.2.1

theorem HasSieveExponent.high_kernel {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ K →
      highKernelNorm M N K ≤ C * (M*N)^ε * (M + Real.sqrt (M/K)*N^α) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := h ε hε
  refine ⟨1024*C,by positivity,?_⟩
  intro M N K hM hN hK
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 < K := by linarith
  let S := highSquareParts M K
  have hrow (A : Ideal O) (hA : A ∈ S) :
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N ≤
        C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2 + N^α) := by
    have hb := highSquareParts_bounds M K hK0 A hA
    have hquot : M/(Ideal.absNorm A : ℝ)^2 ≤ M :=
      div_le_self hM0 (by nlinarith [sq_nonneg ((Ideal.absNorm A : ℝ)-1)])
    apply (hbound _ N hb.2.2.2 hN).trans
    gcongr
  have hsum : (∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2) ≤ 1024 := by
    apply finite_inverse_norm_square_sum S (Real.sqrt (M/K))
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).1.1
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).2.2.1
  have hcard : (S.card : ℝ) ≤ 128*Real.sqrt (M/K) := highSquareParts_card_le M K hM0 hK0
  have hcoeff : 0 ≤ C*(M*N)^ε := by positivity
  have hpow : 0 ≤ N^α := Real.rpow_nonneg hN0 _
  calc
    _ ≤ ∑ A ∈ S, sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N :=
      highKernelNorm_le_squarePart_sum M N K
    _ ≤ ∑ A ∈ S, C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2+N^α) :=
      Finset.sum_le_sum hrow
    _ = C*(M*N)^ε*(M*(∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2)+(S.card:ℝ)*N^α) := by
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ C*(M*N)^ε*(M*1024+(128*Real.sqrt (M/K))*N^α) := by gcongr
    _ ≤ (1024*C)*(M*N)^ε*(M+Real.sqrt (M/K)*N^α) := by
      have hroot : 0 ≤ Real.sqrt (M/K)*N^α := mul_nonneg (Real.sqrt_nonneg _) hpow
      nlinarith [mul_nonneg hcoeff hroot]

end CanonicalQuadraticSieve


end

end OAI

end


