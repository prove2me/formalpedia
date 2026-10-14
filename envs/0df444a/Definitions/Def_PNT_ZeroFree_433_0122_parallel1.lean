-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0122_parallel1
-- name    : PNT_ZeroFree_433_0122_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:40:46.830991+00:00
-- url     : https://prove2.me/theorems/305f33b9-9b7b-4b12-bca6-ac47595203d2
-- title:
--   Zero-free region foundations: QuadraticSieve.RetainedDualBounds [0122_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.RetainedDualBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/RetainedDualBounds.lean#L533-L648

import Definitions.Def_PNT_ZeroFree_433_0122_parallel1_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/RetainedDualBounds.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
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


open scoped BigOperators Classical
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss


theorem highSquareParts_bounds (M K : ℝ) (hK : 0 < K) (A : Ideal O)
    (hA : A ∈ highSquareParts M K) :
    Supported A ∧ 1 ≤ (Ideal.absNorm A : ℝ) ∧
    (Ideal.absNorm A : ℝ) ≤ Real.sqrt (M/K) ∧
    1 ≤ M/(Ideal.absNorm A : ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨hs,hN,hlarge⟩ := mem_highKernelRange.mp hI
  have hparts := (supported_square_parts I).mp hs
  have hna : 1 ≤ (Ideal.absNorm (squarePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnb : 1 ≤ (Ideal.absNorm (squarefreePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.2.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hprod : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) ≤ M := by
    have he : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) =
        (Ideal.absNorm I : ℝ) := by exact_mod_cast norm_decomposition I
    rwa [he]
  have hsquare : (Ideal.absNorm (squarePart I) : ℝ)^2 ≤ M/K := by
    apply (le_div_iff₀ hK).mpr
    exact (mul_le_mul_of_nonneg_left hlarge.le (sq_nonneg _)).trans hprod
  have hM : 0 ≤ M/K := (sq_nonneg _).trans hsquare
  have hroot : (Ideal.absNorm (squarePart I) : ℝ) ≤ Real.sqrt (M/K) := by
    nlinarith [Real.sq_sqrt hM,Real.sqrt_nonneg (M/K)]
  refine ⟨hparts.1,hna,hroot,?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (Ideal.absNorm (squarePart I) : ℝ)^2)).mpr
  nlinarith

theorem highSquarePart_fiber_row_bounds (M K : ℝ) (A I : Ideal O)
    (hI : I ∈ highKernelRange M K) (hA : squarePart I = A) :
    Admissible (squarefreePart I) ∧
      (Ideal.absNorm (squarefreePart I) : ℝ) ≤ M/(Ideal.absNorm A : ℝ)^2 := by
  have hs := (mem_highKernelRange.mp hI).1
  have hparts := (supported_square_parts I).mp hs
  have hna : 0 < (Ideal.absNorm A : ℝ) := by
    rw [←hA]
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hparts.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  refine ⟨hparts.2,(le_div_iff₀ (sq_pos_of_pos hna)).mpr ?_⟩
  have he : (Ideal.absNorm A : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) = (Ideal.absNorm I : ℝ) := by
    rw [←hA]
    exact_mod_cast norm_decomposition I
  simpa only [mul_comm,he] using (mem_highKernelRange.mp hI).2.1

def highSquarePartFiber (M K : ℝ) (A : Ideal O) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => squarePart I = A)

theorem highSquarePartFiber_energy (M N K : ℝ) (A : Ideal O)
    (a : idealRange N → ℂ) :
    (∑ I ∈ highSquarePartFiber M K A,
      ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖^2) ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N * ∑ J, ‖a J‖^2 := by
  let S := highSquarePartFiber M K A
  let b : idealRange N → ℂ := fun J => idealZeroMask J.val (primaryGenerator A) * a J
  let B : Matrix S (idealRange N) ℂ := fun I J =>
    quadraticRow J.val (primaryGenerator (squarefreePart I.val))
  have hinj : Function.Injective (fun I : S => squarefreePart I.val) := by
    intro I I' heq
    dsimp only at heq
    apply Subtype.ext
    have hI := (Finset.mem_filter.mp I.property).2
    have hI' := (Finset.mem_filter.mp I'.property).2
    calc
      I.val = A^2 * squarefreePart I.val := by
        simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
      _ = A^2 * squarefreePart I'.val := by rw [heq]
      _ = I'.val := by simpa only [hI'] using squarePart_sq_mul_squarefreePart I'.val
  have hnorm : ‖FiniteSieveOperator.operator B‖^2 ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N := by
    apply family_squared_norm_le (fun I : S => squarefreePart I.val)
      (fun J : idealRange N => J.val) hinj Subtype.val_injective
    · intro I
      exact highSquarePart_fiber_row_bounds M K A I.val
        (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2
    · intro J
      exact mem_idealRange.mp J.property
  have hrow (I : S) :
      (∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J) =
      ∑ J : idealRange N, B I J * b J := by
    apply Finset.sum_congr rfl
    intro J _
    have hI := (Finset.mem_filter.mp I.property).2
    have he : I.val = A^2 * squarefreePart I.val := by
      simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
    rw [he, canonical_quadraticRow_primary_squarefree J.val
      (mem_idealRange.mp J.property).1]
    change _ = quadraticRow J.val (primaryGenerator (squarefreePart I.val)) *
      (idealZeroMask J.val (primaryGenerator A) * a J)
    ring
  have hb (J : idealRange N) : ‖b J‖^2 ≤ ‖a J‖^2 := by
    dsimp only [b]
    unfold idealZeroMask
    split_ifs <;> simp
  rw [← Finset.sum_coe_sort S]
  simp_rw [hrow]
  exact (FiniteSieveOperator.energy_bound B b).trans
    ((mul_le_mul_of_nonneg_right hnorm (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun J _ => hb J)
        (sieveNorm_nonneg _ _)))

theorem highKernelNorm_le_squarePart_sum (M N K : ℝ) :
    highKernelNorm M N K ≤
      ∑ A ∈ highSquareParts M K, sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N := by
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _
    (Finset.sum_nonneg fun A _ => sieveNorm_nonneg _ _)
  intro a
  simp only [highKernelMatrix]
  rw [Finset.sum_coe_sort (highKernelRange M K)
    (fun I : Ideal O => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖^2)]
  have hmaps : ∀ I ∈ highKernelRange M K, squarePart I ∈ highSquareParts M K :=
    fun I hI => Finset.mem_image_of_mem squarePart hI
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ A ∈ highSquareParts M K,
        sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N * ∑ J, ‖a J‖^2 := by
      apply Finset.sum_le_sum
      intro A hA
      exact highSquarePartFiber_energy M N K A a
    _ = _ := (Finset.sum_mul _ _ _).symm

end CanonicalQuadraticSieve

end

end OAI

end


