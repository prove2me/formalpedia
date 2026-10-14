-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0122_parallel1_1
-- name    : PNT_ZeroFree_433_0122_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T12:38:44.624237+00:00
-- url     : https://prove2.me/theorems/5e27526d-6e5e-41ef-9113-ac1d86aaa26c
-- title:
--   Zero-free region foundations: QuadraticSieve.RetainedDualBounds [0122_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.RetainedDualBounds
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/RetainedDualBounds.lean#L83-L531

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0038_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0044
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0055
import Definitions.Def_PNT_ZeroFree_433_0056_1
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0064
import Definitions.Def_PNT_ZeroFree_433_0068
import Definitions.Def_PNT_ZeroFree_433_0072
import Definitions.Def_PNT_ZeroFree_433_0077
import Definitions.Def_PNT_ZeroFree_433_0089
import Definitions.Def_PNT_ZeroFree_433_0090
import Definitions.Def_PNT_ZeroFree_433_0091
import Definitions.Def_PNT_ZeroFree_433_0092
import Definitions.Def_PNT_ZeroFree_433_0094
import Definitions.Def_PNT_ZeroFree_433_0097
import Definitions.Def_PNT_ZeroFree_433_0098
import Definitions.Def_PNT_ZeroFree_433_0105
import Definitions.Def_PNT_ZeroFree_433_0112
import Definitions.Def_PNT_ZeroFree_433_0113
import Definitions.Def_PNT_ZeroFree_433_0114
import Definitions.Def_PNT_ZeroFree_433_0148
import Definitions.Def_PNT_ZeroFree_433_0173_parallel1
import Definitions.Def_PNT_ZeroFree_433_0241
import Definitions.Def_PNT_ZeroFree_433_0242_parallel2
import Definitions.Def_PNT_ZeroFree_433_0260_parallel2
import Definitions.Def_PNT_ZeroFree_433_0265_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0275_parallel1

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

section

open scoped BigOperators Classical SchwartzMap

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def primePoolDensity (G : Ideal O) : ℂ :=
  ∏ P : primePool {G}, (1-(1:ℂ)/(Ideal.absNorm P.val:ℂ))

theorem principalTruncation_scaled (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Z : ℝ) :
    (c:ℂ)*principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      ((c*X:ℝ):ℂ)*paperRadialFourier W 0*primePoolDensity G -
      paperRadialFourier W 0 * (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) := by
  classical
  have hl : (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ((c*X:ℝ):ℂ)*(∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : Z < (Ideal.absNorm d:ℝ)
    · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
      ring
    · simp only [hd,ite_false,mul_zero]
  have hs : (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) =
      (c:ℂ)*(∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (Ideal.absNorm d:ℝ) ≤ Z <;> simp only [hd,ite_true,ite_false,mul_zero] ; ring
  rw [principalTruncation_eq_ideal_divisors G hG,hl,hs]
  unfold primePoolDensity
  push_cast
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]


end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem dualPrincipalIdeal_truncated_all_conductors
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (V : 𝓢(ℝ,ℂ)) (X Y Z lengthScale : ℝ) (hX : 0<X) :
    dualPrincipalIdeal I J V X = (6:ℂ)⁻¹ *
      (principalTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Z +
       middleTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale +
       truncationError (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale) := by
  let P := fun P : primePool {I*J} => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z *
    (if z=0 then 0 else V (‖eisEmbedding z‖^2/X))
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    by_cases hz : z=0
    · simp only [hz,ite_true,mul_zero,norm_zero]
      exact norm_nonneg _
    · rw [if_neg hz,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one P Finset.univ z)
  have h0 : f 0=0 := by simp only [f,ite_true,mul_zero]
  have hu (u : Oˣ) (z : O) : f (u.val*z)=f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul,norm_eisEmbedding_unit_mul]
    simp only [mul_eq_zero,u.ne_zero,false_or]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hm (z : O) : rowCoprimeMask P Finset.univ z=idealZeroMask I z*idealZeroMask J z := by
    rw [singleton_rowCoprimeMask_eq_idealZeroMask,idealZeroMask_mul I J hI.1 hJ.1]
  have hd : (∑' A : NonzeroIdeal, f (idealGenerator A.val))=dualPrincipalIdeal I J V X := by
    unfold dualPrincipalIdeal
    apply tsum_congr
    intro A
    simp only [f,hm,if_neg (idealGenerator_ne_zero A.val A.property),idealGenerator_norm_sq]
  rw [hd] at he
  have hs : principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale = ∑' z : O, f z := by
    unfold truncationError
    dsimp only [f]
    ring
  change dualPrincipalIdeal I J V X=(6:ℂ)⁻¹ *
    (principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale)
  rw [hs,he]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator


lemma norm_four_correction_terms (A B C D : ℂ) :
    ‖-A-B+C+D‖ ≤ ‖A‖+‖B‖+‖C‖+‖D‖ := by
  have hab := norm_sub_le (-A) B
  have habc := norm_add_le (-A-B) C
  have habcd := norm_add_le (-A-B+C) D
  simp only [norm_neg] at hab
  linarith


lemma sum_ideal_subtype_dyadic {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (K : ℝ) (f : Ideal O → A) :
    (∑ I : S, f I.val) = ∑ j : Fin (columnDyadicLength K+1),
      ∑ I : divisorDyadicBin S K j, f I.val := by
  classical
  rw [Finset.sum_coe_sort S f,sum_divisorDyadicBins S K f]
  exact Finset.sum_congr rfl (fun j _ => (Finset.sum_coe_sort (divisorDyadicBin S K j) f).symm)


end

open scoped BigOperators Classical
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss

def highSquareParts (M K : ℝ) : Finset (Ideal O) := (highKernelRange M K).image squarePart


end CanonicalQuadraticSieve

end

end OAI

end


