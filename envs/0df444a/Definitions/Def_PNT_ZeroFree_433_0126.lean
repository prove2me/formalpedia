-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0126
-- name    : PNT_ZeroFree_433_0126
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:12:47.258489+00:00
-- url     : https://prove2.me/theorems/ba141dc5-152b-4772-9a1d-a2a6bfe1282c
-- title:
--   Zero-free region foundations: QuadraticSieve.CuspCoercivity [0126]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.CuspCoercivity
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean#L77-L601

import Definitions.Def_PNT_ZeroFree_433_0120
import Definitions.Def_PNT_ZeroFree_433_0122_parallel1
import Definitions.Def_PNT_ZeroFree_433_0125
import Definitions.Def_PNT_ZeroFree_433_0126_parallel1
import Definitions.Def_PNT_ZeroFree_433_0126_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/CuspCoercivity.lean
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
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem unrestrictedPrincipalDensity_twisted_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q))
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ)) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
  rw [unrestrictedPrincipalDensity_squarefree _ _ _ _ (by positivity),Real.sqrt_div hM]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),
      normalizedIdealPair,unrestrictedPairCharacter,Complex.ofReal_div]
    ring
  · simp only [hc,ite_false,mul_zero]

theorem densityPairSum_weighted_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (P : Ideal O → Ideal O → ℂ) (Q : ι → Ideal O → Ideal O → ℂ) :
    (∑ q ∈ S, c q*densityPairSum cols a (fun I J => P I J*Q q I J)) =
      densityPairSum cols a (fun I J => P I J*∑ q ∈ S, c q*Q q I J) := by
  simp only [densityPairSum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero]

theorem summed_dual_density {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) := by
  simp_rw [unrestrictedPrincipalDensity_twisted_squarefree cols a _ M K hM hcols]
  calc
    _ = (Real.sqrt M : ℂ)*∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        densityPairSum cols a (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      rw [densityPairSum_weighted_sum]
      rfl

theorem actual_source_dual_density_cancellation {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (hG : G ≠ 0)
    (M K : ℝ) (hM : 0 ≤ M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) -
      maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M =
      (Real.sqrt M : ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K := by
  rw [summed_dual_density cols a G M K hM hcols,
    maskedSourceDensity_coprime_squarefree G hG K M hM cols a hcols hray hGc hbad,
    actualPrincipalDifference_densityColumn cols a G K
      (fun j => (hcols j).1) (fun j => (hGc j).symm)]
  change _ = (Real.sqrt M:ℂ)*(densityPairSum cols a
    (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) -
    primePoolDensity G*densityPairSum cols a (fun I J => normalizedPairCoprimePartial I J G K))
  ring

end CanonicalQuadraticSieve


end

end OAI

end


