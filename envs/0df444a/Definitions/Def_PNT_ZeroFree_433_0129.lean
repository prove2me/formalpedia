-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0129
-- name    : PNT_ZeroFree_433_0129
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:20:40.480161+00:00
-- url     : https://prove2.me/theorems/2655d4b0-66c4-47d1-b873-c085867de305
-- title:
--   Zero-free region foundations: QuadraticSieve.PoissonComparison [0129]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonComparison
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean#L77-L590

import Definitions.Def_PNT_ZeroFree_433_0124
import Definitions.Def_PNT_ZeroFree_433_0126
import Definitions.Def_PNT_ZeroFree_433_0127
import Definitions.Def_PNT_ZeroFree_433_0128
import Definitions.Def_PNT_ZeroFree_433_0129_parallel1
import Definitions.Def_PNT_ZeroFree_433_0129_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/PoissonComparison.lean
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

namespace CanonicalQuadraticSieve

section


section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson


def centeredMaskedSource {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ) (M K : ℝ) : ℂ :=
  maskedPrincipalSourceSum G (quadraticSquareProfile W)
    (fun I : coprimeSquarefreeRange G K => I.val) cols a M -
  paperRadialFourier (quadraticSquareProfile W) 0 *
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M


theorem maskedPoissonDifference_centered {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    (6:ℂ)*maskedPoissonDifference G W cols a M K =
      (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
      (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K +
      paperRadialFourier (quadraticSquareProfile W) 0 *
        ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K) := by
  rw [←actual_source_dual_density_cancellation cols a G hG M K hM.le hcols hray hGc hbad]
  unfold maskedPoissonDifference centeredRetainedDual centeredMaskedSource divisorTwist
  rw [maskedDualFamily_retained G hG cols a W M K hM hcols hray]
  simp only [quadraticSquareProfile_principal_equal]
  rw [finite_centering_identity]
  ring

theorem maskedPoissonDifference_norm_le {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G≠0) (W : 𝓢(ℝ,ℂ)) (cols : n → Ideal O) (a : n → ℂ)
    (M K : ℝ) (hM : 0<M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P∈fixedBadPrimes, P∣G) :
    ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
      (∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖) +
      6*‖maskedDualTailFamily G cols a W M K‖ + ‖centeredMaskedSource G W cols a M K‖ +
      ‖paperRadialFourier (quadraticSquareProfile W) 0‖ *
        ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ := by
  rw [maskedPoissonDifference_centered G hG W cols a M K hM hcols hray hGc hbad]
  have hs : ‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ ≤
      ∑ q∈idealDivisors G, ‖centeredRetainedDual W cols a M K q‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one q)
  calc
    _ ≤ (‖∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q‖ +
        ‖(6:ℂ)*maskedDualTailFamily G cols a W M K‖) + ‖centeredMaskedSource G W cols a M K‖ +
        ‖paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K)‖ := by
      have h1 := norm_add_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K - centeredMaskedSource G W cols a M K)
        (paperRadialFourier (quadraticSquareProfile W) 0 *
          ((Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K))
      have h2 := norm_sub_le
        ((∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q) +
          (6:ℂ)*maskedDualTailFamily G cols a W M K) (centeredMaskedSource G W cols a M K)
      have h3 := norm_add_le
        (∑ q∈idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*centeredRetainedDual W cols a M K q)
        ((6:ℂ)*maskedDualTailFamily G cols a W M K)
      linarith
    _ ≤ _ := by
      simp only [norm_mul]
      norm_num
      gcongr

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator


end

open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum EisensteinSchwartzPoisson
open IdealCoprimeSieveOperator


theorem HasSieveExponent.masked_poisson_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G → (∀P∈fixedBadPrimes,P∣G) →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 1≤M → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀j k, columnRay (cols j)=columnRay (cols k)) → (∀j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖(6:ℂ)*maskedPoissonDifference G W cols a M K‖ ≤
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W := by
  obtain ⟨sD,CD,hCD,hdual⟩ := centeredRetainedDual_sum_bound l
  obtain ⟨sS,CS,hCS,hsource⟩ := masked_source_principal_global l
  obtain ⟨sT,CT,hCT,htail⟩ := maskedDualTailFamily_bound A
  obtain ⟨CP,hCP,hprincipal⟩ := hexp.actual_principal_difference deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro n _ _ ε hε G hG hbad K N M T hK hN hM hT cols hc hcols hray hGc a W hW
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hcols0 : ∀j, Admissible (cols j) := fun j => (hcols j).1
  have hcolsu : ∀j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N :=
    fun j => ⟨(hcols j).1,(hcols j).2.2⟩
  have hd := hdual hexp hα deltaLoss hδ ε hε G hG.ne_zero K N M T hK hN hM0 hT cols hc hcols hray a W
  have hs := hsource hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM0 hT
    (coprimeSquarefreeRange G K)
    (fun I hI => mem_idealRange.mp (coprimeSquarefreeRange_subset_idealRange G hbad K hI))
    cols hc hcolsu hGc a (quadraticSquareProfile W)
    (by simpa only [quadraticSquareProfile_apply,zero_pow (by decide : 2≠0)] using hW)
  have ht := htail G cols a W M N K hG.ne_zero hc hM0 hN (by linarith)
    (fun j => ⟨(hcols j).1.1,(hcols j).2⟩)
  have hp := hprincipal cols hc M N K hM hN hK hcolsu hray
    (densityColumn cols a) G hG hbad ε hε
  have he := densityColumn_energy_le cols a (fun j => (hcols j).1.1)
  have hsupp := (supportConstant_pos ε hε).le
  have hp' : ‖(Real.sqrt M:ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K‖ ≤
      ((idealDivisors G).card:ℝ)^2*(supportConstant ε hε*N^ε)*CP*(K*N)^deltaLoss*
        (Real.sqrt (M/K)*N+Real.sqrt M*K^(α-1/2))*∑j, ‖a j‖^2 := by
    apply hp.trans
    gcongr
  have hmain := maskedPoissonDifference_norm_le G hG.ne_zero W cols a M K hM0 hcols0 hray hGc hbad
  apply hmain.trans
  change _ ≤ _+_+_+_
  have hs' : ‖centeredMaskedSource G W cols a M K‖ ≤
      (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant sS CS l hexp deltaLoss hδ ε hε G (2*K) N M T a
        (quadraticSquareProfile W) := hs
  exact add_le_add (add_le_add (add_le_add hd (mul_le_mul_of_nonneg_left ht (by norm_num))) hs')
    (mul_le_mul_of_nonneg_left hp' (norm_nonneg _))

end


end CanonicalQuadraticSieve


end

end OAI

end


