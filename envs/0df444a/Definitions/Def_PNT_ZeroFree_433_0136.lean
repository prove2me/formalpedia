-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0136
-- name    : PNT_ZeroFree_433_0136
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T13:40:41.353995+00:00
-- url     : https://prove2.me/theorems/dc740569-8b7d-4751-a153-19bba9441a1d
-- title:
--   Zero-free region foundations: QuadraticSieve.AnnularLifting [0136]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularLifting
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean#L82-L653

import Definitions.Def_PNT_ZeroFree_433_0135
import Definitions.Def_PNT_ZeroFree_433_0136_parallel1
import Definitions.Def_PNT_ZeroFree_433_0136_parallel2

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/AnnularLifting.lean
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

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel


theorem annularLift_row_sum (M N K : ℝ) (I : squarefreeHighRange M K)
    (a : idealRange N → ℂ)
    (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑J : idealRange N, quadraticRow J.val (primaryGenerator (annularLift M K I))*a J) =
      ∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J := by
  apply Finset.sum_congr rfl
  intro J _
  by_cases hz : a J=0
  · simp only [hz,mul_zero]
  · rw [annularLift,liftedRow_character M I.val
      (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1 _ J.val
      (mem_idealRange.mp J.property).1 (hcop J hz)]


theorem squarefreeHigh_energy_le_annuli (M N K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K a := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hE (I : Ideal O) : 0≤E I := sq_nonneg _
  have hlift :
      (∑I : squarefreeHighRange M K, E I.val) = ∑I : squarefreeHighRange M K, E (annularLift M K I) := by
    apply Finset.sum_congr rfl
    intro I _
    dsimp only [E]
    rw [annularLift_row_sum M N K I a hcop]
  change (∑I : squarefreeHighRange M K, E I.val)≤_
  rw [hlift]
  have hpoint (I : squarefreeHighRange M K) : E (annularLift M K I) ≤
      ∑j : Fin 7, if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := by
    have hp := annularLift_properties M K I
    obtain ⟨j,hjlo,hjhi⟩ := exists_lifted_annular_scale M _ hM hp.2.2.1 hp.2.2.2
    have hMj : 0<(2:ℝ)^j.val*M := by positivity
    have hm : annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K :=
      mem_highKernelRange.mpr ⟨hp.1,by linarith,hp.2.1⟩
    have hw : annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)=1 := by
      apply QuadraticInitialBound.annularSieveBump_eq_one
      · exact (le_div_iff₀ hMj).mpr (by linarith)
      · exact (div_le_one hMj).mpr hjhi
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 7)))
      (f := fun j => if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0)
      (fun j _ => by split_ifs; exact mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE _); exact le_rfl)
      (Finset.mem_univ j)
    simpa only [hm,ite_true,hw,one_mul] using hh
  calc
    _ ≤ ∑I : squarefreeHighRange M K, ∑j : Fin 7,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ∑j : Fin 7, ∑I : squarefreeHighRange M K,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [annularHighEnergy,Finset.sum_coe_sort (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)]
      exact sum_injective_mask_le (annularLift M K) (annularLift_injective M K)
        (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)
        (fun I => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE I))

end


section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator


theorem ballQuadraticEnergy_lifted_annuli (M N K : ℝ) (hM : 0<M) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      2*((∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingFreeCoefficient N a)) +
        ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingDividedCoefficient N a)) := by
  have hlo := ballQuadraticEnergy_low_high M N K a
  have hs : (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      2*((∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2) +
        ∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) := by
    calc
      _ ≤ ∑I : squarefreeHighRange M K, 2*(
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2 +
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) :=
        Finset.sum_le_sum (fun I _ => liftingCoefficient_row_energy N a (primaryGenerator I.val))
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have hfree := squarefreeHigh_energy_le_annuli M N K hM (liftingFreeCoefficient N a)
    (liftingFreeCoefficient_coprime N a)
  have hdiv := squarefreeHigh_energy_le_annuli M N K hM (liftingDividedCoefficient N a)
    (liftingDividedCoefficient_coprime N a)
  linarith

end

open ActualEisensteinCubic CompletedGauss


end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy


theorem HasSieveExponent.annular_energy_from_scalar_cost {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧ 0<CH ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N K T H C : ℝ),
      1≤M → 1≤N → 1≤K → 4≤T → 0<H → H≤N/2 → 0≤C →
      (∀D∈gcdPool (fun J : idealRange N => J.val), (Ideal.absNorm D:ℝ)≤H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (commonMaskIdeal D) K (N/(Ideal.absNorm D:ℝ)) M T
          (fun _ : Unit => (1:ℂ)) QuadraticInitialBound.annularSieveCutoff≤C) →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤
        16*((C/6)*(divisorConstant ε hε*N^ε) +
          (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
            (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑J,‖a J‖^2 := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hsmall⟩ :=
    hexp.annular_small_gcd_complete hα deltaLoss hδ l A
  obtain ⟨CH,hCH,hhigh⟩ := hexp.high_kernel deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,?_⟩
  intro ε hε M N K T H C hM hN hK hT hH hHN hC hcost a ha
  classical
  let S := (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H)
  have hb (D : Ideal O) (hD : D∈S) (c : EisensteinEPrimaryPhase.Coord) :
      ‖annularRayGcdBlock M N K D c a‖ ≤
        (C/6)*∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 := by
    have hd := Finset.mem_filter.mp hD
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hd.1
    have hh := hsmall ε hε M N N K T hM hK hT a ha D hadm.1 (hd.2.trans hHN) c
    rw [poissonComparisonMajorant_energy_factor] at hh
    have hbound := mul_le_mul_of_nonneg_right (hcost D hd.1 hd.2)
      (show 0≤∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 by positivity)
    change _ ≤ C*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hbound
    have hn : ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖=6*‖annularRayGcdBlock M N K D c a‖ := by
      rw [norm_mul]
      norm_num
    rw [hn] at hh
    change _≤_*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hh
    nlinarith
  have hs := gcdRaySupport_weighted_sum_bound ε hε S (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) a N (C/6) (by positivity)
    (fun J hJ => (mem_idealRange.mp J.property).2)
    (fun D c => ‖annularRayGcdBlock M N K D c a‖) hb
  have hNH : 1≤N/H := (le_div_iff₀ hH).mpr (by linarith)
  have hh := hhigh (2*M) (N/H) K (by linarith) hNH hK
  have hred := annularHighEnergy_gcd_reduction M N K H hN hH ε hε a
  apply hred.trans
  have hsupp := (supportConstant_pos ε hε).le
  have hdiv := (divisorConstant_pos ε hε).le
  calc
    _ ≤ 16*((C/6)*(divisorConstant ε hε*N^ε)*∑J,‖a J‖^2 +
      (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
        (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
      gcongr
    _ = _ := by ring

end


end CanonicalQuadraticSieve

end

end OAI

end


