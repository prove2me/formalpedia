-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0073
-- name    : PNT_ZeroFree_433_0073
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:23:57.083269+00:00
-- url     : https://prove2.me/theorems/d3b975bb-0531-463a-b20c-e16f03e64380
-- title:
--   Zero-free region foundations: CubicSieve.SecondPoisson [0073]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/SecondPoisson.lean#L83-L622

import Definitions.Def_PNT_ZeroFree_433_0071

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/SecondPoisson.lean#L83-L622
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.SecondPoisson
section
namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

section

open scoped BigOperators Classical SchwartzMap ContDiff
section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (activeGaussRowFactor)

theorem masked_pair_second_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S T : Finset ι) (hd : Disjoint S T)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    let n := ∏ i : activeSupport T S, p i.val
    (∑' z : O, rowCoprimeMask (fun i => Ideal.span {p i}) M z *
      (star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg T z) *
        finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S z) *
      W (‖eisEmbedding z‖ ^ 2 / Y)) =
    ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, Ideal.span {p i}) : ℂ) /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
          ∑' k : O, paperRadialFourier W
            (Y * ‖eisEmbedding k‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)) *
              activeGaussRowFactor p hp hinj hg T S e k := by
  dsimp only
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let Q := activePrimes P T S
  let q : activeSupport T S → O := fun i => p i.val
  let hQ := activePrimes_pairwise_isCoprime P hinj T S
  let j := activeExponent T S
  let row := finiteSexticRow Q (fun i => hg i.val) j
  let n := ∏ i, q i
  have hr (z : O) : star (finiteSquarefreeRow P hg T z) * finiteSquarefreeRow P hg S z = row z := by
    rw [finiteSquarefreeRow_pair_activeSupport]
    simp [Finset.disjoint_iff_inter_eq_empty.mp hd.symm, rowCoprimeMask, row, Q, j]
  have h := canonical_masked_radial_poisson_collected P hinj M Q hQ
    (fun i => hg i.val) (fun i => hc i.val) j
    (activeExponent_ne_zero T S) (activeExponent_lt_six T S) W Y hY
  have hn : ‖eisEmbedding (finitePrimeModulus Q)‖ = ‖eisEmbedding n‖ :=
    GaussGeneratorTransport.finitePrimeModulus_norm_eq_product q
  dsimp only at h
  rw [hn] at h
  have ht := GaussGeneratorTransport.gauss_weighted_finite_radial_sum_transport
    q (fun i => hp i.val) hQ (fun i => hg i.val) j M.powerset
    (fun E => let e := primeSubsetGenerator P E
      (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
        (‖eisEmbedding e‖ ^ 2 : ℝ))
    (fun E t => let e := primeSubsetGenerator P E
      paperRadialFourier W (Y * t / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding n‖ ^ 2)))
  calc
    _ = ∑' z : O, rowCoprimeMask P M z * row z * W (‖eisEmbedding z‖ ^ 2 / Y) := by
      apply tsum_congr
      intro z
      rw [hr]
    _ = ((Y : ℂ) / (‖eisEmbedding n‖ : ℂ)) *
        (canonicalNormalizedGauss Q hQ (fun i => hg i.val) j *
          ∑ E ∈ M.powerset,
            ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row (primeSubsetGenerator P E) /
              (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 : ℝ)) *
            ∑' k : O, star (row k) * paperRadialFourier W
              (Y * ‖eisEmbedding k‖ ^ 2 /
                (‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2 * ‖eisEmbedding n‖ ^ 2))) := by
      rw [h]
      ring
    _ = _ := by
      rw [ht]
      simp only [Finset.mul_sum, ← tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      apply tsum_congr
      intro k
      dsimp only [activeGaussRowFactor]
      ring

end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open FirstPassCubeLabels (columnLog primeProductNorm firstDualScale normalizedColumn)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondGaussTerm (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O) (H₁ H₂ : Finset ι → ℂ)
    (S T : Finset ι) : ℂ :=
  star (supportMobius (fun i => Ideal.span {p i}) S *
    secondInputCoefficient p hg Ψ₁ (m * (e * r)) c d H₁ S) *
  (supportMobius (fun i => Ideal.span {p i}) T *
    secondInputCoefficient p hg Ψ₂ (m * (e * r)) c d H₂ T) *
    activeGaussRowFactor p hp hinj hg T S e k

def actualSecondKernel (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T)) *
    ((Y : ℂ) / (‖eisEmbedding (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
    paperRadialFourier W (Y * ‖eisEmbedding k‖ ^ 2 /
      (‖eisEmbedding e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T
    else 0

def secondLogTest (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) : ℂ :=
  (V (columnLog p X S) *
    (if negative then star (logPhase t (-(columnLog p X S))) else logPhase t (-(columnLog p X S)))) /
      (‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)

theorem secondGaussTerm_log_twist (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t : ℝ) (S T : Finset ι) :
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T =
    (logPhase t (-(columnLog p X₁ S)) * logPhase t (-(columnLog p X₂ T))) *
      (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
        secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) := by
  simp only [secondGaussTerm, secondInputCoefficient, secondLogTest, normalizedColumn,
    ite_true, Bool.false_eq_true, ite_false, star_mul, star_div₀, star_star,
    one_div, star_inv₀]
  ring

theorem actualSecondKernel_eq_integral
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, star (V₁ x) * V₂ y *
      paperRadialFourier W (firstDualScale p ∅ Y X₁ X₂ e k * Real.exp (-x-y)) =
      ∫ t : ℝ, (star (V₁ x) * logPhase t (-x)) * (V₂ y * logPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false)) volume ∧
    actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
  let G := fun (t : ℝ) (S T : Finset ι) => if Disjoint S T then b t *
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
      (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) S T else 0
  have hGi (S T : Finset ι) : Integrable (fun t => G t S T) volume := by
    by_cases hd : Disjoint S T
    · simp only [G, if_pos hd, secondGaussTerm_log_twist]
      convert! FirstPassCubeLabels.integrable_log_pair b (-(columnLog p X₁ S)) (-(columnLog p X₂ T))
        (star (V₁ (columnLog p X₁ S)) * V₂ (columnLog p X₂ T) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
            (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T) using 1
    · simp only [G, if_neg hd]
      exact integrable_zero _ _ _
  have hGs (t : ℝ) : (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) =
      b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k
        (secondLogTest p V₁ X₁ t true) (secondLogTest p V₂ X₂ t false) := by
    simp only [G, secondActualPair, secondGaussTerm, Finset.mul_sum, mul_ite, mul_zero]
  have hI : Integrable (fun t => ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, G t S T) volume :=
    integrable_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T))
  constructor
  · simpa only [hGs] using hI
  · rw [← integral_congr_ae (Filter.Eventually.of_forall hGs)]
    rw [integral_finsetSum _ (fun S _ => integrable_finsetSum _ (fun T _ => hGi S T)), Finset.mul_sum]
    unfold actualSecondKernel
    apply Finset.sum_congr rfl
    intro S hS
    rw [integral_finsetSum _ (fun T _ => hGi S T), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    by_cases hd : Disjoint S T
    · simp only [G, if_pos hd, secondGaussTerm_log_twist]
      have harg := FirstPassCubeLabels.actual_radial_argument p hp S T ∅ hd
        (Finset.disjoint_empty_right _) (Finset.disjoint_empty_right _) Y X₁ X₂ hX₁ hX₂ e k
      simp only [Finset.union_empty] at harg
      rw [← harg]
      have hn : secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k
          (normalizedColumn p (fun _ => 1)) (normalizedColumn p (fun _ => 1)) S T =
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
        simp only [secondGaussTerm, secondInputCoefficient, normalizedColumn, one_div,
          mul_one, star_mul, map_inv₀, Complex.star_def, Complex.conj_ofReal]
        ring
      rw [hn]
      rw [Finset.prod_union hd]
      simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
      have hh := congrArg (fun z : ℂ => (Y : ℂ) * z *
        ((‖eisEmbedding (∏ i ∈ S, p i)‖ : ℂ)⁻¹ * (‖eisEmbedding (∏ i ∈ T, p i)‖ : ℂ)⁻¹) *
          secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T)
        (hsep (columnLog p X₁ S) (columnLog p X₂ T))
      rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const] at hh
      convert! hh using 1
      · ring
      · rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        ring
    · simp [hd, G]

end

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

section
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildSum_continuous
    (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) :
    Continuous (fun t : ℝ => secondChildSum p hp hcop hg F V Ψ m r c d e k (H t)) := by
  unfold secondChildSum
  apply continuous_finsetSum
  intro N hN
  have hh := hc (V ∪ N)
  unfold secondChildColumn
  fun_prop

theorem secondChildSum_uniform_bound
    (F V : Finset ι) (Ψ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖secondChildSum p hp hcop hg F V Ψ m r c d e k (H t)‖ ≤ M := by
  refine ⟨∑ N ∈ (F \ V).powerset,
    ‖secondChildColumn p hp hcop hg Ψ (m * r) (c * e * ∏ i ∈ V, p i) (d * e * k)
      (fun U => H 0 (V ∪ U)) N‖, by positivity, ?_⟩
  intro t
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro N hN
  simp only [secondChildColumn, norm_mul, hn]
  exact le_rfl

theorem secondTotalEnergy_nonneg
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : Finset ι → ℂ) (negative : Bool) :
    0 ≤ secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H negative := by
  unfold secondTotalEnergy
  positivity

theorem secondTotalEnergy_continuous
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S)) (negative : Bool) :
    Continuous (fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) := by
  unfold secondTotalEnergy
  apply continuous_finsetSum
  intro z hz
  apply continuous_finsetSum
  intro V hV
  exact continuous_const.mul ((secondChildSum_continuous p hp hcop hg F V
    (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
    m r c d e (if negative then k else -k) H hc).norm.pow 2)

theorem secondTotalEnergy_uniform_bound
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative ≤ M := by
  choose M hM hbound using fun (z : SecondRayIndex) (V : Finset ι) =>
    secondChildSum_uniform_bound p hp hcop hg F V
      (if negative then secondRayMinus Ψ₁ z else secondRayPlus Ψ₂ z)
      m r c d e (if negative then k else -k) H hn
  refine ⟨∑ z : SecondRayIndex, ∑ V ∈ F.powerset,
    ‖secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ m r c d e k (z,V)‖ * (M z V)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro z hz
  apply Finset.sum_le_sum
  intro V hV
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (hbound z V t) 2) (norm_nonneg _)

theorem secondTotalEnergy_integrable
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => H t S))
    (hn : ∀ t S, ‖H t S‖ = ‖H 0 S‖) (negative : Bool) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative) volume := by
  obtain ⟨M, hM, hb⟩ := secondTotalEnergy_uniform_bound p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hn negative
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H hc negative).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H t) negative)]
      exact hb t)

theorem second_integral_norm_le_energy
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => H₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => H₂ t S))
    (hn₁ : ∀ t S, ‖H₁ t S‖ = ‖H₁ 0 S‖)
    (hn₂ : ∀ t S, ‖H₂ t S‖ = ‖H₂ 0 S‖) (b : 𝓢(ℝ, ℂ)) :
    ‖∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false) := by
  let E₁ := fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  let E₂ := fun t => secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  let w := fun t : ℝ => ‖b t‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₁ t) true
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => secondTotalEnergy_nonneg p hp hcop hg F Ψ₁ Ψ₂ m r c d e k (H₂ t) false
  have hw : ∀ t, 0 ≤ w t := fun t => norm_nonneg _
  have i₁ : Integrable (fun t => w t * E₁ t) volume :=
    secondTotalEnergy_integrable p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ hn₁ true b
  have i₂ : Integrable (fun t => w t * E₂ t) volume :=
    secondTotalEnergy_integrable p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ hn₂ false b
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₁ hc₁ true))
  have hg' : Continuous g := Real.continuous_sqrt.comp (b.continuous.norm.mul
    (secondTotalEnergy_continuous p hp hcop hg F Ψ₁ Ψ₂ m r c d e k H₂ hc₂ false))
  have hfsq (t : ℝ) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : ℝ) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : ℝ) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : ℝ, b t * secondActualPair p hp hg hinj F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (secondActualPair_norm_le p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ m r c d e k (H₁ t) (H₂ t)) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, w t * E₁ t) * Real.sqrt (∫ t : ℝ, w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (firstDualScale firstLogDensity primeProductNorm_pos)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogTest_continuous (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (S : Finset ι) :
    Continuous (fun t : ℝ => secondLogTest p V X t negative S) := by
  have h := FourierBridge.logPhase_continuous_left (-(FirstPassCubeLabels.columnLog p X S))
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem secondLogTest_norm (V : ℝ → ℂ) (X t : ℝ) (negative : Bool) (S : Finset ι) :
    ‖secondLogTest p V X t negative S‖ = ‖secondLogTest p V X 0 negative S‖ := by
  cases negative <;> simp only [secondLogTest, Bool.false_eq_true, ite_false, ite_true,
    norm_div, norm_mul, norm_star, FourierBridge.logPhase_norm]

def secondKernelEnergy (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V : ℝ → ℂ) (X : ℝ) (negative : Bool) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * secondTotalEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k
    (secondLogTest p V X t negative) negative

theorem actual_second_kernel_uniform_energy_envelope
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ x, V₂ x ≠ 0 → |x| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Y : ℝ, 0 < Y → ∀ e k : O, e ≠ 0 → k ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p ∅ Y X₁ X₂ e k) ^ A * ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ (Ψ₁ Ψ₂ : O →* ℂ) (m r c d : O),
          ‖actualSecondKernel p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y‖ ≤
            Y * Real.sqrt (secondKernelEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k V₁ X₁ true b) *
              Real.sqrt (secondKernelEnergy p hp hcop hg F Ψ₁ Ψ₂ m r c d e k V₂ X₂ false b) := by
  have hV₁' : ∀ x, star (V₁ x) ≠ 0 → |x| ≤ M₁ := by
    intro x hx
    exact hV₁ x (by intro h; simp [h] at hx)
  obtain ⟨K, hK, hs⟩ := FirstPassCubeLabels.two_variable_radial_envelope W (fun x => star (V₁ x)) V₂
    M₁ M₂ hM₁ hM₂ hV₁' hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro Y hY e k he hk
  have hR : 0 < firstDualScale p ∅ Y X₁ X₂ e k := by
    unfold firstDualScale
    exact div_pos (mul_pos hY (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hk)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro Ψ₁ Ψ₂ m r c d
  rw [(actualSecondKernel_eq_integral p hp hg hinj F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y
    hX₁ hX₂ b hsep).2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY]
  have hi := second_integral_norm_le_energy p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ m r c d e k
    (fun t => secondLogTest p V₁ X₁ t true) (fun t => secondLogTest p V₂ X₂ t false)
    (secondLogTest_continuous p V₁ X₁ true) (secondLogTest_continuous p V₂ X₂ false)
    (fun t S => secondLogTest_norm p V₁ X₁ t true S)
    (fun t S => secondLogTest_norm p V₂ X₂ t false S) b
  change Y * _ ≤ Y * Real.sqrt _ * Real.sqrt _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi hY.le

end

section

open scoped BigOperators Classical
open ActualEisensteinCubic
open SecondPassFiber (OldTuple newLabel newRow Valid)

theorem second_energy_selected_family {κ : Type*} [Fintype κ] (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (P : κ → Ideal O × O → ℂ) (sel : OldTuple → κ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (sel x) (newLabel x, newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : κ, ∑ z ∈ t, ‖P u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := SecondPassFiber.second_energy_pushforward ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale P sel hb0 hB hL hvalid hmap ht hnorm hw
  calc
    _ ≤ ∑ x ∈ s, ‖w x‖ * ∑ u : κ, ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.single_le_sum
        (s := Finset.univ) (a := sel x)
        (f := fun u : κ => ‖P u (newLabel x, newRow x)‖ ^ 2)
        (fun u _ => sq_nonneg _) (Finset.mem_univ (sel x))
    _ = ∑ u : κ, ∑ x ∈ s, ‖w x‖ * ‖P u (newLabel x, newRow x)‖ ^ 2 := by
      simp only [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ u : κ, B * C * (lengthScale * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P u z‖ ^ 2 := by
      exact Finset.sum_le_sum (fun u _ => hb s t b0 w (P u) B lengthScale hb0 hB hL hvalid hmap ht hnorm hw)
    _ = _ := by rw [Finset.mul_sum]

end

open scoped BigOperators Classical
open ActualEisensteinCubic
open ConcretePrimeRowBridge (idealGenerator span_idealGenerator)
open SecondPassFiber (OldTuple newLabel newRow Valid)

local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def tupleLabelElement (x : OldTuple) : O :=
  idealGenerator (x.core 0) * idealGenerator (x.core 1) * idealGenerator (x.core 2) * idealGenerator x.v

theorem tupleLabelElement_span (x : OldTuple) :
    Ideal.span {tupleLabelElement x} = newLabel x := by
  simp only [tupleLabelElement, newLabel, ← Ideal.span_singleton_mul_span_singleton, span_idealGenerator]

theorem exists_label_unit (f : O) (I : Ideal O) (hf : Ideal.span {f} = I) :
    ∃ u : Oˣ, f = (u : O) * idealGenerator I := by
  have hs : Ideal.span {idealGenerator I} = Ideal.span {f} := (span_idealGenerator I).trans hf.symm
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def tupleLabelUnit (x : OldTuple) : Oˣ :=
  Classical.choose (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

theorem tupleLabelUnit_spec (x : OldTuple) :
    tupleLabelElement x = (tupleLabelUnit x : O) * idealGenerator (newLabel x) :=
  Classical.choose_spec (exists_label_unit (tupleLabelElement x) (newLabel x) (tupleLabelElement_span x))

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (f y : O) : ℂ :=
  ∑ N ∈ F.powerset, secondChildColumn p hp hcop hg Ψ m f y H N

def idealChildRow (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (u : Oˣ) (z : Ideal O × O) : ℂ :=
  fixedChildRow p hp hcop hg F Ψ m H ((u : O) * idealGenerator z.1)
    (if negative then -z.2 else z.2)

theorem tuple_child_eq_unit_sector (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (x : OldTuple) :
    fixedChildRow p hp hcop hg F Ψ m H (tupleLabelElement x)
      (if negative then -newRow x else newRow x) =
    idealChildRow p hp hcop hg F Ψ m H negative (tupleLabelUnit x) (newLabel x, newRow x) := by
  rw [tupleLabelUnit_spec]
  rfl

theorem fixed_child_second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (B lengthScale : ℝ)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (negative : Bool),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ lengthScale →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ lengthScale) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ *
        ‖fixedChildRow p hp hcop hg F Ψ m H (tupleLabelElement x)
          (if negative then -newRow x else newRow x)‖ ^ 2) ≤
      B * C * (lengthScale * Ideal.absNorm b0) ^ ε *
        ∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := second_energy_selected_family (κ := Oˣ) ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w B lengthScale F Ψ m H negative hb0 hB hL hvalid hmap ht hnorm hw
  have hh := hb s t b0 w B lengthScale (idealChildRow p hp hcop hg F Ψ m H negative)
    tupleLabelUnit hb0 hB hL hvalid hmap ht hnorm hw
  simpa only [tuple_child_eq_unit_sector] using hh

theorem idealChildRow_unit_energy_le (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (negative : Bool) (t : Finset (Ideal O × O)) (E : ℝ)
    (hE : ∀ u : Oˣ, (∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ E) :
    (∑ u : Oˣ, ∑ z ∈ t, ‖idealChildRow p hp hcop hg F Ψ m H negative u z‖ ^ 2) ≤ 6 * E := by
  have hc : Fintype.card Oˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  calc
    _ ≤ ∑ u : Oˣ, E := Finset.sum_le_sum (fun u _ => hE u)
    _ = _ := by simp [hc]

end SecondPassArithmetic

end

end OAI

end


