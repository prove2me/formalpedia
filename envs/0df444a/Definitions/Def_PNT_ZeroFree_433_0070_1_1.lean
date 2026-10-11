-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0070_1_1
-- name    : PNT_ZeroFree_433_0070_1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T21:10:04.5936+00:00
-- url     : https://prove2.me/theorems/97973a60-3887-4dc2-baab-d0f4239711ce
-- title:
--   Zero-free region foundations: CubicSieve.FirstPassage [0070_1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.FirstPassage
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean#L81-L180

import Definitions.Def_PNT_ZeroFree_433_0069

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/FirstPassage.lean
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

namespace FirstPassCubeLabels

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)

theorem firstColumnEnergy_eq_sum_integrals {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      ∫ t : ℝ, firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r
        (normalizedColumn p C) V (columnLog p X) c d f h b t := by
  have hi (r : RayCharacter × RayCharacter) (D : Finset ι) :=
    firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r
      (normalizedColumn p C) V (columnLog p X) c d f h b
  calc
    _ = ∫ t : ℝ, ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r
        (normalizedColumn p C) V (columnLog p X) c d f h b t := by
      unfold firstColumnEnergy
      rw [normalized_originalLabelColumn]
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [rayIdealEnergy, firstRayIntegrand, Finset.mul_sum, mul_assoc]
    _ = _ := by
      rw [integral_finsetSum _ (fun r hr => integrable_finsetSum _ (fun D hD => hi r D))]
      apply Finset.sum_congr rfl
      intro r hr
      exact integral_finsetSum _ (fun D hD => hi r D)

theorem first_column_energy_integral (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1))
          V X d x.2 (b x)) ≤
      (M * H * K * Y ^ deltaLoss) * ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
        ‖crossCoeff r.1 r.2‖ * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) (normalizedColumn p C) V (columnLog p X) c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := first_ray_energy_integral deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hv negative C V X c d s T w b J M H Y hM hH hY hs hmap hT hnorm hw hdom
  simp_rw [firstColumnEnergy_eq_sum_integrals p hp hinj hcop hg F B v ε₁ ε₂ hv,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D hD
  have h := hbound p hp hinj hcop hg hc F D B v ε₁ ε₂ hv negative r
    (normalizedColumn p C) V (columnLog p X) c d s T w b J M H Y
    hM hH hY hs hmap hT hnorm hw hdom
  simpa only [mul_assoc, Finset.mul_sum] using h

open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

def firstOutputEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖crossCoeff r.1 r.2‖ * ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) (normalizedColumn p C) V (columnLog p X) c d t z‖ ^ 2

theorem firstOutputEnergy_nonneg {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (c d : O) (J : ℕ) (T : Finset O) :
    0 ≤ firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ negative C V X c d J T := by
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro D hD
  apply mul_nonneg (norm_nonneg _)
  apply integral_nonneg
  intro t
  exact mul_nonneg (firstLogDensity_nonneg J t) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))


end


end FirstPassCubeLabels


end

end OAI

end


