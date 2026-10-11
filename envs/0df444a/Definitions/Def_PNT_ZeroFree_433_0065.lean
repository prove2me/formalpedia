-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0065
-- name    : PNT_ZeroFree_433_0065
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T16:38:14.03936+00:00
-- url     : https://prove2.me/theorems/772fcc2f-eba3-4e7e-8d57-ebb6d4918268
-- title:
--   Zero-free region foundations: QuadraticSieve.IdealQuotients [0065]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean#L415-L711

import Definitions.Def_PNT_ZeroFree_433_0065_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/IdealQuotients.lean
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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT


end

open ActualEisensteinCubic CompletedGauss


end CanonicalQuadraticSieve

section
open MeasureTheory
open scoped FourierTransform SchwartzMap ContDiff
namespace FourierBridge


end FourierBridge

namespace LocalLogFourier


end LocalLogFourier

namespace EisensteinSchwartzPoisson

theorem paperRadialFourier_log_separation_envelope
    {ι : Type*} [Fintype ι]
    (W : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hVwindow : ∀ j z, V j z ≠ 0 → |z| ≤ M j)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ y : ι → ℝ,
          (∏ j : ι, V j (y j)) *
            paperRadialFourier W (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, V j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) volume ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C ∧
        (∀ t : ℝ, (1 + R) ^ A * (1 + ‖t‖) ^ J * ‖b t‖ ≤ C) := by
  obtain ⟨CF, hCF, hEuler⟩ := paperRadialFourier_euler_bound W A
    (J + (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower)
  exact LocalLogFourier.coupled_positive_log_separation_envelope V (paperRadialFourier W)
    a M hM hVwindow (paperRadialFourier_contDiffOn W) A J CF hCF hEuler

end EisensteinSchwartzPoisson
end

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius supportRay supportIdealFamily supportIdealFamily_pos
  supportIdealFamily_good recoveredSupport)
open ConcretePrimeRowBridge (conjugateIdealRowSum)
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

def rayIdealRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  let P := fun i => Ideal.span {p i}
  conjugateIdealRowSum (supportIdealFamily P (F \ D))
    (supportIdealFamily_pos P (F \ D)) (supportIdealFamily_good P hg (F \ D))
    (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
      else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C (D ∪ recoveredSupport P (F \ D) I)) h

def rayPairWeight {ι : Type*} (p : ι → O)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  crossCoeff r.1 r.2 * (supportMobius (fun i => Ideal.span {p i}) D *
    rowCoprimeMask (fun i => Ideal.span {p i}) D h * supportRay p r.1 D * supportRay p r.2 D)

def rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (h : O) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ *
      ‖rayIdealRow p hg F C negative (if negative then r.1 else r.2) D h‖ ^ 2

theorem rayIdealEnergy_nonneg {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (h : O) :
    0 ≤ rayIdealEnergy p hg F C negative h := by
  unfold rayIdealEnergy
  positivity

theorem idealPairReindex_eq_ray_rows {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    idealPairReindex p hg F C₁ C₂ h =
    ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      rayPairWeight p r D h * rayIdealRow p hg F C₂ false r.2 D h *
        star (rayIdealRow p hg F C₁ true r.1 D h) := by
  simp only [idealPairReindex, rayPairWeight, rayIdealRow, Bool.false_eq_true,
    ite_false, ite_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact Finset.sum_congr rfl (fun D hD => by ring)

theorem idealPairReindex_norm_le {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    ‖idealPairReindex p hg F C₁ C₂ h‖ ≤
      Real.sqrt (rayIdealEnergy p hg F C₁ true h) *
        Real.sqrt (rayIdealEnergy p hg F C₂ false h) := by
  rw [idealPairReindex_eq_ray_rows]
  have hc := DescentWeightedCauchy.weighted_cauchy
    ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset)
    (fun z => rayPairWeight p z.1 z.2 h)
    (fun z => rayIdealRow p hg F C₂ false z.1.2 z.2 h)
    (fun z => rayIdealRow p hg F C₁ true z.1.1 z.2 h)
  simp only [Finset.sum_product] at hc
  change ‖∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      rayPairWeight p r D h * rayIdealRow p hg F C₂ false r.2 D h *
        star (rayIdealRow p hg F C₁ true r.1 D h)‖ ≤
    Real.sqrt (rayIdealEnergy p hg F C₂ false h) *
      Real.sqrt (rayIdealEnergy p hg F C₁ true h) at hc
  exact hc.trans_eq (mul_comm _ _)

theorem norm_rayPairWeight {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) :
    ‖rayPairWeight p r D h‖ = ‖crossCoeff r.1 r.2‖ *
      ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ := by
  have hmu : ‖supportMobius (fun i => Ideal.span {p i}) D‖ = 1 := by
    have hh := FirstCauchyArithmetic.supportMobius_sq (fun i => Ideal.span {p i})
      (fun i => Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance) hinj D
    have hh' := congrArg norm hh
    simp only [norm_mul, norm_one] at hh'
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) D)]
  have hr (χ : RayCharacter) : ‖supportRay p χ D‖ = 1 := by
    obtain ⟨u, hu⟩ := RayFourExpansion.prime_product_unit_mod_four p hc D
    change ‖χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i))‖ = 1
    rw [← hu]
    exact FiniteRayExpansion.norm_char_unit χ u
  simp only [rayPairWeight, norm_mul, hmu, hr, one_mul, mul_one]

def cubeLogCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : O) :
    Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistMinus C V y t) d
  else cubePlusCoefficient p hp hcop hg B v ε₁ ε₂ (logTwistPlus C V y t) d

theorem cubeLogCoefficient_continuous {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (d : O) (S : Finset ι) :
    Continuous (fun t : ℝ => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t d S) := by
  cases negative <;>
    simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true,
      cubeMinusCoefficient, cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus]
  all_goals
    have hp := FourierBridge.logPhase_continuous_left (-(y S))
    fun_prop

theorem norm_cubeLogCoefficient_eq_zero {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : O) (S : Finset ι) :
    ‖cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t d S‖ =
    ‖cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y 0 d S‖ := by
  cases negative <;>
    simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true,
      cubeMinusCoefficient, cubePlusCoefficient, FirstCauchyArithmetic.firstPassColumnMinus,
      FirstCauchyArithmetic.firstPassColumnPlus, logTwistMinus, logTwistPlus,
      norm_mul, norm_star, FourierBridge.logPhase_norm]

private theorem rayIdealRow_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    Continuous (fun t => rayIdealRow p hg F (C t) negative χ D h) := by
  simp only [rayIdealRow, ConcretePrimeRowBridge.conjugateIdealRowSum,
    ConcretePrimeRowBridge.mobiusIdealColumn]
  fun_prop

private theorem rayIdealRow_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖rayIdealRow p hg F (C t) negative χ D h‖ ≤ M := by
  let P := fun i => Ideal.span {p i}
  let s := supportIdealFamily P (F \ D)
  let T := fun (t : ℝ) (I : Ideal O) =>
    ConcretePrimeRowBridge.mobiusIdealColumn
      (fun I => (if negative then star (supportRay p χ (recoveredSupport P (F \ D) I))
        else supportRay p χ (recoveredSupport P (F \ D) I)) *
        C t (D ∪ recoveredSupport P (F \ D) I)) I *
      star (ConcretePrimeRowBridge.idealSexticRow s (supportIdealFamily_pos P (F \ D))
        (supportIdealFamily_good P hg (F \ D)) I h)
  refine ⟨∑ I ∈ s, ‖T 0 I‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), ?_⟩
  intro t
  change ‖∑ I ∈ s, T t I‖ ≤ _
  apply (norm_sum_le s (T t)).trans_eq
  apply Finset.sum_congr rfl
  intro I hI
  simp only [T, ConcretePrimeRowBridge.mobiusIdealColumn, norm_mul, hC]

private theorem rayIdealEnergy_continuous {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (h : O) :
    Continuous (fun t => rayIdealEnergy p hg F (C t) negative h) := by
  unfold rayIdealEnergy
  apply continuous_finsetSum _
  intro r hr
  apply continuous_finsetSum _
  intro D hD
  exact continuous_const.mul ((rayIdealRow_continuous p hg F C hC negative _ D h).norm.pow 2)

private theorem rayIdealEnergy_uniform_bound {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hC : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, rayIdealEnergy p hg F (C t) negative h ≤ M := by
  choose M hM hbound using fun (r : RayCharacter × RayCharacter) (D : Finset ι) =>
    rayIdealRow_uniform_bound p hg F C hC negative (if negative then r.1 else r.2) D h
  refine ⟨∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ * (M r D)^2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro D hD
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hbound r D t) 2)
    (norm_nonneg _)

private theorem integrable_rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (negative : Bool) (h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t : ℝ => ‖b t‖ * rayIdealEnergy p hg F (C t) negative h) volume := by
  obtain ⟨M, hM, hb⟩ := rayIdealEnergy_uniform_bound p hg F C hn negative h
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (rayIdealEnergy_continuous p hg F C hc negative h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (rayIdealEnergy_nonneg p hg F (C t) negative h)]
      exact hb t)

theorem cube_integral_norm_le_energy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F : Finset ι)
    (C₁ C₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => C₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => C₂ t S))
    (hn₁ : ∀ t S, ‖C₁ t S‖ = ‖C₁ 0 S‖)
    (hn₂ : ∀ t S, ‖C₂ t S‖ = ‖C₂ 0 S‖)
    (h : O) (b : 𝓢(ℝ, ℂ)) (a : ℂ) :
    ‖∫ t : ℝ, b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₁ t) true h) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * rayIdealEnergy p hg F (C₂ t) false h) := by
  let E₁ := fun t => rayIdealEnergy p hg F (C₁ t) true h
  let E₂ := fun t => rayIdealEnergy p hg F (C₂ t) false h
  let w := fun t : ℝ => ‖b t‖ * ‖a‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => rayIdealEnergy_nonneg p hg F (C₁ t) true h
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => rayIdealEnergy_nonneg p hg F (C₂ t) false h
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have i₁ : Integrable (fun t => w t * E₁ t) volume := by
    convert! (integrable_rayIdealEnergy p hg F C₁ hc₁ hn₁ true h b).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₁]
    ring
  have i₂ : Integrable (fun t => w t * E₂ t) volume := by
    convert! (integrable_rayIdealEnergy p hg F C₂ hc₂ hn₂ false h b).mul_const ‖a‖ using 1
    funext t
    dsimp only [w, E₂]
    ring
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f :=
    Real.continuous_sqrt.comp (((b.continuous.norm.mul_const ‖a‖).mul
      (rayIdealEnergy_continuous p hg F C₁ hc₁ true h)))
  have hg' : Continuous g :=
    Real.continuous_sqrt.comp (((b.continuous.norm.mul_const ‖a‖).mul
      (rayIdealEnergy_continuous p hg F C₂ hc₂ false h)))
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
  have hnorm : ‖∫ t : ℝ, b t * a * idealPairReindex p hg F (C₁ t) (C₂ t) h‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (idealPairReindex_norm_le p hg F (C₁ t) (C₂ t) h) (hw t))
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

end FirstPassCubeLabels

end

end OAI

end


