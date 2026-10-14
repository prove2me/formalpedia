-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0104
-- name    : PNT_ZeroFree_433_0104
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T11:49:32.39293+00:00
-- url     : https://prove2.me/theorems/96dded25-586c-466c-9557-b886858f59d9
-- title:
--   Zero-free region foundations: QuadraticSieve.SpatialDerivatives [0104]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.QuadraticSieve.SpatialDerivatives
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/SpatialDerivatives.lean#L77-L678

import Definitions.Def_PNT_ZeroFree_433_0102

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/QuadraticSieve/SpatialDerivatives.lean#L77-L678
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.QuadraticSieve.SpatialDerivatives
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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

theorem column_sqrt_ratio_bounds (N n : ℝ) (hN : 0 < N) (hn : N / 2 ≤ n ∧ n ≤ N) :
    1 / 4 ≤ Real.sqrt (n / N) ∧ Real.sqrt (n / N) ≤ 2 := by
  have hq0 : 0 ≤ n / N := div_nonneg (by linarith) hN.le
  have hq1 : (1 / 2 : ℝ) ≤ n / N := (le_div_iff₀ hN).mpr (by linarith)
  have hq2 : n / N ≤ 1 := (div_le_one hN).mpr hn.2
  have hs := Real.sq_sqrt hq0
  have hp := Real.sqrt_nonneg (n / N)
  constructor <;> nlinarith

theorem dual_middle_sqrt_identity (M B b N i j F : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : 0 < b) (hN : 0 < N)
    (hi : 0 < i) (hj : 0 < j) (hF : 0 < F) :
    N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N) =
      Real.sqrt (F * i * j / (M * b)) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, Real.sq_sqrt (show 0 ≤ F / (M * B) by positivity),
    Real.sq_sqrt (show 0 ≤ B / b by positivity), Real.sq_sqrt (show 0 ≤ i / N by positivity),
    Real.sq_sqrt (show 0 ≤ j / N by positivity), Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity)]
  field_simp

theorem dual_middle_argument (M B b N i j F D₁ d D₂ e q : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b ∧ b ≤ B) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) (hF : 0 < F)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d ∧ d ≤ 2 * D₁)
    (hD₂ : 0 < D₂) (he : D₂ ≤ e ∧ e ≤ 2 * D₂) :
    (N * Real.sqrt (F / (M * B)) * q / (D₁ * D₂)) *
      Real.exp (Real.log (middleRatio B b D₁ d D₂ e) +
        (Real.log (Real.sqrt (i / N)) + Real.log (Real.sqrt (j / N)))) =
      Real.sqrt (F * i * j / (M * b)) * q / (d * e) := by
  have hb0 : 0 < b := by linarith
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd.1
  have he0 : 0 < e := hD₂.trans_le he.1
  have hr : 0 < middleRatio B b D₁ d D₂ e := by
    have hh := middleRatio_bounds B b D₁ d D₂ e hB hb hD₁ hd hD₂ he
    linarith
  rw [Real.exp_add, Real.exp_add, Real.exp_log hr,
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hi0 hN)),
    Real.exp_log (Real.sqrt_pos.mpr (div_pos hj0 hN))]
  unfold middleRatio
  calc
    _ = (N * Real.sqrt (F / (M * B)) * Real.sqrt (B / b) * Real.sqrt (i / N) * Real.sqrt (j / N)) * q / (d * e) := by
      field_simp

    _ = _ := by rw [dual_middle_sqrt_identity M B b N i j F hM hB hb0 hN hi0 hj0 hF]

theorem actual_dual_middle_radial_block_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
        [DecidableEq m] [DecidableEq n] [DecidableEq p]
        (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
        (D₁ D₂ B N M F : ℝ) (_hD₁ : 1 ≤ D₁) (_hD₂ : 1 ≤ D₂) (_hB : 1 ≤ B) (_hN : 1 ≤ N)
        (_hM : 0 < M) (_hF : 0 < F)
        (_hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
        (_hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
        (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
        (_hr : Function.Injective rows) (_hl : Function.Injective left) (_hri : Function.Injective right)
        (_hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
        (_hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
        (_hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
        (a : n → ℂ) (b : p → ℂ) (h : O), h ≠ 0 →
        (1 + N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)) ^ A *
          (∑ D : S, ∑ E : T, ∑ i, ‖∑ j, ∑ k,
            originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
              (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
                (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
                  ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
          C * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  obtain ⟨C, hC, hb⟩ := canonical_original_radial_divisor_block_bound W 4 4 4 (by norm_num) (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n p _ _ _ _ _ _ ε hε S T D₁ D₂ B N M F hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have hB0 : 0 < B := by linarith
  have hN0 : 0 < N := by linarith
  let R := N * Real.sqrt (F / (M * B)) * ‖eisEmbedding h‖ ^ 2 / (D₁ * D₂)
  have hR : 0 < R := div_pos (mul_pos (mul_pos hN0 (Real.sqrt_pos.mpr (by positivity)))
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)))) (mul_pos hD₁0 hD₂0)
  let x : S → T → m → ℝ := fun D E i => Real.log
    (middleRatio B (Ideal.absNorm (rows i)) D₁ (Ideal.absNorm D.val) D₂ (Ideal.absNorm E.val))
  let y : n → ℝ := fun j => Real.log (Real.sqrt ((Ideal.absNorm (left j) : ℝ) / N))
  let z : p → ℝ := fun k => Real.log (Real.sqrt ((Ideal.absNorm (right k) : ℝ) / N))
  have hx (D : S) (E : T) (i : m) : |x D E i| ≤ 4 :=
    middleRatio_log_bound _ (middleRatio_bounds _ _ _ _ _ _ hB0 (hrows i).2 hD₁0
      (hS D.val D.property) hD₂0 (hT E.val E.property))
  have hy (j : n) : |y j| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hleft j).2)
  have hz (k : p) : |z k| ≤ 4 := middleRatio_log_bound _ (column_sqrt_ratio_bounds N _ hN0 (hright k).2)
  have he := hb R hR ε hε S T D₁ D₂ B N hD₁ hD₂ hN hS hT rows left right hr hl hri
    (fun i => ⟨(hrows i).1, (hrows i).2.2⟩) (fun j => ⟨(hleft j).1, (hleft j).2.2⟩)
    (fun k => ⟨(hright k).1, (hright k).2.2⟩) a b x y z hx hy hz
  have harg (D : S) (E : T) (i : m) (j : n) (k : p) : R * Real.exp (x D E i + (y j + z k)) =
      Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
        (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)) :=
    dual_middle_argument _ _ _ _ _ _ _ _ _ _ _ _ hM hB0 (hrows i).2 hN0 (hleft j).2 (hright k).2 hF
      hD₁0 (hS D.val D.property) hD₂0 (hT E.val E.property)
  simpa only [harg, R] using he

theorem principal_middle_prefactor_bound (M B b D₁ d D₂ e : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hb : B / 2 ≤ b)
    (hD₁ : 0 < D₁) (hd : D₁ ≤ d) (hD₂ : 0 < D₂) (he : D₂ ≤ e) :
    Real.sqrt (M / b) / (d * e) ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := hD₁.trans_le hd
  have he0 : 0 < e := hD₂.trans_le he
  have hq : M / b ≤ 4 * (M / B) := by
    calc
      _ ≤ (4 * M) / B := (div_le_div_iff₀ hb0 hB).mpr (by nlinarith [mul_nonneg hM.le (show 0 ≤ 4 * b - B by linarith)])
      _ = _ := by ring
  have hs : Real.sqrt (M / b) ≤ 2 * Real.sqrt (M / B) := by
    have hh := Real.sqrt_le_sqrt hq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    have hs4 : Real.sqrt (4 : ℝ) = 2 := by
      simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)
    rw [hs4] at hh
    exact hh
  calc
    _ ≤ (2 * Real.sqrt (M / B)) / (d * e) := div_le_div_of_nonneg_right hs (mul_pos hd0 he0).le
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (mul_pos hD₁ hD₂)
      (mul_le_mul hd he hD₂.le hd0.le)

theorem principal_middle_prefactor_sum {m : Type*} [Fintype m]
    (S T : Finset (Ideal O)) (rows : m → Ideal O) (f : S → T → m → ℝ)
    (hf : ∀ D E i, 0 ≤ f D E i) (M B D₁ D₂ : ℝ)
    (hM : 0 < M) (hB : 0 < B) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hrows : ∀ i, B / 2 ≤ (Ideal.absNorm (rows i) : ℝ))
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ)) (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ)) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) * f D E i) ≤
      (2 * Real.sqrt (M / B) / (D₁ * D₂)) * ∑ D : S, ∑ E : T, ∑ i, f D E i := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (hf D E i)
  exact principal_middle_prefactor_bound M B _ D₁ _ D₂ _ hM hB (hrows i) hD₁
    (hS D.val D.property) hD₂ (hT E.val E.property)

def originalMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose

def dualMiddleConstant (W : 𝓢(ℝ, ℂ)) : ℝ := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose

theorem dual_principal_prefactor_identity (M F b i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hi : 0 < i) (hj : 0 < j) :
    (M / (Real.sqrt (i * j) * F)) * Real.sqrt (F * i * j / (M * b)) =
      Real.sqrt ((M / F) / b) := by
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  simp only [mul_pow, div_pow, Real.sq_sqrt (show 0 ≤ i * j by positivity),
    Real.sq_sqrt (show 0 ≤ F * i * j / (M * b) by positivity),
    Real.sq_sqrt (show 0 ≤ (M / F) / b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
  (D₁ D₂ B N M : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M)
  (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D : ℝ) ∧ (Ideal.absNorm D : ℝ) ≤ 2 * D₁)
  (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E : ℝ) ∧ (Ideal.absNorm E : ℝ) ≤ 2 * D₂)
  (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
  (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
  (hrows : ∀ i, Admissible (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
  (a : n → ℂ) (b : p → ℂ) (h : O) (hh : h ≠ 0)

include hD₁ hD₂ hB hN hM hS hT hr hl hri hrows hh

theorem actual_original_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ))
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) * ‖eisEmbedding h‖ ^ 2 /
          ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt (M / B) / (D₁ * D₂)) * originalMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hk := (actual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M
    hD₁ hD₂ hB hN hM hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ originalMiddleConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T rows _ (fun _ _ _ => norm_nonneg _) M B D₁ D₂ hM
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).2.1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt (M / B) / (D₁ * D₂) by positivity)

theorem actual_dual_middle_weighted_bound
    (W : 𝓢(ℝ, ℂ)) (F : ℝ) (hF : 0 < F)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N) :
    (∑ D : S, ∑ E : T, ∑ i,
      (Real.sqrt ((M / F) / (Ideal.absNorm (rows i) : ℝ)) /
        ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ))) *
      ‖∑ j, ∑ k, originalTerm rows left right a b D.val E.val i j k * paperRadialFourier W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))) * ‖eisEmbedding h‖ ^ 2 /
            ((Ideal.absNorm D.val : ℝ) * (Ideal.absNorm E.val : ℝ)))‖) ≤
    (2 * Real.sqrt ((M / F) / B) / (D₁ * D₂)) * dualMiddleConstant W *
      Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) := by
  have hk := (actual_dual_middle_radial_block_bound.{0, 0, 0} W 0).choose_spec.2 ε hε S T D₁ D₂ B N M F
    hD₁ hD₂ hB hN hM hF hS hT rows left right hr hl hri hrows hleft hright a b h hh
  change _ ≤ dualMiddleConstant W * Real.sqrt (divisorBlockCost ε hε D₁ D₂ B N a b) at hk
  simp only [pow_zero, one_mul] at hk
  apply (principal_middle_prefactor_sum S T rows _ (fun _ _ _ => norm_nonneg _) (M / F) B D₁ D₂ (div_pos hM hF)
    (by linarith) (by linarith) (by linarith) (fun i => (hrows i).2.1)
    (fun D hD => (hS D hD).1) (fun E hE => (hT E hE).1)).trans
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hk (show 0 ≤ 2 * Real.sqrt ((M / F) / B) / (D₁ * D₂) by positivity)

end CanonicalQuadraticSieve

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma abs_le_inv_of_mul_sq_le_one {v t : ℝ} (hv : 0<v) (h : v^2*t^2≤1) :
    |t|≤1/v := by
  apply (le_div_iff₀ hv).mpr
  have he : |v*t|≤1 := (sq_le_one_iff_abs_le_one _).mp (by simpa only [mul_pow] using h)
  simpa only [abs_mul,abs_of_pos hv,mul_comm] using he

lemma heightLog_first_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : 0<v)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    |heightLogDx A B C D x y v|≤1/v ∧
    |heightLogDy A B C D x y v|≤1/v ∧
    |heightLogDv A B C D x y v|≤1/v := by
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  exact ⟨abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith),
    abs_le_inv_of_mul_sq_le_one hv (by nlinarith)⟩

lemma heightLog_second_bounds (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C^2) (hv : 0<v)
    (hA : 0≤A) (hq : 0<quadraticHeightDenominator A B C D x y v)
    (hAv : A*v^2≤quadraticHeightDenominator A B C D x y v) :
    |heightLogDxx A B C D x y v|≤7/v^2 ∧
    |heightLogDyy A B C D x y v|≤7/v^2 ∧
    |heightLogDvv A B C D x y v|≤7/v^2 := by
  let q := quadraticHeightDenominator A B C D x y v
  let r := v^2*A/q
  have hr0 : 0≤r := div_nonneg (mul_nonneg (sq_nonneg v) hA) hq.le
  have hr1 : r≤1 := (div_le_one hq).mpr (by simpa only [mul_comm] using hAv)
  have he := heightLog_eikonal A B C D x y v hrel hv.ne' hq.ne'
  have hx := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDx A B C D x y v))
  have hy := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDy A B C D x y v))
  have hz := mul_nonneg (sq_nonneg v) (sq_nonneg (heightLogDv A B C D x y v))
  have hx1 : v^2*(heightLogDx A B C D x y v)^2≤1 := by nlinarith
  have hy1 : v^2*(heightLogDy A B C D x y v)^2≤1 := by nlinarith
  have hxx : v^2*heightLogDxx A B C D x y v =
      v^2*(heightLogDx A B C D x y v)^2-2*r := by
    dsimp [heightLogDxx,heightLogDx,r,q]
    field_simp
    ; ring
  have hyy : v^2*heightLogDyy A B C D x y v =
      v^2*(heightLogDy A B C D x y v)^2-2*r := by
    dsimp [heightLogDyy,heightLogDy,r,q]
    field_simp
    ; ring
  have hvv : v^2*heightLogDvv A B C D x y v = -1-2*r+4*r^2 := by
    dsimp [heightLogDvv,r,q]
    field_simp [hv.ne',hq.ne']
    ; ring
  have hconv (a : ℝ) (ha : |v^2*a|≤7) : |a|≤7/v^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hv)).mpr
    simpa only [abs_mul,abs_of_nonneg (sq_nonneg v),mul_comm] using ha
  refine ⟨hconv _ (abs_le.mpr ⟨?_,?_⟩), hconv _ (abs_le.mpr ⟨?_,?_⟩),
    hconv _ (abs_le.mpr ⟨?_,?_⟩)⟩
  all_goals nlinarith [sq_nonneg r,mul_nonneg hr0 (sub_nonneg.mpr hr1)]

lemma actual_quadraticHeight_nonneg (u : Fin 2 → ℂ) (x y v : ℝ) :
    Complex.normSq (u 0)*v^2 ≤
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [← heightDenominator_eq_quadratic]
  unfold heightDenominator
  rw [Complex.normSq_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

open Filter
open scoped BigOperators Classical Topology Matrix

abbrev SpatialCoordinates := Fin 3 → ℝ

def axisSlice (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ → ℂ :=
  fun t => f (Function.update p j t)

def spatialLogD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDx A B C D (p 0) (p 1) (p 2),
    heightLogDy A B C D (p 0) (p 1) (p 2),
    heightLogDv A B C D (p 0) (p 1) (p 2)]
def spatialLogDD (A B C D : ℝ) (p : SpatialCoordinates) : Fin 3 → ℝ :=
  ![heightLogDxx A B C D (p 0) (p 1) (p 2),
    heightLogDyy A B C D (p 0) (p 1) (p 2),
    heightLogDvv A B C D (p 0) (p 1) (p 2)]

lemma spatial_axis_hasDerivAt (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j)
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*s*(spatialLogD A B C D p j:ℂ)) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 0) (p 2))
      (quadraticHeightDenominator_hasDerivAt_x A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDx] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_const (p 1) (p 2))
      (quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDy] using h
  · have h := hasDerivAt_logRatioPower s (hasDerivAt_id (p 2))
      (quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) (p 2)) hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,heightLogDv] using h

lemma spatial_axis_hasDerivAt_deriv (s : ℂ) (A B C D : ℝ) (p : SpatialCoordinates) (j : Fin 3)
    (hv : p 2≠0) (hq : quadraticHeightDenominator A B C D (p 0) (p 1) (p 2)≠0) :
    HasDerivAt (deriv (axisSlice (fun q => spatialHeightPower s A B C D (q 0) (q 1) (q 2)) p j))
      (spatialHeightPower s A B C D (p 0) (p 1) (p 2)*
        (s^2*(spatialLogD A B C D p j:ℂ)^2+s*(spatialLogDD A B C D p j:ℂ))) (p j) := by
  unfold axisSlice
  fin_cases j
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D t (p 1) (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+B)) (p 0) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t (p 1) (p 2))
      (hasDerivAt_const (p 0) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 0)).const_mul A |>.add_const B).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDx,heightLogDxx] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun _ => p 2)
      (fun t => quadraticHeightDenominator A B C D (p 0) t (p 2)) (fun _ => 0)
      (fun t => 2*(A*t+C)) (p 1) 0 (2*A)
      (fun t => hasDerivAt_const t (p 2))
      (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D (p 0) t (p 2))
      (hasDerivAt_const (p 1) 0)
      (by simpa only [id_eq,mul_one] using ((hasDerivAt_id (p 1)).const_mul A |>.add_const C).const_mul 2)
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDy,heightLogDyy] using h
  · have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
      (fun t => quadraticHeightDenominator A B C D (p 0) (p 1) t) (fun _ => 1)
      (fun t => 2*A*t) (p 2) 0 (2*A)
      (fun t => hasDerivAt_id t)
      (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D (p 0) (p 1) t)
      (hasDerivAt_const (p 2) 1)
      (by simpa only [id_eq,mul_one] using (hasDerivAt_id (p 2)).const_mul (2*A))
      hv hq
    simpa [axisSlice,Function.update,spatialHeightPower,spatialLogD,spatialLogDD,heightLogDv,heightLogDvv,div_eq_mul_inv] using h

def rowSmoothPower (s : ℂ) (u : Fin 2 → ℂ) (p : SpatialCoordinates) : ℂ :=
  spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2)

def rowLogD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

def rowLogDD (u : Fin 2 → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ :=
  spatialLogDD (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
    (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) p j

lemma row_denominator_pos (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) :
    0 < quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
      (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) (p 0) (p 1) (p 2) := by
  rw [← heightDenominator_eq_quadratic]
  exact heightDenominator_pos _ _ hv u hu

lemma rowLogD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogD u p j| ≤ 1/(p 2) := by
  have h := heightLog_first_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (row_denominator_pos u hu p hv).ne'
  fin_cases j <;> simp only [rowLogD,spatialLogD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma rowLogDD_bound (u : Fin 2 → ℂ) (hu : u≠0) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    |rowLogDD u p j| ≤ 7/(p 2)^2 := by
  have h := heightLog_second_bounds _ _ _ _ (p 0) (p 1) (p 2)
    (complex_row_quadratic_relation (u 0) (u 1)) hv (Complex.normSq_nonneg _)
    (row_denominator_pos u hu p hv) (actual_quadraticHeight_nonneg u (p 0) (p 1) (p 2))
  fin_cases j <;> simp only [rowLogDD,spatialLogDD,]
  · exact h.1
  · exact h.2.1
  · exact h.2.2

lemma row_axis_hasDerivAt (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (axisSlice (rowSmoothPower s u) p j)
      (rowSmoothPower s u p*s*(rowLogD u p j:ℂ)) (p j) :=
  spatial_axis_hasDerivAt _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

lemma row_axis_hasDerivAt_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    HasDerivAt (deriv (axisSlice (rowSmoothPower s u) p j))
      (rowSmoothPower s u p*(s^2*(rowLogD u p j:ℂ)^2+s*(rowLogDD u p j:ℂ))) (p j) :=
  spatial_axis_hasDerivAt_deriv _ _ _ _ _ p j hv.ne' (row_denominator_pos u hu p hv).ne'

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

lemma hasDerivAt_deriv_tsum_of_bounds {ι : Type*} (f : ι → ℝ → ℂ)
    (M₁ M₂ : ι → ℝ) (U : Set ℝ) (x : ℝ)
    (hU : IsOpen U) (hUc : IsPreconnected U) (hx : x ∈ U)
    (hM₁ : Summable M₁) (hM₂ : Summable M₂)
    (hfirst : ∀i y, y∈U → DifferentiableAt ℝ (f i) y)
    (hsecond : ∀i y, y∈U → DifferentiableAt ℝ (deriv (f i)) y)
    (hbound₁ : ∀i y, y∈U → ‖deriv (f i) y‖≤M₁ i)
    (hbound₂ : ∀i y, y∈U → ‖deriv (deriv (f i)) y‖≤M₂ i)
    (hsum : Summable (fun i => f i x)) :
    HasDerivAt (deriv (fun y => ∑'i,f i y)) (∑'i,deriv (deriv (f i)) x) x := by
  have hfirstSum (y : ℝ) (hy : y∈U) :=
    hasDerivAt_tsum_of_isPreconnected hM₁ hU hUc
      (fun i z hz => (hfirst i z hz).hasDerivAt) hbound₁ hx hsum hy
  have hsumFirst : Summable (fun i => deriv (f i) x) :=
    Summable.of_norm_bounded hM₁ (fun i => hbound₁ i x hx)
  have hsecondSum := hasDerivAt_tsum_of_isPreconnected hM₂ hU hUc
    (fun i z hz => (hsecond i z hz).hasDerivAt) hbound₂ hx hsumFirst hx
  apply hsecondSum.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (hfirstSum y hy).deriv

lemma norm_row_axis_deriv (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (rowSmoothPower s u) p j) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖ * (1/(p 2))) := by
  rw [(row_axis_hasDerivAt s u hu p hv j).deriv,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ ‖rowSmoothPower s u p‖*‖s‖*(1/(p 2)) :=
      mul_le_mul_of_nonneg_left (rowLogD_bound u hu p hv j) (by positivity)
    _ = _ := by ring

lemma norm_row_axis_deriv2 (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (rowSmoothPower s u) p j)) (p j)‖ ≤
      ‖rowSmoothPower s u p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  rw [(row_axis_hasDerivAt_deriv s u hu p hv j).deriv,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ ‖s^2*(rowLogD u p j:ℂ)^2‖+‖s*(rowLogDD u p j:ℂ)‖ := norm_add_le _ _
    _ = ‖s‖^2*|rowLogD u p j|^2 + ‖s‖*|rowLogDD u p j| := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ _ := by
      have hfirst := rowLogD_bound u hu p hv j
      have hsecond := rowLogDD_bound u hu p hv j
      gcongr

def smoothSummand (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) : ℂ :=
  (cosetCharacter r)⁻¹ * rowSmoothPower s (embeddedRow r) p

lemma smoothSummand_eq_actual (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates) (hv : 0<p 2) :
    smoothSummand s r p =
      summand (upperSection ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hv) s r := by
  rw [smoothSummand,← eigenfunction_summand_eq_actual_series]
  congr 1
  exact (actualHeightPower_eq_spatial s (embeddedRow r) (embeddedRow_ne_zero r)
    (p 0) (p 1) (p 2) hv).symm

lemma smooth_axis_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) (p j) :=
  ((row_axis_hasDerivAt s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma smooth_axis_deriv_differentiable (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) (p j) := by
  change DifferentiableAt ℝ (deriv (fun t => (cosetCharacter r)⁻¹ *
    axisSlice (rowSmoothPower s (embeddedRow r)) p j t)) (p j)
  rw [deriv_const_mul_field']
  exact ((row_axis_hasDerivAt_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j).const_mul _).differentiableAt

lemma norm_smooth_axis_deriv (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (axisSlice (smoothSummand s r) p j) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖ * (1/(p 2))) := by
  have h := norm_row_axis_deriv s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma norm_smooth_axis_deriv2 (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) (p j)‖ ≤
      ‖smoothSummand s r p‖ * (‖s‖^2 * (1/(p 2))^2 + ‖s‖ * (7/(p 2)^2)) := by
  have h := norm_row_axis_deriv2 s (embeddedRow r) (embeddedRow_ne_zero r) p hv j
  unfold axisSlice at h ⊢
  simpa only [smoothSummand,deriv_const_mul_field',deriv_const_mul_field,norm_mul,norm_inv,
    norm_cosetCharacter,inv_one,one_mul] using h

lemma smoothSummand_axis_update (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (j : Fin 3) (t : ℝ) :
    axisSlice (smoothSummand s r) (Function.update p j t) j =
      axisSlice (smoothSummand s r) p j := by
  funext z
  simp only [axisSlice,Function.update_idem]

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

def clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) (p : SpatialCoordinates) : UpperCoordinates :=
  ⟨((p 0:ℂ)+(p 1:ℂ)*Complex.I,max deltaLoss (p 2)),lt_of_lt_of_le hδ (le_max_left _ _)⟩

lemma continuous_clampedCoordinates (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    Continuous (clampedCoordinates deltaLoss hδ) := by
  apply Continuous.subtype_mk
  exact ((Complex.continuous_ofReal.comp (continuous_apply 0)).add
    ((Complex.continuous_ofReal.comp (continuous_apply 1)).mul_const Complex.I)).prodMk
      (continuous_const.max (continuous_apply 2))

lemma continuous_axis_update (p : SpatialCoordinates) (j : Fin 3) :
    Continuous (fun t : ℝ => Function.update p j t) := by
  apply continuous_pi
  intro k
  by_cases h : k=j
  · subst k
    simp only [Function.update_self]
    fun_prop
  · simpa only [Function.update_of_ne h] using (continuous_const : Continuous (fun _ : ℝ => p k))

lemma smoothSummand_eq_clamped (s : ℂ) (r : CuspCosets) (p : SpatialCoordinates)
    (deltaLoss : ℝ) (hδ : 0<deltaLoss) (hp : deltaLoss≤p 2) :
    smoothSummand s r p = summand (coordinateSection (clampedCoordinates deltaLoss hδ p)) s r := by
  have hv : 0<p 2 := lt_of_lt_of_le hδ hp
  simpa only [coordinateSection,clampedCoordinates,max_eq_right hp] using smoothSummand_eq_actual s r p hv

theorem axis_summable_derivative_bounds (s : ℂ) (hs : 2<s.re)
    (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    ∃ ε : ℝ, 0<ε ∧ ∃ M₀ M₁ M₂ : CuspCosets → ℝ,
      Summable M₀ ∧ Summable M₁ ∧ Summable M₂ ∧
      ∀ t ∈ Metric.ball (p j) ε,
        0 < (Function.update p j t) 2 ∧ ∀ r : CuspCosets,
        ‖axisSlice (smoothSummand s r) p j t‖≤M₀ r ∧
        ‖deriv (axisSlice (smoothSummand s r) p j) t‖≤M₁ r ∧
        ‖deriv (deriv (axisSlice (smoothSummand s r) p j)) t‖≤M₂ r := by
  let deltaLoss : ℝ := p 2/2
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let path := fun t => clampedCoordinates deltaLoss hδ (Function.update p j t)
  have hpath : Continuous path := (continuous_clampedCoordinates deltaLoss hδ).comp (continuous_axis_update p j)
  let C := rowBound (coordinateSection (path (p j)))+1
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection (path (p j)))]
  have hb : ∀ᶠ t in 𝓝 (p j), rowBound (coordinateSection (path t))<C :=
    (continuous_coordinate_rowBound.comp hpath).continuousAt.eventually_lt_const (by dsimp [C]; linarith)
  have hh : ∀ᶠ t in 𝓝 (p j), deltaLoss < (Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change deltaLoss < (Function.update p j (p j)) 2
    rw [Function.update_eq_self]
    dsimp [deltaLoss]
    linarith
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff_ball.mp (hh.and hb)
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C s.re s.re hC hs hs
  let c₁ := ‖s‖*(1/deltaLoss)
  let c₂ := ‖s‖^2*(1/deltaLoss)^2 + ‖s‖*(7/deltaLoss^2)
  refine ⟨ε,hε,M,fun r => M r*c₁,fun r => M r*c₂,hM,hM.mul_right _,hM.mul_right _,?_⟩
  intro t ht
  obtain ⟨hht,hbt⟩ := hball t ht
  have hpos : 0 < (Function.update p j t) 2 := lt_trans hδ hht
  refine ⟨hpos,fun r => ?_⟩
  have hm : ‖smoothSummand s r (Function.update p j t)‖≤M r := by
    rw [smoothSummand_eq_clamped s r _ deltaLoss hδ hht.le]
    exact hbound (path t,s) hbt.le le_rfl le_rfl r
  have hfrac : 1 / (Function.update p j t) 2 ≤ 1/deltaLoss := one_div_le_one_div_of_le hδ hht.le
  have hfrac₂ : 7 / ((Function.update p j t) 2)^2 ≤ 7/deltaLoss^2 := by
    apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hδ)
    nlinarith
  have hd₁ := norm_smooth_axis_deriv s r (Function.update p j t) hpos j
  have hd₂ := norm_smooth_axis_deriv2 s r (Function.update p j t) hpos j
  rw [smoothSummand_axis_update,Function.update_self] at hd₁ hd₂
  refine ⟨hm,hd₁.trans ?_,hd₂.trans ?_⟩
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    exact mul_le_mul_of_nonneg_left hfrac (norm_nonneg s)
  · apply mul_le_mul hm _ (by positivity) (hMnonneg r)
    dsimp [c₂]
    gcongr

lemma smooth_axis_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (axisSlice (smoothSummand s r) p j) t := by
  have h := smooth_axis_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

lemma smooth_axis_deriv_differentiable_at (s : ℂ) (r : CuspCosets)
    (p : SpatialCoordinates) (j : Fin 3) (t : ℝ) (hv : 0<(Function.update p j t) 2) :
    DifferentiableAt ℝ (deriv (axisSlice (smoothSummand s r) p j)) t := by
  have h := smooth_axis_deriv_differentiable s r (Function.update p j t) hv j
  simpa only [smoothSummand_axis_update,Function.update_self] using h

end CubicEisenstein

end

end OAI

end


