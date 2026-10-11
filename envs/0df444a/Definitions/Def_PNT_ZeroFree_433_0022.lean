-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0022
-- name    : PNT_ZeroFree_433_0022
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:19:48.089761+00:00
-- url     : https://prove2.me/theorems/a2862c7b-d5e9-4204-86da-e29ff828d0d7
-- title:
--   Zero-free region foundations: PrimeRows.RationalApproximation [0022]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.PrimeRows.RationalApproximation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L332-L608

import Definitions.Def_PNT_ZeroFree_433_0022_1

/- Supporting zero-free-region estimates, split at Lean command boundaries.
Uniquely named private helpers in the first part are promoted
so the remaining estimates can use them across the module boundary.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean
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

namespace RationalQuant


end RationalQuant

open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

namespace RationalPrimeExtraction


end RationalPrimeExtraction

open ActualEisensteinCubic ShortDraftLatticeCount

namespace RationalPrimeExtraction


open ActualEisensteinCubic ShortDraftLatticeCount

theorem actual_rational_prime_extraction
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      (∀ n ∈ columns, qNat n ≤ D) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖∑ n ∈ columns, weight n‖ ≤
        1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₁, hgeneric⟩ := eventual_finite_extraction ε hε
  refine ⟨max 2 D₁, ?_⟩
  intro D hD hcolnorm hmean
  classical
  have hDtwoReal : (2 : ℝ) ≤ D := (le_max_left _ _).trans hD
  have hDtwo : 2 ≤ D := by exact_mod_cast hDtwoReal
  have hDone : 1 ≤ D := by omega
  have hDgeneric : D₁ ≤ (D : ℝ) := (le_max_right _ _).trans hD
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have happrox : ∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
      ‖A 1 - A ((r : O) ^ 6)‖ ≤
        512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
    intro r hr
    have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) ((r : O) ^ 6))‖ ≤ _
    exact (rational_prime_sixth_row_approx P hgood columns support weight
      r hrprime D hsupport hcolnorm hweight).trans
      (selected_row_error_bound D hDone r hr)
  have hmean' :
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤ (D : ℝ) ^ ((31 / 15 : ℝ) + ε) := hmean
  have hbound := hgeneric D hDgeneric A happrox hmean'
  simpa only [hone] using hbound

end RationalPrimeExtraction

namespace OscSpecial

noncomputable def phaseBoundConstant (a b : ℝ) : ℝ :=
  2 * (|a - b| + |a| + |b|) + 1

theorem phaseBoundConstant_pos (a b : ℝ) :
    0 < phaseBoundConstant a b := by
  unfold phaseBoundConstant
  positivity

theorem quadratic_phase_abs_le (a b k l : ℝ) :
    |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
      phaseBoundConstant a b * (k ^ 2 + k * l + l ^ 2) := by
  let Q : ℝ := k ^ 2 + k * l + l ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l), sq_nonneg k, sq_nonneg l]
  have hsum : k ^ 2 + l ^ 2 ≤ 2 * Q := by
    dsimp [Q]
    nlinarith [sq_nonneg (k + l)]
  have hcross : 2 * |k| * |l| ≤ k ^ 2 + l ^ 2 := by
    nlinarith [sq_nonneg (|k| - |l|), sq_abs k, sq_abs l]
  have hk : k ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg l]
  have hl : l ^ 2 ≤ 2 * Q := by nlinarith [hsum, sq_nonneg k]
  have hkl : 2 * |k| * |l| ≤ 2 * Q := hcross.trans hsum
  have h1 := mul_le_mul_of_nonneg_left hk (abs_nonneg (a - b))
  have h2 := mul_le_mul_of_nonneg_left hkl (abs_nonneg a)
  have h3 := mul_le_mul_of_nonneg_left hl (abs_nonneg b)
  have htri :
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
        |a - b| * k ^ 2 + 2 * |a| * |k| * |l| + |b| * l ^ 2 := by
    calc
      |(a - b) * k ^ 2 + 2 * a * k * l + b * l ^ 2| ≤
          |(a - b) * k ^ 2| + |2 * a * k * l| + |b * l ^ 2| := by
        calc
          _ ≤ |(a - b) * k ^ 2 + 2 * a * k * l| + |b * l ^ 2| := abs_add_le _ _
          _ ≤ _ := by
            have hh := abs_add_le ((a - b) * k ^ 2) (2 * a * k * l)
            linarith
      _ = _ := by
        simp [abs_mul,  abs_of_nonneg (sq_nonneg k),
          abs_of_nonneg (sq_nonneg l)]
  unfold phaseBoundConstant
  nlinarith [htri, h1, h2, h3, hQ]

end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter

theorem scaled_moment_vanishes_const (K : ℝ) (hK : 0 < K) :
    Tendsto
      (fun η : ℝ => η ^ 3 *
        (∑' z : ℤ × ℤ, RankTwoPoisson.eisQ z * realGauss (K * η) z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun η : ℝ => K * η)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun η : ℝ => K * η) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with η hη
      change 0 < η at hη
      exact mul_pos hK hη
  have h := scaled_moment_vanishes.comp hscale
  have h' := h.const_mul (1 / K ^ 3)
  convert! h' using 1
  · funext η
    dsimp [Function.comp_def]
    field_simp [hK.ne']
  · simp

end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex

private theorem breveE_period_div_lam_O (z : O) :
    ShortDraftTrace.breveE (eisEmbedding z / eisLam) = 1 := by
  let a := (ActualEisensteinCoordinates.coords z).1
  let b := (ActualEisensteinCoordinates.coords z).2
  have hz : z = ActualEisensteinCoordinates.eval a b :=
    (ActualEisensteinCoordinates.eval_coords z).symm
  rw [hz, eisEmbedding_eval]
  exact ConcreteBreveE.breveE_period_coordinates a b

noncomputable def fixedDualPhase (c y : O) : ℂ :=
  ShortDraftTrace.breveE (eisEmbedding (-(c*y^2)) / eisLam / (4 : ℂ))

theorem fixedDualPhase_period_two (c y w : O) :
    fixedDualPhase c (y + 2*w) = fixedDualPhase c y := by
  let d : O := -(c * (y*w+w^2))
  have hO : -(c * (y + 2*w)^2) = -(c*y^2) + 4*d := by
    dsimp [d]
    ring
  have h4 : eisEmbedding (4*d) = 4 * eisEmbedding d := by
    simp only [map_mul, map_ofNat]
  have harg :
      eisEmbedding (-(c * (y + 2*w)^2)) / eisLam / (4 : ℂ) =
        eisEmbedding (-(c*y^2)) / eisLam / (4 : ℂ) +
          eisEmbedding d / eisLam := by
    rw [hO, map_add, h4]
    ring
  unfold fixedDualPhase
  rw [harg, AddChar.map_add_eq_mul, breveE_period_div_lam_O, mul_one]

theorem fixedDualPhase_eq_of_mod_two (c y z : O)
    (h : Ideal.Quotient.mk (Ideal.span {(2 : O)}) y =
      Ideal.Quotient.mk (Ideal.span {(2 : O)}) z) :
    fixedDualPhase c y = fixedDualPhase c z := by
  have hsub : y-z ∈ Ideal.span {(2 : O)} :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h
  obtain ⟨w, hw⟩ := (Ideal.mem_span_singleton).mp hsub
  have hy : y = z + 2*w := by
    calc
      y = z+(y-z) := by ring
      _ = z+2*w := by rw [hw]
  rw [hy, fixedDualPhase_period_two]

theorem fixedDualPhase_weighted_partition (c : O) (W : O → ℂ)
    (hsum : Summable (fun y : O => fixedDualPhase c y * W y)) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    (∑' y : O, fixedDualPhase c y * W y) =
      ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r) *
          ∑' w : O,
            W (GaussianShiftedPartition.representative 2 r + 2*w) := by
  let h2 : (2 : O) ≠ 0 := by norm_num
  let : Finite (O ⧸ Ideal.span {(2 : O)}) := finite_quotient_span h2
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  rw [GaussianAbelPartition.tsum_by_finite_fibers
    (Ideal.Quotient.mk (Ideal.span {(2 : O)})) _ hsum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    (∑' z : ((Ideal.Quotient.mk (Ideal.span {(2 : O)})) ⁻¹' {r}),
      fixedDualPhase c z.1 * W z.1) =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r + 2*w) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) :=
      GaussianFiberEquiv.fiber_tsum 2 h2 r
        (GaussianShiftedPartition.representative 2 r)
        (GaussianShiftedPartition.representative_spec 2 r)
        (fun y => fixedDualPhase c y * W y)
    _ =
        ∑' w : O, fixedDualPhase c
          (GaussianShiftedPartition.representative 2 r) *
          W (GaussianShiftedPartition.representative 2 r + 2*w) := by
      apply tsum_congr
      intro w
      rw [fixedDualPhase_period_two]
    _ = _ := tsum_mul_left

end ActualEisensteinCubic

namespace OscSpecial

open scoped Topology
open Filter

noncomputable def dualScale (η a b : ℝ) : ℝ :=
  η * q a b / (4 * r η a b)

theorem dualScale_tendsto (a b : ℝ) (hq : 0 < q a b) :
    Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  have hnum : ContinuousAt (fun η : ℝ => η * q a b) 0 := by fun_prop
  have hden : ContinuousAt (fun η : ℝ => 4 * r η a b) 0 := by
    change ContinuousAt
      (fun η : ℝ => 4 * (1 + 3 * q a b * η ^ 2 / 16)) 0
    fun_prop
  have hden0 : 4 * r 0 a b ≠ 0 := by simp [r]
  have hcont : ContinuousAt (fun η : ℝ => dualScale η a b) 0 := by
    exact hnum.div hden hden0
  have hlim : Tendsto (fun η : ℝ => dualScale η a b)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [dualScale] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact hlim
  · filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hr : 0 < r η a b := by
      unfold r
      positivity
    exact div_pos (mul_pos hη hq) (mul_pos (by norm_num) hr)

theorem abel_mass_dual_scale (a b : ℝ) (hq : 0 < q a b)
    (F : ℝ → ℂ) (L : ℂ)
    (hF : Tendsto (fun t : ℝ => (t : ℂ) * F t)
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun η : ℝ => (η : ℂ) * F (dualScale η a b))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((4 / q a b : ℝ) : ℂ) * L)) := by
  have hscale := dualScale_tendsto a b hq
  have hF' := hF.comp hscale
  have hrcont : ContinuousAt
      (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ)) 0 := by
    change ContinuousAt
      (fun η : ℝ => ((4 * (1 + 3 * q a b * η ^ 2 / 16) / q a b : ℝ) : ℂ)) 0
    fun_prop
  have hr : Tendsto (fun η : ℝ => ((4 * r η a b / q a b : ℝ) : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 ((4 / q a b : ℝ) : ℂ)) := by
    simpa [r] using hrcont.tendsto.mono_left nhdsWithin_le_nhds
  have hprod := hr.mul hF'
  have heq : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ),
      (η : ℂ) * F (dualScale η a b) =
        ((4 * r η a b / q a b : ℝ) : ℂ) *
          (((dualScale η a b : ℝ) : ℂ) * F (dualScale η a b)) := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    change 0 < η at hη
    have hrpos : 0 < r η a b := by
      unfold r
      positivity
    have hqC : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hrC : (r η a b : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    dsimp [dualScale]
    push_cast
    field_simp [hqC, hrC]
  exact hprod.congr' (heq.mono fun η h => h.symm)

end OscSpecial

end

end OAI

end


