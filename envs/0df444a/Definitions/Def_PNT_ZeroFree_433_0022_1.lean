-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0022_1
-- name    : PNT_ZeroFree_433_0022_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:17:37.692796+00:00
-- url     : https://prove2.me/theorems/44078576-3a33-4bfe-8467-ef44daefe298
-- title:
--   Zero-free region foundations: PrimeRows.RationalApproximation [0022_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.PrimeRows.RationalApproximation
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/PrimeRows/RationalApproximation.lean#L24-L328

import Definitions.Def_PNT_ZeroFree_433_0021

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

 theorem cpos : 0 < Real.log 2 / 20 := by
  have h : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

theorem eventual_log_absorption (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D → 2 ≤ D →
      D ^ ((4 / 45 : ℝ) - ε) ≤
        (Real.log 2 / 20) *
          (D ^ (4 / 45 : ℝ) / Real.log (D ^ (4 / 45 : ℝ))) := by
  have hsmall := (isLittleO_log_rpow_atTop hε).bound cpos
  obtain ⟨D₀, hD₀⟩ := eventually_atTop.mp hsmall
  refine ⟨D₀, ?_⟩
  intro D hD hDtwo
  have hDpos : 0 < D := by linarith
  have hDone : 1 ≤ D := by linarith
  have hlogDpos : 0 < Real.log D := Real.log_pos (by linarith)
  have hpowpos : 0 < D ^ (4 / 45 : ℝ) := Real.rpow_pos_of_pos hDpos _
  have hlogYpos : 0 < Real.log (D ^ (4 / 45 : ℝ)) := by
    rw [Real.log_rpow hDpos]
    positivity
  have hlogD : Real.log D ≤
      (Real.log 2 / 20) * D ^ ε := by
    have h := hD₀ D hD
    simpa only [Real.norm_eq_abs, abs_of_pos hlogDpos,
      abs_of_pos (Real.rpow_pos_of_pos hDpos ε)] using h
  have hYleD : D ^ (4 / 45 : ℝ) ≤ D := by
    calc
      D ^ (4 / 45 : ℝ) ≤ D ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDone (by norm_num)
      _ = D := by simp
  have hlogY : Real.log (D ^ (4 / 45 : ℝ)) ≤
      (Real.log 2 / 20) * D ^ ε :=
    (Real.log_le_log hpowpos hYleD).trans hlogD
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hlogYpos).mpr
  calc
    D ^ ((4 / 45 : ℝ) - ε) * Real.log (D ^ (4 / 45 : ℝ)) ≤
        D ^ ((4 / 45 : ℝ) - ε) *
          ((Real.log 2 / 20) * D ^ ε) :=
          mul_le_mul_of_nonneg_left hlogY (Real.rpow_nonneg hDpos.le _)
    _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
      calc
        D ^ ((4 / 45 : ℝ) - ε) *
            ((Real.log 2 / 20) * D ^ ε) =
            (Real.log 2 / 20) *
              (D ^ ((4 / 45 : ℝ) - ε) * D ^ ε) := by ring
        _ = (Real.log 2 / 20) *
            D ^ (((4 / 45 : ℝ) - ε) + ε) := by
              rw [← Real.rpow_add hDpos]
        _ = (Real.log 2 / 20) * D ^ (4 / 45 : ℝ) := by
              congr 1
              ring_nf

theorem scale_large_eventually (Y₀ : ℝ) :
    ∃ D₀ : ℝ, ∀ D : ℝ, D₀ ≤ D →
      2 ≤ D ∧ Y₀ ≤ D ^ (4 / 45 : ℝ) := by
  let M : ℝ := max 1 Y₀
  refine ⟨max 2 (M ^ (45 / 4 : ℝ)), ?_⟩
  intro D hD
  have hD2 : 2 ≤ D := (le_max_left _ _).trans hD
  have hMpos : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_max_left _ _)
  have hpowle : M ^ (45 / 4 : ℝ) ≤ D :=
    (le_max_right _ _).trans hD
  have hroot : M ≤ D ^ (4 / 45 : ℝ) := by
    calc
      M = (M ^ (45 / 4 : ℝ)) ^ (4 / 45 : ℝ) := by
        rw [← Real.rpow_mul hMpos.le]
        have hmul : (45 / 4 : ℝ) * (4 / 45 : ℝ) = 1 := by norm_num
        rw [hmul]
        simp
      _ ≤ D ^ (4 / 45 : ℝ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hMpos.le _) hpowle (by norm_num)
  exact ⟨hD2, (le_max_right _ _).trans hroot⟩

theorem from_rational_prime_rows_with_constant
    (D ε J A C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hC : 1 ≤ C)
    (hJ : D ^ ((4 / 45 : ℝ) - ε) ≤ J)
    (hmean : J * A ^ 2 ≤
      2 * D ^ ((31 / 15 : ℝ) + ε) +
      2 * J * C ^ 2 * D ^ (82 / 45 : ℝ)) :
    A ≤ 2 * C * D ^ ((89 / 90 : ℝ) + ε) := by
  let E : ℝ := (89 / 90 : ℝ) + ε
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hJpos : 0 < J := lt_of_lt_of_le (Real.rpow_pos_of_pos hDpos _) hJ
  have hpow :
      D ^ ((31 / 15 : ℝ) + ε) ≤
        J * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    calc
      D ^ ((31 / 15 : ℝ) + ε) =
          D ^ ((4 / 45 : ℝ) - ε) *
            D ^ ((89 / 45 : ℝ) + 2 * ε) := by
            rw [← Real.rpow_add hDpos]
            congr 1
            ring
      _ ≤ J * D ^ ((89 / 45 : ℝ) + 2 * ε) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
  have herr : D ^ (82 / 45 : ℝ) ≤
      D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    apply Real.rpow_le_rpow_of_exponent_le hD
    linarith
  have hC2 : 1 ≤ C ^ 2 := by nlinarith
  have hP : 0 ≤ J * D ^ ((89 / 45 : ℝ) + 2 * ε) := by positivity
  have hsq : A ^ 2 ≤
      4 * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    have hmain : J * A ^ 2 ≤
        4 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
      calc
        J * A ^ 2 ≤
            2 * D ^ ((31 / 15 : ℝ) + ε) +
            2 * J * C ^ 2 * D ^ (82 / 45 : ℝ) := hmean
        _ ≤ 2 * (J * D ^ ((89 / 45 : ℝ) + 2 * ε)) +
            2 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
              gcongr
        _ ≤ 4 * J * C ^ 2 * D ^ ((89 / 45 : ℝ) + 2 * ε) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hC2) hP]
    nlinarith
  have hexp : (89 / 45 : ℝ) + 2 * ε = E * 2 := by
    dsimp [E]
    ring
  have hpow2 : (D ^ E) ^ 2 = D ^ ((89 / 45 : ℝ) + 2 * ε) := by
    calc
      (D ^ E) ^ 2 = D ^ (E * 2) :=
        (Real.rpow_mul_natCast hDpos.le E 2).symm
      _ = D ^ ((89 / 45 : ℝ) + 2 * ε) := by rw [hexp]
  have htwo : 0 ≤ 2 * C * D ^ E := by positivity
  apply (sq_le_sq₀ hA htwo).mp
  rw [mul_pow, mul_pow, hpow2]
  nlinarith

theorem rational_row_error_power
    (D r : ℕ) (hD : 1 ≤ D)
    (hrlo : (D : ℝ) ^ (4 / 45 : ℝ) / 3 < (r : ℝ)) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  let X : ℝ := (D : ℝ) ^ (4 / 45 : ℝ)
  let P : ℝ := (D : ℝ) ^ (41 / 45 : ℝ)
  let q : ℝ := (D / r : ℕ)
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hXpos : 0 < X := Real.rpow_pos_of_pos hDpos _
  have hqnonneg : 0 ≤ q := by positivity
  have hP1 : 1 ≤ P := by
    calc
      1 = (D : ℝ) ^ (0 : ℝ) := by simp
      _ ≤ (D : ℝ) ^ (41 / 45 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hDreal (by norm_num)
  have hDP : (D : ℝ) = X * P := by
    dsimp [X, P]
    rw [← Real.rpow_add hDpos]
    norm_num
  have hdivnat : D / r * r ≤ D := Nat.div_mul_le_self D r
  have hdivreal : q * (r : ℝ) ≤ (D : ℝ) := by
    change ((D / r : ℕ) : ℝ) * (r : ℝ) ≤ (D : ℝ)
    exact_mod_cast hdivnat
  have hXr : X ≤ 3 * (r : ℝ) := by
    dsimp [X] at hrlo ⊢
    linarith
  have hXq : X * q ≤ 3 * (D : ℝ) := by
    calc
      X * q ≤ (3 * (r : ℝ)) * q :=
        mul_le_mul_of_nonneg_right hXr hqnonneg
      _ ≤ 3 * (D : ℝ) := by nlinarith [hdivreal]
  have hq : q ≤ 3 * P := by
    apply le_of_mul_le_mul_left (a := X) ?_ hXpos
    calc
      X * q ≤ 3 * (D : ℝ) := hXq
      _ = X * (3 * P) := by rw [hDP]; ring
  have hfinal : (128 : ℝ) * (q + 1) ≤ 512 * P := by
    nlinarith [hq, hP1]
  simpa [q, P] using hfinal

end RationalQuant

open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

namespace RationalPrimeExtraction

theorem eventual_count_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      2 ≤ D ∧
      (D : ℝ) ^ ((4 / 45 : ℝ) - ε) ≤
        ((selected ((D : ℝ) ^ (4 / 45 : ℝ))).card : ℝ) := by
  obtain ⟨Y₀, hcount⟩ := rational_prime_three_interval_count
  obtain ⟨Dlog, hlog⟩ := RationalQuant.eventual_log_absorption ε hε
  obtain ⟨Dscale, hscale⟩ := RationalQuant.scale_large_eventually Y₀
  refine ⟨max Dlog Dscale, ?_⟩
  intro D hD
  have hDl : Dlog ≤ (D : ℝ) := (le_max_left _ _).trans hD
  have hDs : Dscale ≤ (D : ℝ) := (le_max_right _ _).trans hD
  obtain ⟨hDtwo, hY⟩ := hscale (D : ℝ) hDs
  have hDtwoNat : 2 ≤ D := by exact_mod_cast hDtwo
  have habs := hlog (D : ℝ) hDl hDtwo
  have hprime := hcount ((D : ℝ) ^ (4 / 45 : ℝ)) hY
  exact ⟨hDtwoNat, habs.trans (by simpa only [selected] using hprime)⟩

theorem selected_rows_in_ball [DecidableEq O] (D : ℕ) (hD : 1 ≤ D) :
    (selected ((D : ℝ) ^ (4 / 45 : ℝ))).image
      (fun r : ℕ => (r : O) ^ 6) ⊆
      rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ := by
  classical
  intro u hu
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
  have hrI : r ∈ Finset.Ioc
      ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊
      ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_filter.mp hr).1
  have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
  have hrupper : r ≤ ⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ :=
    (Finset.mem_Ioc.mp hrI).2
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hYpos : 0 ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    Real.rpow_nonneg hDpos.le _
  have hrupperCast : (r : ℝ) ≤
      (⌊(D : ℝ) ^ (4 / 45 : ℝ)⌋₊ : ℝ) := by
    exact_mod_cast hrupper
  have hrupperReal : (r : ℝ) ≤ (D : ℝ) ^ (4 / 45 : ℝ) :=
    hrupperCast.trans (Nat.floor_le hYpos)
  have hnorm : qNat ((r : O) ^ 6) = r ^ 12 := by
    rw [rational_qNat_pow r 6 hrprime.ne_zero]
    ring
  have hpow : (r : ℝ) ^ 12 ≤
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 := by gcongr
  have hYpow : ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
      (D : ℝ) ^ (16 / 15 : ℝ) := by
    calc
      ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12 =
          (D : ℝ) ^ ((4 / 45 : ℝ) * (12 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 12).symm
      _ = (D : ℝ) ^ (16 / 15 : ℝ) := by congr 1; norm_num
  have hnormreal : (qNat ((r : O) ^ 6) : ℝ) ≤
      (⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊ : ℝ) := by
    rw [hnorm]
    exact (by exact_mod_cast hpow :
      ((r ^ 12 : ℕ) : ℝ) ≤ ((D : ℝ) ^ (4 / 45 : ℝ)) ^ 12).trans
        (hYpow.le.trans (Nat.le_ceil _))
  exact mem_rowNormBall_of_qNat_le _ _ (by exact_mod_cast hnormreal)

theorem selected_row_error_bound (D : ℕ) (hD : 1 ≤ D)
    (r : ℕ) (hr : r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ))) :
    ((128 * (D / r + 1) : ℕ) : ℝ) ≤
      512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
  have hrlo : ⌊(D : ℝ) ^ (4 / 45 : ℝ) / 3⌋₊ < r :=
    (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1
  exact RationalQuant.rational_row_error_power D r hD
    (Nat.lt_of_floor_lt hrlo)

end RationalPrimeExtraction

open ActualEisensteinCubic ShortDraftLatticeCount

namespace RationalPrimeExtraction

theorem eventual_finite_extraction (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ A : O → ℂ,
      (∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
        ‖A 1 - A ((r : O) ^ 6)‖ ≤
          512 * (D : ℝ) ^ (41 / 45 : ℝ)) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤
          (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖A 1‖ ≤ 1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₀, hcount⟩ := eventual_count_power ε hε
  refine ⟨D₀, ?_⟩
  intro D hD A happrox hmean
  classical
  obtain ⟨hDtwo, hJcount⟩ := hcount D hD
  have hDone : 1 ≤ D := by omega
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hDone
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  let S := selected ((D : ℝ) ^ (4 / 45 : ℝ))
  let rows := rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊
  let E : ℝ := 512 * (D : ℝ) ^ (41 / 45 : ℝ)
  let M : ℝ := (D : ℝ) ^ ((31 / 15 : ℝ) + ε)
  have hrows : S.image (fun r : ℕ => (r : O) ^ 6) ⊆ rows :=
    selected_rows_in_ball D hDone
  have hinj : Set.InjOn (fun r : ℕ => (r : O) ^ 6) (S : Set ℕ) := by
    intro r _ s _ hrs
    exact rational_sixth_injective hrs
  have hextract := ShortDraft.complex_row_extraction rows S
    (fun r : ℕ => (r : O) ^ 6) A 1 E M
    (by dsimp [E]; positivity) hrows hinj happrox hmean
  have herr : E ^ 2 = 512 ^ 2 * (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [E]
    rw [mul_pow]
    congr 1
    calc
      ((D : ℝ) ^ (41 / 45 : ℝ)) ^ 2 =
          (D : ℝ) ^ ((41 / 45 : ℝ) * (2 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = (D : ℝ) ^ (82 / 45 : ℝ) := by congr 1; norm_num
  rw [herr] at hextract
  have hextract' : (S.card : ℝ) * ‖A 1‖ ^ 2 ≤
      2 * (D : ℝ) ^ ((31 / 15 : ℝ) + ε) +
      2 * (S.card : ℝ) * 512 ^ 2 *
        (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [M] at hextract
    nlinarith [hextract]
  have hbound := RationalQuant.from_rational_prime_rows_with_constant
    (D : ℝ) ε (S.card : ℝ) ‖A 1‖ 512 hDreal hε.le
    (norm_nonneg _) (by norm_num) hJcount hextract'
  simpa only [show (2 : ℝ) * 512 = 1024 by norm_num] using hbound

open ActualEisensteinCubic ShortDraftLatticeCount


end RationalPrimeExtraction

namespace OscSpecial


end OscSpecial

namespace GaussianMoment

open scoped Topology
open Filter


end GaussianMoment

namespace ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT Complex


end ActualEisensteinCubic

namespace OscSpecial

open scoped Topology
open Filter


end OscSpecial

end

end OAI

end


