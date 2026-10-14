-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0298_parallel1_1
-- name    : PNT_ZeroFree_433_0298_parallel1_1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:23:21.004017+00:00
-- url     : https://prove2.me/theorems/b0833747-53f3-4eb7-ae67-52697b725542
-- title:
--   Zero-free region foundations: Moments.Lattice [0298_parallel1_1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Moments.Lattice
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/Lattice.lean#L15-L177

import Mathlib.Algebra.Ring.NonZeroDivisors
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.GaussSum
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0003
import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0038_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0042
import Definitions.Def_PNT_ZeroFree_433_0046_1_1
import Definitions.Def_PNT_ZeroFree_433_0048
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0062
import Definitions.Def_PNT_ZeroFree_433_0067
import Definitions.Def_PNT_ZeroFree_433_0068_1
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0192_parallel1
import Definitions.Def_PNT_ZeroFree_433_0225_parallel1
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region proofs, split between original source modules.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Moments/Lattice.lean#L15-L177
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Moments.Lattice
section
namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentLattice
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open QuadraticInitialBound

theorem radial_zero_mode_error (W : 𝓢(ℝ, ℂ)) (t : ℝ) (ht : 0 < t)
    (A : O → ℂ) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ h, ‖A h‖ ≤ B) :
    ‖t • (∑' h : O, A h * paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)) -
      t • (A 0 * paperRadialFourier W 0)‖ ≤ B * pvControl W := by
  let F : O → ℂ := fun h => A h * paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hF (h : O) : ‖F h‖ ≤ B * ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA h) (norm_nonneg _)
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF (hs.mul_left B)
  have hsplit := hFs.of_norm.tsum_eq_add_tsum_ite 0
  have hzero : F 0 = A 0 * paperRadialFourier W 0 := by simp only [F, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
  have htail : (∑' h : O, if h = 0 then 0 else F h) =
      ∑' h : {h : O // h ≠ 0}, F h := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [if_neg h.property]
  have heq : (∑' h : O, F h) - F 0 = ∑' h : {h : O // h ≠ 0}, F h := by
    rw [hsplit, htail]
    ring
  have hn : ‖∑' h : {h : O // h ≠ 0}, F h‖ ≤
      B * (∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) := by
    calc
      _ ≤ ∑' h : {h : O // h ≠ 0}, ‖F h‖ := norm_tsum_le_tsum_norm (hFs.subtype _)
      _ ≤ ∑' h : {h : O // h ≠ 0}, B *
          ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ :=
        (hFs.subtype _).tsum_le_tsum (fun h => hF h) ((hs.subtype _).mul_left B)
      _ = _ := tsum_mul_left
  change ‖t • (∑' h : O, F h) - t • (A 0 * paperRadialFourier W 0)‖ ≤ _
  rw [← hzero, ← smul_sub, heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ t * (B * ∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) :=
      mul_le_mul_of_nonneg_left hn ht.le
    _ = B * (t * ∑' h : {h : O // h ≠ 0},
        ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖) := by ring
    _ ≤ B * pvControl W := mul_le_mul_of_nonneg_left (pv_lattice_bound W t ht) hB

theorem periodic_lattice_volume_error (W : 𝓢(ℝ, ℂ)) (X : ℝ) (hX : 0 < X)
    (c : O) (hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖(∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
        W (‖eisEmbedding z‖ ^ 2 / X)) -
      (X / ‖eisEmbedding c‖ ^ 2 : ℝ) •
        ((∑ r : O ⧸ Ideal.span {c}, P r) * paperRadialFourier W 0)‖ ≤
      (∑ r : O ⧸ Ideal.span {c}, ‖P r‖) * pvControl W := by
  classical
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  let A : O → ℂ := fun h => ∑ r : O ⧸ Ideal.span {c},
    P r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)
  let B : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖P r‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hA (h : O) : ‖A h‖ ≤ B := by
    apply (norm_sum_le _ _).trans
    dsimp only [B]
    apply Finset.sum_le_sum
    intro r _
    rw [norm_mul, ψ.norm_apply, mul_one]
  have hA0 : A 0 = ∑ r : O ⧸ Ideal.span {c}, P r := by
    simp only [A, map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
  have hnorm : 0 < ‖eisEmbedding c‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have h := radial_zero_mode_error W (X / ‖eisEmbedding c‖ ^ 2)
    (div_pos hX hnorm) A B hB hA
  rw [actual_radial_paper_poisson_trace W X hX c hc P]
  rw [hA0] at h
  simpa only [A, B, ψ, div_mul_eq_mul_div] using h

theorem logPhase_eq_normPower (t x : ℝ) (hx : 0 < x) :
    FourierBridge.logPhase (t / (2 * Real.pi)) (Real.log x) =
      (x : ℂ) ^ (Complex.I * t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
  unfold FourierBridge.logPhase
  rw [← Complex.ofReal_log hx.le]
  congr 1
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  push_cast
  field_simp

def normPowerProfile (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t : ℝ) : 𝓢(ℝ, ℂ) :=
  CompletedHeight.uniformTwistedSchwartz W a b ha hs hW (t / (2 * Real.pi))

theorem normPowerProfile_apply (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t x : ℝ) :
    normPowerProfile W a b ha hs hW t x = (x : ℂ) ^ (Complex.I * t) * W x := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply]
  unfold CompletedHeight.normTwistedSource
  by_cases hx : W x = 0
  · simp only [hx, mul_zero]
  · rw [logPhase_eq_normPower t x (lt_of_lt_of_le ha (hs hx).1)]

theorem normPowerProfile_zero_mode (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
      (2 * Real.pi / Real.sqrt 3 : ℂ) *
        ∫ y : ℝ in Set.Ioi 0, (y : ℂ) ^ (Complex.I * t) * W y := by
  rw [paperRadialFourier_zero_eq_halfline]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro y _
  exact normPowerProfile_apply W a b ha hs hW t y

theorem normPowerProfile_uniform_degree (a b : ℝ) (ha : 0 < a)
    (S : Finset (ℕ × ℕ)) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (normPowerProfile W a b ha hs hW t) ≤
        C * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
  obtain ⟨n, hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha S
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hbound⟩ := hn W hs hW
  exact ⟨C, hC, fun t => hbound (t / (2 * Real.pi))⟩

theorem periodic_twisted_lattice_volume_error (a b : ℝ) (ha : 0 < a) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∀ c : O, ∀ hc : c ≠ 0,
      ∀ P : O ⧸ Ideal.span {c} → ℂ,
      letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
      letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
      ∃ C : ℝ, 0 < C ∧ ∀ t X : ℝ, 0 < X →
        ‖(∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
            (((‖eisEmbedding z‖ ^ 2 / X : ℝ) : ℂ) ^ (Complex.I * t) *
              W (‖eisEmbedding z‖ ^ 2 / X))) -
          (X / ‖eisEmbedding c‖ ^ 2 : ℝ) •
            ((∑ r : O ⧸ Ideal.span {c}, P r) *
              paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)‖ ≤
          C * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  refine ⟨n, ?_⟩
  intro W hs hW c hc P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  obtain ⟨D, hD, hbound⟩ := hn W hs hW
  let B : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖P r‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine ⟨(1 + B) * pvConstant * D, mul_pos (mul_pos (by linarith) pvConstant_pos) hD, ?_⟩
  intro t X hX
  have h := periodic_lattice_volume_error (normPowerProfile W a b ha hs hW t) X hX c hc P
  simp only [normPowerProfile_apply] at h
  apply h.trans
  change B * (pvConstant * _) ≤ _
  calc
    _ ≤ B * (pvConstant * (D * (1 + ‖t / (2 * Real.pi)‖) ^ n)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbound t) pvConstant_pos.le) hB
    _ ≤ (1 + B) * pvConstant * D * (1 + ‖t / (2 * Real.pi)‖) ^ n := by
      nlinarith [mul_nonneg pvConstant_pos.le hD.le,
        mul_nonneg (mul_nonneg pvConstant_pos.le hD.le)
          (show 0 ≤ (1 + ‖t / (2 * Real.pi)‖) ^ n by positivity)]

end SevenEighths.CenteredMomentLattice
end

end OAI

end


