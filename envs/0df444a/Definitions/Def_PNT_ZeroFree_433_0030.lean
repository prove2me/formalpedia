-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0030
-- name    : PNT_ZeroFree_433_0030
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T13:50:16.028929+00:00
-- url     : https://prove2.me/theorems/7c903945-12cc-4a3e-87fe-1ab75105bf80
-- title:
--   Zero-free region foundations: Mellin.FiniteEulerRestoration [0030]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.FiniteEulerRestoration
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L45-L685

import Definitions.Def_PNT_ZeroFree_433_0029

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/FiniteEulerRestoration.lean#L45-L685
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Mellin.FiniteEulerRestoration
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

namespace FiniteEulerRestoration

theorem isBigO_power_atTop_div_const {A : ℝ → ℂ} {σ N : ℝ}
    (hN : 0 < N) (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => A (D / N)) =O[atTop] (fun D : ℝ => D ^ σ) := by
  have hshift : (fun D : ℝ => A (D / N)) =O[atTop]
      (fun D : ℝ => (D / N) ^ σ) :=
    hA.comp_tendsto ((tendsto_div_const_atTop_of_pos hN).2 tendsto_id)
  have hconst : (fun D : ℝ => (N ^ σ)⁻¹ * D ^ σ) =O[atTop]
      (fun D : ℝ => D ^ σ) :=
    isBigO_const_mul_self (N ^ σ)⁻¹ (fun D : ℝ => D ^ σ) atTop
  have hpower : (fun D : ℝ => (D / N) ^ σ) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
    apply hconst.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with D hD
    rw [Real.div_rpow hD hN.le]
    ring
  exact hshift.trans hpower

theorem isBigO_finite_Euler_shifts {ι : Type*} (s : Finset ι)
    (A : ℝ → ℂ) (c : ι → ℂ) (N : ι → ℝ) {σ : ℝ}
    (hN : ∀ i ∈ s, 0 < N i)
    (hA : A =O[atTop] fun D : ℝ => D ^ σ) :
    (fun D : ℝ => ∑ i ∈ s, c i * A (D / N i)) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
  have hsum : (∑ i ∈ s, fun D : ℝ => c i * A (D / N i)) =O[atTop]
      (fun D : ℝ => D ^ σ) := by
    apply IsBigO.sum
    intro i hi
    exact (isBigO_power_atTop_div_const (hN i hi) hA).const_mul_left (c i)
  exact hsum.congr_left (by
    intro D
    simp only [Finset.sum_apply])

theorem tsum_dvd_shift {N : ℕ} (hN : 0 < N)
    (b : ℕ → ℂ) (φ : ℕ → ℂ) :
    (∑' n : ℕ, if N ∣ n then b (n / N) * φ n else 0) =
      ∑' m : ℕ, b m * φ (N * m) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  let g : ℕ → ℂ := fun m => b m * φ (N * m)
  have hindex (m : ℕ) : f (N * m) = g m := by
    simp [f, g, hN]
  change (∑' n : ℕ, f n) = ∑' m : ℕ, g m
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x : Function.support g => N * x.1) ?_ ?_ ?_
  · intro x y hxy
    apply Subtype.ext
    exact Nat.mul_left_cancel hN hxy
  · intro n hn
    have hdiv : N ∣ n := by
      by_contra hnot
      have : f n = 0 := by simp [f, hnot]
      exact hn this
    let m := n / N
    have hnm : N * m = n := Nat.mul_div_cancel' hdiv
    have hgm : g m ≠ 0 := by
      intro hg
      apply hn
      rw [← hnm, hindex, hg]
    exact ⟨⟨m, hgm⟩, hnm⟩
  · intro x
    exact hindex x.1

theorem tsum_restore_one_prime {N : ℕ} (hN : 0 < N)
    (c : ℂ) (a b φ : ℕ → ℂ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * φ n))
    (hshift : Summable (fun m => b m * φ (N * m))) :
    (∑' n : ℕ, a n * φ n) =
      (∑' n : ℕ, b n * φ n) +
        c * (∑' m : ℕ, b m * φ (N * m)) := by
  classical
  let f : ℕ → ℂ := fun n => if N ∣ n then b (n / N) * φ n else 0
  have hcomp : (fun m => f (N * m)) = (fun m => b m * φ (N * m)) := by
    funext m
    simp [f, hN]
  have hinj : Function.Injective (fun m : ℕ => N * m) :=
    fun _ _ h => Nat.mul_left_cancel hN h
  have hsupport : ∀ n, n ∉ Set.range (fun m : ℕ => N * m) → f n = 0 := by
    intro n hn
    have hnot : ¬N ∣ n := by
      intro hd
      exact hn ⟨n / N, Nat.mul_div_cancel' hd⟩
    simp [f, hnot]
  have hf : Summable f := by
    rw [← (hinj.summable_iff hsupport)]
    change Summable (fun m => f (N * m))
    rw [hcomp]
    exact hshift
  have hfc : Summable (fun n => c * f n) := hf.mul_left c
  have hpoint (n : ℕ) : a n * φ n = b n * φ n + c * f n := by
    rw [hcoeff n]
    by_cases hd : N ∣ n
    · simp [f, hd]
      ring
    · simp [f, hd]
  calc
    (∑' n : ℕ, a n * φ n) = ∑' n : ℕ, (b n * φ n + c * f n) := by
      congr 1
      funext n
      exact hpoint n
    _ = (∑' n : ℕ, b n * φ n) + ∑' n : ℕ, c * f n :=
      hb.tsum_add hfc
    _ = (∑' n : ℕ, b n * φ n) + c * (∑' m : ℕ, b m * φ (N * m)) := by
      rw [tsum_mul_left, tsum_dvd_shift hN b φ]

theorem tsum_restore_one_prime_exp {N : ℕ} (hN : 0 < N)
    (c : ℂ) (a b : ℕ → ℂ) (t : ℝ)
    (hcoeff : ∀ n, a n = b n + if N ∣ n then c * b (n / N) else 0)
    (hb : Summable (fun n => b n * Real.exp (-(n : ℝ) * t)))
    (hscaled : Summable (fun m => b m * Real.exp (-(m : ℝ) * ((N : ℝ) * t)))) :
    (∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)) =
      (∑' n : ℕ, b n * Real.exp (-(n : ℝ) * t)) +
        c * (∑' m : ℕ, b m * Real.exp (-(m : ℝ) * ((N : ℝ) * t))) := by
  have hscale (m : ℕ) :
      Real.exp (-((N * m : ℕ) : ℝ) * t) =
        Real.exp (-(m : ℝ) * ((N : ℝ) * t)) := by
    congr 1
    simp only [Nat.cast_mul]
    ring
  have hshift : Summable (fun m : ℕ =>
      b m * Real.exp (-((N * m : ℕ) : ℝ) * t)) := by
    convert! hscaled using 1
    funext m
    rw [hscale]
  simpa only [hscale] using
    tsum_restore_one_prime hN c a b
      (fun n : ℕ => (Real.exp (-(n : ℝ) * t) : ℂ)) hcoeff hb hshift

end FiniteEulerRestoration

namespace FiniteSFactor

noncomputable def outsideExpSum (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, outsideCoeff S w n * Real.exp (-(n : ℝ) * t)

theorem outsideExpSum_restore_insert_prime
    (S : Finset (Ideal O)) (hprime : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (t : ℝ)
    (hbase : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n * Real.exp (-(n : ℝ) * t)))
    (hscaled : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n *
        Real.exp (-(n : ℝ) * ((Ideal.absNorm P : ℝ) * t)))) :
    outsideExpSum S w t = outsideExpSum (insert P S) w t +
      w P * outsideExpSum (insert P S) w ((Ideal.absNorm P : ℝ) * t) := by
  let N : ℕ := Ideal.absNorm P
  have hN : 0 < N :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have hcoeff (n : ℕ) :
      outsideCoeff S w n = outsideCoeff (insert P S) w n +
        (if N ∣ n then w P * outsideCoeff (insert P S) w (n / N) else 0) :=
    restore_insert_prime S hprime P hP hPnot w hzero hmul n
  unfold outsideExpSum
  exact FiniteEulerRestoration.tsum_restore_one_prime_exp hN
    (w P) (outsideCoeff S w) (outsideCoeff (insert P S) w)
    t hcoeff hbase hscaled

end FiniteSFactor
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace CompactMellinBridge

theorem mellin_weighted_sum
    (a : ℕ → ℂ) (W F : ℝ → ℂ) (s : ℂ)
    (ha0 : a 0 = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) =
      mellin W s * LSeries a s := by
  have hterm (n : ℕ) :
      (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        mellin W s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hscale := mellin_comp_mul_left W s hnpos
      have hmul : mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s =
          a n * mellin (fun t : ℝ => W ((n : ℝ) * t)) s := by
        simpa only [smul_eq_mul] using
          (mellin_const_smul (fun t : ℝ => W ((n : ℝ) * t)) s (a n))
      change mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s = _
      rw [hmul, hscale, LSeries.term_of_ne_zero hn]
      simp only [smul_eq_mul, Complex.ofReal_natCast, Complex.cpow_neg]
      ring
  have hsum :
      (∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) :=
    integral_tsum_of_summable_integral_norm hint hsumint
  have hseries :
      (∑' n : ℕ, mellin W s * LSeries.term a s n) =
        mellin W s * LSeries a s := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (mellin W s) |>.tsum_eq
  calc
    mellin (fun D : ℝ => F D⁻¹) (-s) = mellin F s := by
      simpa using mellin_comp_inv F (-s)
    _ = ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (t : ℂ) ^ (s - 1) * F t =
        ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))
      rw [← (hF t ht).tsum_eq]
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := hsum.symm
    _ = ∑' n : ℕ, mellin W s * LSeries.term a s n := by simp_rw [hterm]
    _ = mellin W s * LSeries a s := hseries

theorem normFiber_compact_euler_identity
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (s : ℂ) (hs : 1 < s.re)
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖)) :
    (χ.LFunction s * ψ.LFunction s) *
      mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s := by
  have hM := mellin_weighted_sum
    (ShortDraftHeckeBridge.normFiberCoeff weight) W F s hcoeff0 hF
    hint hsumint
    ((LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (ShortDraftHeckeBridge.pairInverseCoeff_LSeriesSummable χ ψ s hs))
  rw [hM,
    ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
  have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity χ ψ s hs
  calc
    (χ.LFunction s * ψ.LFunction s) *
        (mellin W s * LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) =
        (χ.LFunction s * ψ.LFunction s *
          LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) * mellin W s := by ring
    _ = mellin W s := by rw [hEuler]; ring

theorem weighted_sum_zero_of_large_t
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (t : ℝ) (ht : 2 ≤ t) : F t = 0 := by
  have hterm (n : ℕ) : a n * W ((n : ℝ) * t) = 0 := by
    by_cases hn : n = 0
    · simp [hn, ha0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnt : 2 ≤ (n : ℝ) * t := by
        calc
          2 ≤ t := ht
          _ = (1 : ℝ) * t := by ring
          _ ≤ (n : ℝ) * t :=
            mul_le_mul_of_nonneg_right hn1 (by linarith)
      simp [hW _ hnt]
  have hzero : HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) 0 := by
    simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  exact (hF t (lt_of_lt_of_le (by norm_num) ht)).unique hzero

theorem weighted_sum_zero_near_small_D
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
  have hDpos : 0 < D := hD.1
  have hDsmall : D < 1 / 2 := hD.2
  have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
  have hinv : 2 ≤ D⁻¹ := by
    rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
    nlinarith
  exact weighted_sum_zero_of_large_t a ha0 W F hW hF D⁻¹ hinv

theorem compact_weight_mellin_analytic
    (W : ℝ → ℂ) (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0)
    (σ : ℝ) :
    AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re} := by
  let A : ℝ → ℂ := fun D => W D⁻¹
  have hcont : ContinuousOn A (Set.Ioi (0 : ℝ)) := by
    have hcontW : ContinuousOn W Set.univ := hW.continuous.continuousOn
    apply hcontW.comp
      (continuousOn_inv₀.mono (by
        intro D hD
        exact ne_of_gt hD))
    intro D hD
    simp
  have hlocal : LocallyIntegrableOn A (Set.Ioi (0 : ℝ)) :=
    hcont.locallyIntegrableOn measurableSet_Ioi
  have hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with D hD
    have hDpos : 0 < D := hD.1
    have hDsmall : D < 1 / 2 := hD.2
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right (le_of_lt hDsmall) hDinvpos.le
    have hinv : 2 ≤ D⁻¹ := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inr hinv)
  have hzeroTop : A =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with D hD
    have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
    have hDinvpos : 0 < D⁻¹ := inv_pos.mpr hDpos
    have hmul := mul_le_mul_of_nonneg_right hD hDinvpos.le
    have hinv : D⁻¹ ≤ 1 := by
      rw [mul_inv_cancel₀ (ne_of_gt hDpos)] at hmul
      nlinarith
    exact hsupp D⁻¹ (Or.inl hinv)
  have htop : A =O[atTop] (fun D : ℝ => D ^ σ) :=
    hzeroTop.isBigO.trans (isBigO_zero _ _)
  have hM := ShortDraftMellin.inverse_mellin_analytic A σ hlocal htop hzero
  simpa only [A, mellin_comp_inv, neg_neg] using hM

theorem pair_zero_free_of_compact_weight_bound
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧ ψ.LFunction ρ ≠ 0 := by
  let a : ℕ → ℂ := ShortDraftHeckeBridge.normFiberCoeff weight
  have ha0 : a 0 = 0 := hcoeff0
  have hMseries (s : ℂ) (hs : 1 < s.re) :
      mellin (fun D : ℝ => F D⁻¹) (-s) =
        mellin W s * LSeries a s := by
    apply mellin_weighted_sum a W F s ha0 (fun t ht => hF t ht)
      (hint s hs) (hsumint s hs)
    exact (LSeriesSummable_congr s (fun {n} hn => hcoeff n hn)).mpr
      (ShortDraftHeckeBridge.pairInverseCoeff_LSeriesSummable χ ψ s hs)
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLχ : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hL : AnalyticOnNhd ℂ (fun s => χ.LFunction s * ψ.LFunction s) U :=
    hLχ.mul hLψ
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => F D⁻¹) (-s)) U :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have heq (s : ℂ) (hs : 1 < s.re) :
      (χ.LFunction s * ψ.LFunction s) *
        mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s := by
    rw [hMseries s hs,
      ShortDraftHeckeBridge.normFiber_LSeries_eq_pair_inverse χ ψ weight hcoeff s]
    have hEuler := ShortDraftHeckeBridge.pair_inverse_euler_identity χ ψ s hs
    calc
      (χ.LFunction s * ψ.LFunction s) *
          (mellin W s * LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) =
          (χ.LFunction s * ψ.LFunction s *
            LSeries (ShortDraftHeckeBridge.pairInverseCoeff χ ψ) s) * mellin W s := by ring
      _ = mellin W s := by rw [hEuler]; ring
  have hprod : χ.LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_analytic_identity σ hσ
      (fun s => χ.LFunction s * ψ.LFunction s)
      (fun s => mellin (fun D : ℝ => F D⁻¹) (-s)) (mellin W)
      hL hM hWanalytic heq ρ hρ hWρ
  exact mul_ne_zero_iff.mp hprod

theorem pair_zero_free_of_weighted_identity_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (σ : ℝ) (hσ : σ < 1) (M W : ℂ → ℂ)
    (hM : AnalyticOnNhd ℂ M {s : ℂ | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s : ℂ | σ < s.re})
    (heq : ∀ s : ℂ, 1 < s.re →
      ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) (hWρ : W ρ ≠ 0) :
    (1 : DirichletCharacter ℂ q).LFunction ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s : ℂ | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hLregular₁ : AnalyticOnNhd ℂ
      (DirichletCharacter.LFunctionTrivChar₁ q) U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ q).differentiableOn
  have hLψ : AnalyticOnNhd ℂ ψ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (ψ.differentiable_LFunction hψ).differentiableOn
  have hLregular : AnalyticOnNhd ℂ
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) U :=
    hLregular₁.mul hLψ
  have hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s =
        (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) := by
    intro s _ hs
    simp [DirichletCharacter.LFunctionTrivChar₁,
      DirichletCharacter.LFunctionTrivChar, Function.update_of_ne hs]
    ring
  have heqregular : ∀ s : ℂ, 1 < s.re →
      (DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s) * M s =
        (s - 1) * W s := by
    intro s hs
    rw [hregular s (lt_trans hσ hs) (by
      intro h; subst s; norm_num at hs)]
    calc
      (s - 1) * ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s =
          (s - 1) * (((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) * M s) := by ring
      _ = (s - 1) * W s := by rw [heq s hs]
  have hprod :
      (1 : DirichletCharacter ℂ q).LFunction ρ * ψ.LFunction ρ ≠ 0 :=
    ShortDraft.zero_free_of_regularized_analytic_identity σ hσ
      (fun s => (1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s)
      (fun s => DirichletCharacter.LFunctionTrivChar₁ q s * ψ.LFunction s)
      M W hLregular hM hW hregular heqregular ρ hρ hρone hWρ
  exact mul_ne_zero_iff.mp hprod

theorem pair_zero_free_of_compact_weight_bound_principal_left
    {q r : ℕ} [NeZero q] [NeZero r]
    (ψ : DirichletCharacter ℂ r) (hψ : ψ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff
          (1 : DirichletCharacter ℂ q) ψ n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : mellin W ρ ≠ 0) :
    (1 : DirichletCharacter ℂ q).LFunction ρ ≠ 0 ∧
      ψ.LFunction ρ ≠ 0 := by
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => F D⁻¹) (-s))
      {s : ℂ | σ < s.re} :=
    ShortDraftMellin.inverse_mellin_analytic _ σ hlocal htop hzero
  have heq (s : ℂ) (hs : 1 < s.re) :
      ((1 : DirichletCharacter ℂ q).LFunction s * ψ.LFunction s) *
        mellin (fun D : ℝ => F D⁻¹) (-s) = mellin W s :=
    normFiber_compact_euler_identity 1 ψ weight hcoeff hcoeff0 W F
      hF s hs (hint s hs) (hsumint s hs)
  exact pair_zero_free_of_weighted_identity_principal_left ψ hψ σ hσ
    (fun s => mellin (fun D : ℝ => F D⁻¹) (-s)) (mellin W)
    hM hWanalytic heq ρ hρ hρone hWρ

theorem pair_zero_free_of_compact_weight_bound_principal_right
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (weight : Ideal ShortDraftHeckeBridge.O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff χ
          (1 : DirichletCharacter ℂ r) n)
    (hcoeff0 : ShortDraftHeckeBridge.normFiberCoeff weight 0 = 0)
    (W F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ =>
        ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) *
          (ShortDraftHeckeBridge.normFiberCoeff weight n * W ((n : ℝ) * t))‖))
    (σ : ℝ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn (fun D : ℝ => F D⁻¹) (Set.Ioi 0))
    (hzero : (fun D : ℝ => F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (htop : (fun D : ℝ => F D⁻¹) =O[atTop] (fun D : ℝ => D ^ σ))
    (hWanalytic : AnalyticOnNhd ℂ (mellin W) {s : ℂ | σ < s.re})
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : mellin W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 ∧
      (1 : DirichletCharacter ℂ r).LFunction ρ ≠ 0 := by
  have hcoeff' : ∀ n : ℕ, n ≠ 0 →
      ShortDraftHeckeBridge.normFiberCoeff weight n =
        ShortDraftHeckeBridge.pairInverseCoeff
          (1 : DirichletCharacter ℂ r) χ n := by
    intro n hn
    rw [hcoeff n hn, ShortDraftHeckeBridge.pairInverseCoeff_comm]
  have h := pair_zero_free_of_compact_weight_bound_principal_left
    χ hχ weight hcoeff' hcoeff0 W F hF hint hsumint
    σ hσ hlocal hzero htop hWanalytic ρ hρ hρone hWρ
  exact ⟨h.2, h.1⟩

structure BaseChangeCompactTest
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) where
  W : ℝ → ℂ
  F : ℝ → ℂ
  sigma : ℝ
  sigma_pos : 0 < sigma
  sigma_lt : sigma < ρ.re
  smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) W
  support : ∀ y : ℝ, y ≤ 1 ∨ 2 ≤ y → W y = 0
  sum_eq : ∀ t : ℝ, 0 < t →
    HasSum (fun n : ℕ =>
      ShortDraftHeckeBridge.normFiberCoeff
        (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)) (F t)
  term_integrable : ∀ (s : ℂ), 1 < s.re → ∀ n : ℕ,
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t)))
      (Set.Ioi 0)
  fubini : ∀ (s : ℂ), 1 < s.re → Summable (fun n : ℕ =>
    ∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) *
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ) n * W ((n : ℝ) * t))‖)
  locally_integrable : LocallyIntegrableOn
    (fun D : ℝ => F D⁻¹) (Set.Ioi 0)
  power_bound : (fun D : ℝ => F D⁻¹) =O[atTop]
    (fun D : ℝ => D ^ sigma)
  mellin_nonzero : mellin W ρ ≠ 0

theorem dirichletTarget_of_compact_normFiber_tests
    (hTest : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        BaseChangeCompactTest χ ρ) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · let T := hTest q χ ρ h23 hρ
    have hσone : T.sigma < 1 := lt_trans T.sigma_lt hρ
    have hρone : ρ ≠ 1 := by
      intro hh
      subst ρ
      norm_num at hρ
    have hc := ShortDraftHeckeBridge.normFiberCoeff_baseChange_eq_pairInverseCoeff χ
    have hz := ShortDraftHeckeBridge.normFiberCoeff_baseChangeWeight_zero χ
    have hzeroTest :
        (fun D : ℝ => T.F D⁻¹) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0) :=
      weighted_sum_zero_near_small_D
        (ShortDraftHeckeBridge.normFiberCoeff
          (ShortDraftHeckeBridge.baseChangeWeight χ)) hz T.W T.F
        (fun y hy => T.support y (Or.inr hy)) T.sum_eq
    have hWanalytic : AnalyticOnNhd ℂ (mellin T.W)
        {s : ℂ | T.sigma < s.re} :=
      compact_weight_mellin_analytic T.W T.smooth T.support T.sigma
    by_cases hχ : χ = 1
    · have hψ : ShortDraftHeckeBridge.baseChangeChar χ ≠ 1 :=
        ShortDraftHeckeBridge.baseChangeChar_ne_one_of_one χ hχ
      have hc' : ∀ n : ℕ, n ≠ 0 →
          ShortDraftHeckeBridge.normFiberCoeff
            (ShortDraftHeckeBridge.baseChangeWeight χ) n =
            ShortDraftHeckeBridge.pairInverseCoeff
              (1 : DirichletCharacter ℂ q)
              (ShortDraftHeckeBridge.baseChangeChar χ) n := by
        intro n hn
        simpa only [hχ] using hc n hn
      have hpair := pair_zero_free_of_compact_weight_bound_principal_left
        (q := q) (ShortDraftHeckeBridge.baseChangeChar χ) hψ
        (ShortDraftHeckeBridge.baseChangeWeight χ) hc' hz
        T.W T.F T.sum_eq T.term_integrable T.fubini
        T.sigma hσone T.locally_integrable hzeroTest T.power_bound
        hWanalytic ρ T.sigma_lt hρone T.mellin_nonzero
      simpa only [hχ] using hpair.1
    · by_cases hψ : ShortDraftHeckeBridge.baseChangeChar χ = 1
      · have hc' : ∀ n : ℕ, n ≠ 0 →
            ShortDraftHeckeBridge.normFiberCoeff
              (ShortDraftHeckeBridge.baseChangeWeight χ) n =
              ShortDraftHeckeBridge.pairInverseCoeff χ
                (1 : DirichletCharacter ℂ (q * 3)) n := by
          intro n hn
          simpa only [hψ] using hc n hn
        exact (pair_zero_free_of_compact_weight_bound_principal_right
          χ hχ (ShortDraftHeckeBridge.baseChangeWeight χ) hc' hz
          T.W T.F T.sum_eq T.term_integrable T.fubini
          T.sigma hσone T.locally_integrable hzeroTest T.power_bound
          hWanalytic ρ T.sigma_lt hρone T.mellin_nonzero).1
      · exact (pair_zero_free_of_compact_weight_bound
          χ (ShortDraftHeckeBridge.baseChangeChar χ) hχ hψ
          (ShortDraftHeckeBridge.baseChangeWeight χ) (fun n hn => hc n hn) hz
          T.W T.F T.sum_eq T.term_integrable T.fubini
          T.sigma hσone T.locally_integrable hzeroTest T.power_bound
          hWanalytic ρ T.sigma_lt T.mellin_nonzero).1
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

end CompactMellinBridge

end

end OAI

end


