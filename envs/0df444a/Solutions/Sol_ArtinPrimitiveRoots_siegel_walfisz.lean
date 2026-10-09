-- Prove2me | solution 1 for ArtinPrimitiveRoots.siegel_walfisz
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:43.816644+00:00
-- url     : https://prove2.me/submissions/036be4d5-4c6b-41b3-b0f8-53f574da7890

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_ArtinSieve
import Definitions.Def_SWPort_001
import Theorems.Thm_SWPort_Davenport_siegel_walfisz_ap

section
-- module Solutions.Artin.SW.BridgeCore
/-!
# From the `ψ` form of Siegel–Walfisz to the `π`/`Li` form

`SWPsi` is the progression form `ψ(N;q,a) = N/φ(q) + O(N exp(-c √log N))` for `q ≤ (log N)^A`,
with `ψ(N;q,a) = ∑_{n<N, n ≡ a (q)} Λ(n)` written out exactly as alya's `Davenport.psiAP`
(prove2.me theorem `Davenport.siegel_walfisz_ap`, ff9f3207).  `siegel_walfisz_of_psi` derives
`ArtinPrimitiveRoots.siegel_walfisz` from it by partial summation: prime powers cost
`O(√k log k)`, moduli below `√Y` are bounded trivially, and `exp(-c √log Y)` beats every power of
`log Y`.

The partial-summation lemmas (`abel_sum_real` … `abs_thetaq_sub_psiAP_le`) are copied from our
Bombieri–Vinogradov development `Solutions/Artin/BV` (LiSum, Transfer1, Transfer2).
-/

namespace SWPort.Bridge

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-! ## Partial summation (from `Solutions/Artin/BV`) -/

theorem antitoneOn_inv_log : AntitoneOn (fun t : ℝ => 1 / Real.log t) (Set.Ici 2) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have h1 : 0 < Real.log a := Real.log_pos (by linarith)
  have h2 : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  exact one_div_le_one_div_of_le h1 h2

theorem li_sum_compare (k : ℕ) (hk : 2 ≤ k) :
    |ArtinPrimitiveRoots.logIntegral k - ∑ j ∈ Ioc 1 k, 1 / Real.log j| ≤ 1 / Real.log 2 := by
  set f : ℝ → ℝ := fun t => 1 / Real.log t with hf
  set a := k - 2 with ha
  have hk' : (k : ℝ) = 2 + a := by rw [ha]; push_cast [hk]; ring
  have hanti : AntitoneOn f (Set.Icc 2 (2 + a)) :=
    antitoneOn_inv_log.mono (fun t ht => ht.1)
  have hI1 := hanti.integral_le_sum
  have hI2 := hanti.sum_le_integral
  have hli : ArtinPrimitiveRoots.logIntegral k = ∫ x in (2 : ℝ)..2 + a, f x := by
    rw [ArtinPrimitiveRoots.logIntegral, hk']
  have hsum : ∑ j ∈ Ioc 1 k, 1 / Real.log j = ∑ i ∈ range (a + 1), f (2 + i) := by
    rw [show k = 1 + (a + 1) by omega, ← Finset.Ico_add_one_add_one_eq_Ioc,
      Finset.sum_Ico_eq_sum_range]
    rw [show 1 + (a + 1) + 1 - (1 + 1) = a + 1 by omega]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hf]; push_cast; ring_nf
  have hs1 : ∑ i ∈ range (a + 1), f (2 + i) = ∑ i ∈ range a, f (2 + i) + f (2 + a) :=
    Finset.sum_range_succ _ _
  have hs2 : ∑ i ∈ range (a + 1), f (2 + i) = ∑ i ∈ range a, f (2 + (i + 1 : ℕ)) + f 2 := by
    rw [Finset.sum_range_succ']; simp
  have hfa : 0 ≤ f (2 + a) := by
    simp only [hf]; exact one_div_nonneg.mpr (Real.log_nonneg (by have : (0:ℝ) ≤ a := Nat.cast_nonneg a; linarith))
  have hf2 : f 2 = 1 / Real.log 2 := rfl
  rw [hli, hsum, abs_le]
  constructor
  · rw [hs2]; linarith
  · rw [hs1]; linarith

/-- Real Abel summation. -/
theorem abel_sum_real (g f : ℕ → ℝ) (s N : ℕ) (hsN : s ≤ N) :
    ∑ k ∈ Ioc s N, g k * f k =
      (∑ j ∈ Ioc s N, g j) * f N - ∑ k ∈ Ico s N, (∑ j ∈ Ioc s k, g j) * (f (k + 1) - f k) := by
  induction N, hsN using Nat.le_induction with
  | base => simp
  | succ N hsN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_Ioc_succ_top (by omega),
      Finset.sum_Ico_succ_top hsN]
    ring

theorem pi_eq_sum (Y : ℝ) (q a : ℕ) :
    (ArtinPrimitiveRoots.primeCountingAP Y q a : ℝ) =
      ∑ j ∈ Ioc 1 ⌊Y⌋₊, (if j.Prime ∧ j ≡ a [MOD q] then (1 : ℝ) else 0) := by
  rw [ArtinPrimitiveRoots.primeCountingAP, Finset.sum_boole]
  congr 2
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨h, hp, hpa⟩; exact ⟨⟨hp.one_lt, by omega⟩, hp, hpa⟩
  · rintro ⟨⟨_, h⟩, hp, hpa⟩; exact ⟨by omega, hp, hpa⟩

theorem li_sub_li_floor (Y : ℝ) (hY : 2 ≤ Y) :
    |ArtinPrimitiveRoots.logIntegral Y - ArtinPrimitiveRoots.logIntegral ⌊Y⌋₊| ≤ 1 / Real.log 2 := by
  set N := ⌊Y⌋₊ with hN
  have hN2 : (2 : ℝ) ≤ N := by
    have : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
    exact_mod_cast this
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYN : Y - N < 1 := by have := Nat.lt_floor_add_one Y; linarith
  have hcont : ∀ a b : ℝ, 2 ≤ a → 2 ≤ b →
      IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have : 2 ≤ t := by
      rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
    exact (continuousAt_const.div (Real.continuousAt_log (by linarith))
      (Real.log_pos (by linarith)).ne').continuousWithinAt
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hcont 2 N le_rfl hN2)
    (hcont N Y hN2 hY)
  rw [ArtinPrimitiveRoots.logIntegral, ArtinPrimitiveRoots.logIntegral, ← hsplit, add_sub_cancel_left]
  have hb : ∀ t ∈ Set.uIoc (N : ℝ) Y, ‖1 / Real.log t‖ ≤ 1 / Real.log 2 := by
    intro t ht
    rw [Set.uIoc_of_le hNY] at ht
    have h2t : 2 ≤ t := by linarith [ht.1]
    rw [Real.norm_of_nonneg (one_div_nonneg.mpr (Real.log_nonneg (by linarith)))]
    exact one_div_le_one_div_of_le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) h2t)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Y - N)] at this
  have h2 : 0 < 1 / Real.log 2 := by have := Real.log_two_gt_d9; positivity
  nlinarith

/-- The per-modulus partial summation estimate. -/
theorem abs_pi_sub_li_le (Y : ℝ) (hY : 2 ≤ Y) (q a : ℕ) (hq : 1 ≤ q) :
    |(ArtinPrimitiveRoots.primeCountingAP Y q a : ℝ) - ArtinPrimitiveRoots.logIntegral Y / q.totient|
      ≤ |Gq ⌊Y⌋₊ q a| * (1 / Real.log ⌊Y⌋₊) +
        ∑ k ∈ Ico 2 ⌊Y⌋₊, |Gq k q a| * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) + 3 := by
  set N := ⌊Y⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hY)
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  set f : ℕ → ℝ := fun k => 1 / Real.log k with hf
  set g : ℕ → ℝ := fun j => (if j.Prime ∧ j ≡ a [MOD q] then Real.log j else 0) - 1 / q.totient
    with hg
  have hpi : (ArtinPrimitiveRoots.primeCountingAP Y q a : ℝ) =
      ∑ k ∈ Ioc 1 N, g k * f k + (1 / (q.totient : ℝ)) * ∑ k ∈ Ioc 1 N, f k := by
    rw [pi_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ioc] at hj
    have hl : Real.log j ≠ 0 := (Real.log_pos (by exact_mod_cast hj.1)).ne'
    simp only [hg, hf]
    split_ifs <;> field_simp <;> ring
  have hG : ∀ k, Gq k q a = ∑ j ∈ Ioc 1 k, g j := fun k => rfl
  have habel := abel_sum_real g f 1 N (by omega)
  have hIco : ∑ k ∈ Ico 1 N, (∑ j ∈ Ioc 1 k, g j) * (f (k + 1) - f k) =
      ∑ k ∈ Ico 2 N, (∑ j ∈ Ioc 1 k, g j) * (f (k + 1) - f k) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < N)]
    simp
  rw [hIco] at habel
  have hfN : 0 ≤ f N := one_div_nonneg.mpr (Real.log_natCast_nonneg N)
  have hmono : ∀ k ∈ Ico 2 N, 0 ≤ f k - f (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    simp only [hf]
    have h1 : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk.1)
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk.1
    have hk0 : (0 : ℝ) < k := by linarith
    have h2 : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log hk0 (by push_cast; linarith)
    have := one_div_le_one_div_of_le h1 h2
    linarith
  have hmain : |∑ k ∈ Ioc 1 N, g k * f k| ≤ |Gq N q a| * f N +
      ∑ k ∈ Ico 2 N, |Gq k q a| * (f k - f (k + 1)) := by
    rw [habel, ← hG]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hfN]
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun k hk => ?_))
      rw [abs_mul, ← hG, abs_sub_comm, abs_of_nonneg (hmono k hk)]
  have hli1 := li_sum_compare N hN2
  have hli2 := li_sub_li_floor Y hY
  rw [← hN] at hli2
  have hl2 : 1 / Real.log 2 < 1.45 := by
    have := Real.log_two_gt_d9
    rw [div_lt_iff₀ (by linarith)]; linarith
  have hφ1 : 1 / (q.totient : ℝ) ≤ 1 := by
    rw [div_le_one hφ]; exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hrest : |(1 / (q.totient : ℝ)) * ∑ k ∈ Ioc 1 N, f k -
      ArtinPrimitiveRoots.logIntegral Y / q.totient| ≤ 3 := by
    have e : (1 / (q.totient : ℝ)) * ∑ k ∈ Ioc 1 N, f k -
        ArtinPrimitiveRoots.logIntegral Y / q.totient =
        (1 / (q.totient : ℝ)) * ((∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N) +
          (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)) := by ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N| ≤ 1 / Real.log 2 := by
      rw [abs_sub_comm]; exact hli1
    have h2 : |ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y| ≤
        1 / Real.log 2 := by rw [abs_sub_comm]; exact hli2
    have h3 := abs_add_le (∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N)
      (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)
    have h4 : 0 ≤ |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N +
        (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)| := abs_nonneg _
    calc 1 / (q.totient : ℝ) * |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N +
          (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)|
        ≤ 1 * |∑ k ∈ Ioc 1 N, f k - ArtinPrimitiveRoots.logIntegral N +
          (ArtinPrimitiveRoots.logIntegral N - ArtinPrimitiveRoots.logIntegral Y)| :=
          mul_le_mul_of_nonneg_right hφ1 h4
      _ ≤ 3 := by linarith
  rw [hpi, add_sub_assoc]
  refine (abs_add_le _ _).trans ?_
  have e2 : ∀ k ∈ Ico 2 N, |Gq k q a| * (f k - f (k + 1)) =
      |Gq k q a| * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) := fun k _ => rfl
  rw [← Finset.sum_congr rfl e2]
  linarith

/-- `|θ(k;q,a) - ψ(k;q,a)| ≤ 2 √k log k`. -/
theorem abs_thetaq_sub_psiAP_le (k q a : ℕ) (hk : 1 ≤ k) :
    |thetaq k q a - psiAP k q a| ≤ 2 * √(k : ℝ) * Real.log k := by
  set F : ℕ → ℝ := fun n => if n.Prime ∧ n ≡ a [MOD q] then Λ n else 0 with hF
  have e1 : thetaq k q a = ∑ n ∈ Ioc 0 k, F n := by
    rw [← Finset.sum_Ioc_consecutive F (Nat.zero_le 1) hk]
    have h0 : ∑ n ∈ Ioc 0 1, F n = 0 := by simp [hF, Nat.not_prime_one]
    rw [h0, zero_add, thetaq]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [hF]
    split_ifs with h
    · rw [ArithmeticFunction.vonMangoldt_apply_prime h.1]
    · rfl
  have e2 : psiAP k q a = ∑ n ∈ Ioc 0 k, (if n ≡ a [MOD q] then Λ n else 0) := by
    rw [psiAP, Finset.sum_filter]
  have hdiff : psiAP k q a - thetaq k q a =
      ∑ n ∈ Ioc 0 k, ((if n ≡ a [MOD q] then Λ n else 0) - F n) := by
    rw [e1, e2, Finset.sum_sub_distrib]
  have hlo : 0 ≤ psiAP k q a - thetaq k q a := by
    rw [hdiff]
    refine Finset.sum_nonneg fun n _ => ?_
    simp only [hF]
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]
  have hhi : psiAP k q a - thetaq k q a ≤ ∑ n ∈ (Ioc 0 k).filter (fun n => ¬ n.Prime), Λ n := by
    rw [hdiff, Finset.sum_filter]
    refine Finset.sum_le_sum fun n _ => ?_
    simp only [hF]
    split_ifs <;> simp_all [ArithmeticFunction.vonMangoldt_nonneg]
  have hcheb := Chebyshev.psi_sub_theta_eq_sum_not_prime (k : ℝ)
  rw [Nat.floor_natCast] at hcheb
  have hle := Chebyshev.psi_sub_theta_le (x := (k : ℝ)) (by exact_mod_cast hk)
  rw [abs_sub_comm, abs_of_nonneg hlo]
  linarith

/-! ## New: the bridge -/

theorem psiAP_eq_range (k q a : ℕ) :
    psiAP k q a = ∑ n ∈ range (k + 1),
      if (n : ZMod q) = (a : ZMod q) then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 := by
  have hI : Ioc 0 k = Ico 1 (k + 1) := by ext n; simp; omega
  rw [psiAP, Finset.sum_filter, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < k + 1), hI]
  simp only [Nat.cast_zero, ArithmeticFunction.map_zero, ite_self, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [ZMod.natCast_eq_natCast_iff]

theorem Gq_eq (k q a : ℕ) (hk : 1 ≤ k) :
    Gq k q a = thetaq k q a - ((k : ℝ) - 1) / q.totient := by
  rw [Gq, thetaq, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
  rw [Nat.cast_sub hk]
  ring

theorem thetaq_nonneg (k q a : ℕ) : 0 ≤ thetaq k q a :=
  Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact Real.log_natCast_nonneg j
    · exact le_rfl

theorem thetaq_le (k q a : ℕ) : thetaq k q a ≤ k * Real.log k := by
  calc thetaq k q a ≤ ∑ j ∈ Ioc 1 k, Real.log k := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_Ioc] at hj
        split_ifs
        · exact Real.log_le_log (by exact_mod_cast (by omega : 0 < j)) (by exact_mod_cast hj.2)
        · exact Real.log_natCast_nonneg k
    _ = ((k - 1 : ℕ) : ℝ) * Real.log k := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    _ ≤ k * Real.log k := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.log_natCast_nonneg k)
        exact_mod_cast Nat.sub_le k 1

/-- Trivial bound `|G_q(k)| ≤ k (log k + 1)`. -/
theorem abs_Gq_triv (k q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    |Gq k q a| ≤ k * (Real.log k + 1) := by
  rw [Gq_eq k q a hk]
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h1 : 0 ≤ ((k : ℝ) - 1) / q.totient := by
    apply div_nonneg _ (by linarith); have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have h2 : ((k : ℝ) - 1) / q.totient ≤ k := by
    rw [div_le_iff₀ (by linarith)]; have : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have h3 := thetaq_nonneg k q a
  have h4 := thetaq_le k q a
  rw [abs_le]; constructor <;> nlinarith

/-- `|G_q(k)| ≤ 2 √k log k + |ψ(k+1; q, a) - (k+1)/φ(q)| + 2` with `ψ` in the `Davenport` form. -/
theorem abs_Gq_le_psi (k q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q) :
    |Gq k q a| ≤ 2 * √(k : ℝ) * Real.log k +
      |(∑ n ∈ range (k + 1),
          if (n : ZMod q) = (a : ZMod q) then (ArithmeticFunction.vonMangoldt n : ℝ) else 0)
          - ((k + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ)| + 2 := by
  rw [Gq_eq k q a hk, ← psiAP_eq_range]
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have h2 : 0 ≤ 2 / (q.totient : ℝ) ∧ 2 / (q.totient : ℝ) ≤ 2 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ (by linarith)]; linarith
  have e : thetaq k q a - ((k : ℝ) - 1) / q.totient =
      (thetaq k q a - psiAP k q a) + (psiAP k q a - ((k + 1 : ℕ) : ℝ) / q.totient)
        + 2 / q.totient := by
    push_cast; ring
  rw [e]
  have := abs_thetaq_sub_psiAP_le k q a hk
  calc _ ≤ |thetaq k q a - psiAP k q a| + |psiAP k q a - ((k + 1 : ℕ) : ℝ) / q.totient|
        + |2 / (q.totient : ℝ)| := abs_add_three _ _ _
    _ ≤ _ := by rw [abs_of_nonneg h2.1]; linarith [h2.2]

/-- Any power of `t` is `O(exp(β √t))`. -/
theorem rpow_le_exp_sqrt (B β : ℝ) (hB : 0 ≤ B) (hβ : 0 < β) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → t ^ B ≤ K * Real.exp (β * √t) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * B ≤ n := ⟨⌈2 * B⌉₊, Nat.le_ceil _⟩
  refine ⟨max 1 (n.factorial / β ^ n), le_max_left _ _, fun t ht => ?_⟩
  rcases le_or_gt t 1 with h1 | h1
  · have : t ^ B ≤ 1 := Real.rpow_le_one ht h1 hB
    have h3 : 1 ≤ Real.exp (β * √t) := Real.one_le_exp (by positivity)
    calc t ^ B ≤ 1 := this
      _ ≤ max 1 (n.factorial / β ^ n) * 1 := by simp
      _ ≤ _ := by gcongr
  · have hexp := Real.pow_div_factorial_le_exp (x := β * √t) (by positivity) n
    have hsq : (√t) ^ n = t ^ ((n : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ht]; ring_nf
    have hmono : t ^ B ≤ t ^ ((n : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (by linarith)
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hβn : 0 < β ^ n := pow_pos hβ n
    rw [mul_pow, hsq, div_le_iff₀ hfac] at hexp
    calc t ^ B ≤ t ^ ((n : ℝ) / 2) := hmono
      _ = (n.factorial / β ^ n) * (β ^ n * t ^ ((n : ℝ) / 2) / n.factorial) := by
          field_simp
      _ ≤ (n.factorial / β ^ n) * Real.exp (β * √t) := by
          gcongr; rw [div_le_iff₀ hfac]; linarith
      _ ≤ _ := by gcongr; exact le_max_right _ _

theorem sum_Ico_telescope (f : ℕ → ℝ) (M : ℕ) (hM : 2 ≤ M) :
    ∑ k ∈ Ico 2 M, (f k - f (k + 1)) = f 2 - f M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih => rw [Finset.sum_Ico_succ_top hM, ih]; ring

theorem primeCountingAP_le (Y : ℝ) (hY : 2 ≤ Y) (q v : ℕ) :
    (ArtinPrimitiveRoots.primeCountingAP Y q v : ℝ) ≤ 2 * Y := by
  have h1 : ArtinPrimitiveRoots.primeCountingAP Y q v ≤ ⌊Y⌋₊ + 1 := by
    rw [ArtinPrimitiveRoots.primeCountingAP]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have h2 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have : (ArtinPrimitiveRoots.primeCountingAP Y q v : ℝ) ≤ ⌊Y⌋₊ + 1 := by exact_mod_cast h1
  linarith

theorem logIntegral_nonneg_le (Y : ℝ) (hY : 2 ≤ Y) :
    0 ≤ ArtinPrimitiveRoots.logIntegral Y ∧ ArtinPrimitiveRoots.logIntegral Y ≤ 2 * Y := by
  have hl2 : 1 / Real.log 2 < 1.45 := by
    have := Real.log_two_gt_d9
    rw [div_lt_iff₀ (by linarith)]; linarith
  have hb : ∀ t ∈ Set.uIoc (2 : ℝ) Y, ‖1 / Real.log t‖ ≤ 1 / Real.log 2 := by
    intro t ht
    rw [Set.uIoc_of_le hY] at ht
    have h2t : 2 ≤ t := by linarith [ht.1]
    rw [Real.norm_of_nonneg (one_div_nonneg.mpr (Real.log_nonneg (by linarith)))]
    exact one_div_le_one_div_of_le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) h2t)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ Y - 2)] at this
  have hnn : 0 ≤ ArtinPrimitiveRoots.logIntegral Y := by
    rw [ArtinPrimitiveRoots.logIntegral]
    refine intervalIntegral.integral_nonneg hY fun t ht => ?_
    exact one_div_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
  refine ⟨hnn, ?_⟩
  have h := (le_abs_self _).trans this
  rw [← ArtinPrimitiveRoots.logIntegral] at h
  have h1 : (0 : ℝ) ≤ 1 / Real.log 2 := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **The bridge.** The `ψ` form of Siegel–Walfisz implies the `π`/`Li` form. -/
theorem siegel_walfisz_of_psi (hSW : SWPsi) (A N : ℝ) (hA : 0 < A) (hN : 0 < N) :
    ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ log Y ^ N →
      ∀ v : ℕ, Nat.Coprime v q →
        |(ArtinPrimitiveRoots.primeCountingAP Y q v : ℝ) -
            ArtinPrimitiveRoots.logIntegral Y / Nat.totient q| ≤
          C * (Y * log Y ^ (-A)) := by
  obtain ⟨c, C, hc, hC, hsw⟩ := hSW (N + 1) (by linarith)
  set T0 : ℝ := (2 : ℝ) ^ (N + 1) with hT0
  have hT0ge : 2 ≤ T0 := by
    have : (2 : ℝ) ^ (1 : ℝ) ≤ (2 : ℝ) ^ (N + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    simpa using this
  obtain ⟨K1, hK1, hK1b⟩ := rpow_le_exp_sqrt (A + 1) (1 / 2) (by linarith) (by norm_num)
  obtain ⟨K2, hK2, hK2b⟩ := rpow_le_exp_sqrt A c hA.le hc
  -- the constant
  refine ⟨max (3 * Real.exp T0 ^ (0 : ℕ) * (2 * T0 ^ A) * Real.exp T0)
      (3 * (3 * K1 + 4 * C * 2 ^ A * K2 + 5 * K1)), ?_⟩
  intro Y hY q hq hqY v hv
  have hY0 : 0 < Y := by linarith
  set t := Real.log Y with ht
  have htpos : 0 < t := Real.log_pos (by linarith)
  have hYt : Real.exp t = Y := Real.exp_log hY0
  have hLpos : 0 < t ^ A := Real.rpow_pos_of_pos htpos A
  have hrhs : Y * t ^ (-A) = Y / t ^ A := by rw [Real.rpow_neg htpos.le, div_eq_mul_inv]
  rw [hrhs]
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  rcases lt_or_ge t T0 with hsmall | hlarge
  · -- small `Y`: trivial bounds
    have hpi := primeCountingAP_le Y hY q v
    have hpi0 : (0 : ℝ) ≤ ArtinPrimitiveRoots.primeCountingAP Y q v := Nat.cast_nonneg _
    obtain ⟨hl0, hl1⟩ := logIntegral_nonneg_le Y hY
    have hdiv0 : 0 ≤ ArtinPrimitiveRoots.logIntegral Y / q.totient := by positivity
    have hdiv1 : ArtinPrimitiveRoots.logIntegral Y / q.totient ≤ 2 * Y := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have habs : |(ArtinPrimitiveRoots.primeCountingAP Y q v : ℝ) -
        ArtinPrimitiveRoots.logIntegral Y / q.totient| ≤ 2 * Y := by
      rw [abs_le]; constructor <;> linarith
    have htA : t ^ A ≤ T0 ^ A := Real.rpow_le_rpow htpos.le hsmall.le hA.le
    have hT0A : 0 < T0 ^ A := Real.rpow_pos_of_pos (by linarith) A
    have hexpT0 : 1 ≤ Real.exp T0 := Real.one_le_exp (by linarith)
    calc _ ≤ 2 * Y := habs
      _ ≤ (3 * Real.exp T0 ^ (0 : ℕ) * (2 * T0 ^ A) * Real.exp T0) * (Y / t ^ A) := by
          rw [pow_zero, mul_div_assoc', le_div_iff₀ hLpos]
          have : 2 * Y * t ^ A ≤ 2 * Y * T0 ^ A := by gcongr
          nlinarith [mul_pos hY0 hT0A]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · -- large `Y`
    have ht2 : 2 ≤ t := le_trans hT0ge hlarge
    set M := ⌊Y⌋₊ with hM
    have hM2 : 2 ≤ M := Nat.le_floor (by exact_mod_cast hY)
    have hMY : (M : ℝ) ≤ Y := Nat.floor_le hY0.le
    have hsqY : √Y = Real.exp (t / 2) := by
      rw [← hYt, Real.sqrt_eq_iff_mul_self_eq_of_pos (Real.exp_pos _), ← Real.exp_add]; ring_nf
    have hsqY1 : 1 ≤ √Y := by rw [hsqY]; exact Real.one_le_exp (by linarith)
    have hsqYY : √Y ≤ Y := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    -- the uniform bound on `G_q(k)`
    set B : ℝ := √Y * (t + 1) + (2 * √Y * t + C * (2 * Y) * Real.exp (-c * √(t / 2)) + 2) with hB
    have hB0a : 0 ≤ √Y * (t + 1) := by positivity
    have hB0b : 0 ≤ 2 * √Y * t + C * (2 * Y) * Real.exp (-c * √(t / 2)) + 2 := by positivity
    have hG : ∀ k : ℕ, 2 ≤ k → k ≤ M → |Gq k q v| ≤ B := by
      intro k hk2 hkM
      have hk1 : 1 ≤ k := by omega
      have hkY : (k : ℝ) ≤ Y := le_trans (by exact_mod_cast hkM) hMY
      have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
      have hlogk : Real.log k ≤ t := Real.log_le_log hk0 hkY
      rcases le_or_gt (k : ℝ) √Y with hks | hks
      · have := abs_Gq_triv k q v hk1 hq
        have : (k : ℝ) * (Real.log k + 1) ≤ √Y * (t + 1) := by
          have : 0 ≤ Real.log k + 1 := by linarith [Real.log_natCast_nonneg k]
          calc (k : ℝ) * (Real.log k + 1) ≤ √Y * (Real.log k + 1) := by gcongr
            _ ≤ √Y * (t + 1) := by gcongr
        linarith
      · have hmain := abs_Gq_le_psi k q v hk1 hq
        have hk1' : ((k + 1 : ℕ) : ℝ) = k + 1 := by push_cast; ring
        have hlog1 : t / 2 ≤ Real.log ((k + 1 : ℕ) : ℝ) := by
          rw [hk1']
          have : Real.log √Y ≤ Real.log ((k : ℝ) + 1) :=
            Real.log_le_log (by linarith) (by linarith)
          rwa [hsqY, Real.log_exp] at this
        have hqk : (q : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) ^ (N + 1) := by
          have h1 : t ^ N ≤ (t / 2) ^ (N + 1) := by
            rw [Real.div_rpow htpos.le (by norm_num), Real.rpow_add htpos, Real.rpow_one,
              ← hT0, le_div_iff₀ (by positivity)]
            have : 0 < t ^ N := Real.rpow_pos_of_pos htpos N
            nlinarith
          exact hqY.trans (h1.trans (Real.rpow_le_rpow (by positivity) hlog1 (by linarith)))
        have hsw' := hsw (k + 1) q v (by omega) hq hqk hv
        have hexp : Real.exp (-c * √(Real.log ((k + 1 : ℕ) : ℝ))) ≤ Real.exp (-c * √(t / 2)) := by
          apply Real.exp_le_exp.mpr
          have := Real.sqrt_le_sqrt hlog1
          nlinarith
        have hk1Y : ((k + 1 : ℕ) : ℝ) ≤ 2 * Y := by rw [hk1']; linarith
        have hsw'' : C * ((k + 1 : ℕ) : ℝ) * Real.exp (-c * √(Real.log ((k + 1 : ℕ) : ℝ)))
            ≤ C * (2 * Y) * Real.exp (-c * √(t / 2)) := by
          have : 0 ≤ C * ((k + 1 : ℕ) : ℝ) := by positivity
          calc _ ≤ C * ((k + 1 : ℕ) : ℝ) * Real.exp (-c * √(t / 2)) := by gcongr
            _ ≤ _ := by gcongr
        have hpp : 2 * √(k : ℝ) * Real.log k ≤ 2 * √Y * t := by
          have : √(k : ℝ) ≤ √Y := Real.sqrt_le_sqrt hkY
          have : 0 ≤ Real.log k := Real.log_natCast_nonneg k
          have : 0 ≤ √(k : ℝ) := Real.sqrt_nonneg _
          calc 2 * √(k : ℝ) * Real.log k ≤ 2 * √Y * Real.log k := by gcongr
            _ ≤ 2 * √Y * t := by gcongr
        linarith
    -- partial summation
    have hps := abs_pi_sub_li_le Y hY q v hq
    rw [← hM] at hps
    have hf2 : 1 / Real.log 2 ≤ 2 := by
      have := Real.log_two_gt_d9
      rw [div_le_iff₀ (by linarith)]; linarith
    have hfM : 0 ≤ 1 / Real.log M := one_div_nonneg.mpr (Real.log_natCast_nonneg M)
    have hfMle : 1 / Real.log M ≤ 1 / Real.log 2 :=
      one_div_le_one_div_of_le (Real.log_pos (by norm_num))
        (Real.log_le_log (by norm_num) (by exact_mod_cast hM2))
    have hsum : ∑ k ∈ Ico 2 M, |Gq k q v| * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ))
        ≤ B * (1 / Real.log 2 - 1 / Real.log M) := by
      have := sum_Ico_telescope (fun k : ℕ => 1 / Real.log k) M hM2
      simp only [Nat.cast_ofNat] at this
      rw [← this, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Finset.mem_Ico] at hk
      have hd : 0 ≤ 1 / Real.log k - 1 / Real.log (k + 1 : ℕ) := by
        have h1 : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk.1)
        have h2 : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast (by omega : 0 < k)) (by push_cast; linarith)
        linarith [one_div_le_one_div_of_le h1 h2]
      push_cast at hd ⊢
      exact mul_le_mul_of_nonneg_right (hG k hk.1 hk.2.le) hd
    have hGM := hG M hM2 le_rfl
    have htot : |(ArtinPrimitiveRoots.primeCountingAP Y q v : ℝ) -
        ArtinPrimitiveRoots.logIntegral Y / q.totient| ≤ 2 * B + 3 := by
      have : |Gq M q v| * (1 / Real.log M) ≤ B * (1 / Real.log M) :=
        mul_le_mul_of_nonneg_right hGM hfM
      have hB0 : 0 ≤ B := by rw [hB]; linarith
      have e : B * (1 / Real.log 2 - 1 / Real.log M) = B * (1 / Real.log 2) - B * (1 / Real.log M) :=
        mul_sub _ _ _
      have h2B : B * (1 / Real.log 2) ≤ B * 2 := mul_le_mul_of_nonneg_left hf2 hB0
      linarith
    -- each piece of `2B + 3` is `O(Y / t^A)`
    have hsqt : √t ≤ t := by
      have h := Real.sqrt_le_sqrt (le_mul_of_one_le_right htpos.le (by linarith) : t ≤ t * t)
      rwa [Real.sqrt_mul_self htpos.le] at h
    have hp1 : √Y * t * t ^ A ≤ K1 * Y := by
      have h := hK1b t htpos.le
      rw [Real.rpow_add htpos, Real.rpow_one] at h
      have h' : Real.exp (1 / 2 * √t) ≤ √Y := by
        rw [hsqY]; exact Real.exp_le_exp.mpr (by linarith)
      have hsY : √Y * √Y = Y := Real.mul_self_sqrt hY0.le
      calc √Y * t * t ^ A = √Y * (t ^ A * t) := by ring
        _ ≤ √Y * (K1 * √Y) :=
            mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left h' (by linarith)))
              (Real.sqrt_nonneg _)
        _ = K1 * (√Y * √Y) := by ring
        _ = K1 * Y := by rw [hsY]
    have hp2 : Real.exp (-c * √(t / 2)) * t ^ A ≤ 2 ^ A * K2 := by
      have h := hK2b (t / 2) (by positivity)
      have e : t ^ A = 2 ^ A * (t / 2) ^ A := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]; ring_nf
      rw [e]
      have hE : Real.exp (-c * √(t / 2)) * Real.exp (c * √(t / 2)) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have h2A : 0 < (2 : ℝ) ^ A := by positivity
      calc Real.exp (-c * √(t / 2)) * (2 ^ A * (t / 2) ^ A)
          ≤ Real.exp (-c * √(t / 2)) * (2 ^ A * (K2 * Real.exp (c * √(t / 2)))) := by gcongr
        _ = 2 ^ A * K2 * (Real.exp (-c * √(t / 2)) * Real.exp (c * √(t / 2))) := by ring
        _ = 2 ^ A * K2 := by rw [hE, mul_one]
    have hp3 : t ^ A ≤ K1 * Y := by
      have h := hK1b t htpos.le
      rw [Real.rpow_add htpos, Real.rpow_one] at h
      have h' : Real.exp (1 / 2 * √t) ≤ Y := by
        rw [← hYt]; exact Real.exp_le_exp.mpr (by linarith)
      have : t ^ A ≤ t ^ A * t := le_mul_of_one_le_right hLpos.le (by linarith)
      nlinarith [Real.exp_pos (1 / 2 * √t)]
    -- assemble
    rw [mul_div_assoc', le_div_iff₀ hLpos]
    have hKmax : 3 * (3 * K1 + 4 * C * 2 ^ A * K2 + 5 * K1) * Y ≤
        max (3 * Real.exp T0 ^ (0 : ℕ) * (2 * T0 ^ A) * Real.exp T0)
          (3 * (3 * K1 + 4 * C * 2 ^ A * K2 + 5 * K1)) * Y := by
      gcongr; exact le_max_right _ _
    have hexpand : (2 * B + 3) * t ^ A =
        2 * (√Y * t * t ^ A) + 2 * (√Y * t ^ A) + 4 * (√Y * t * t ^ A)
          + 4 * (C * Y * (Real.exp (-c * √(t / 2)) * t ^ A)) + 7 * t ^ A := by
      rw [hB]; ring
    have hsqLe : √Y * t ^ A ≤ √Y * t * t ^ A := by
      have : 0 ≤ √Y * t ^ A := by positivity
      calc √Y * t ^ A = √Y * t ^ A * 1 := (mul_one _).symm
        _ ≤ √Y * t ^ A * t := mul_le_mul_of_nonneg_left (by linarith) this
        _ = √Y * t * t ^ A := by ring
    have hCY : C * Y * (Real.exp (-c * √(t / 2)) * t ^ A) ≤ C * Y * (2 ^ A * K2) :=
      mul_le_mul_of_nonneg_left hp2 (by positivity)
    have hfin : 3 * (3 * K1 + 4 * C * 2 ^ A * K2 + 5 * K1) * Y =
        24 * (K1 * Y) + 12 * (C * Y * (2 ^ A * K2)) := by ring
    have hpos1 : 0 ≤ K1 * Y := by positivity
    have hpos2 : 0 ≤ C * Y * (2 ^ A * K2) := by positivity
    have hp3' : t ^ A ≤ K1 * Y := hp3
    calc |(ArtinPrimitiveRoots.primeCountingAP Y q v : ℝ) -
          ArtinPrimitiveRoots.logIntegral Y / q.totient| * t ^ A
        ≤ (2 * B + 3) * t ^ A := by gcongr
      _ ≤ 3 * (3 * K1 + 4 * C * 2 ^ A * K2 + 5 * K1) * Y := by
          rw [hexpand, hfin]; linarith
      _ ≤ _ := hKmax

end SWPort.Bridge
end

section
-- module Solutions.Artin.SW.Bridge
/-!
# `ArtinPrimitiveRoots.siegel_walfisz` from alya's `Davenport.siegel_walfisz_ap`

`SWPort.Davenport.siegel_walfisz_ap` is alya's prove2.me proof (theorem ff9f3207, Mathlib c5ea003)
of the Siegel–Walfisz theorem in the `ψ` form, ported to Mathlib 0df444a under `SWPort`;
`SWPort.Bridge.siegel_walfisz_of_psi` converts it to the `π`/`Li` form by partial summation.
-/

open Real

theorem ArtinPrimitiveRoots.siegel_walfisz_oai (A N : ℝ) (hA : 0 < A) (hN : 0 < N) :
    ∃ C : ℝ, ∀ Y : ℝ, 2 ≤ Y → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ log Y ^ N →
      ∀ v : ℕ, Nat.Coprime v q →
        |(ArtinPrimitiveRoots.primeCountingAP Y q v : ℝ) -
            ArtinPrimitiveRoots.logIntegral Y / Nat.totient q| ≤
          C * (Y * log Y ^ (-A)) :=
  SWPort.Bridge.siegel_walfisz_of_psi (fun A hA => SWPort.Davenport.siegel_walfisz_ap A hA) A N hA hN
end

theorem solution : type_of% @ArtinPrimitiveRoots.siegel_walfisz_oai := @ArtinPrimitiveRoots.siegel_walfisz_oai
