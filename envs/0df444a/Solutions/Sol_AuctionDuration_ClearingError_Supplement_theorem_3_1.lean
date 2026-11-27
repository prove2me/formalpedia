-- Prove2me | solution 1 for AuctionDuration.ClearingError.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:56.141013+00:00
-- url     : https://prove2.me/submissions/c9ddf87e-618f-4465-9355-c06a53e263b9

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Supplement_StrategicGame

open AuctionDuration
open AuctionDuration.ClearingError
open AuctionDuration.ClearingError.Supplement

/-- Theorem 3.1 (arXiv:1906.01713v3, p.13): simultaneous attained
best responses, from every natural count pair, against all predictable deviations.
The zero-duration case is the deterministic terminal-cost extension. -/
theorem solution (G : Game) (hG : G.Standing) :
    G.WellDefined ∧ ∃ fa fb : ValueField, G.IsNash fa fb := by
      open MeasureTheory Set Filter ProbabilityTheory in
      open scoped Topology ENNReal NNReal in
      have ODE1 : ∀ (h l u : ℝ), 0 ≤ h → 0 < l → l ≤ u →
          ∃ (V A : Fin 2 → ℝ → State → ℝ) (K : State → ℝ) (C : ℝ), 0 ≤ C ∧ (∀ x, 0 ≤ K x) ∧
            (∀ i x, V i 0 x = terminalCost i x) ∧
            (∀ i τ x, 0 ≤ τ → τ ≤ h → |V i τ x| ≤ C * 2 ^ (x 0 + x 1)) ∧
            (∀ i σ τ x, 0 ≤ σ → σ ≤ τ → τ ≤ h → |V i τ x - V i σ x| ≤ K x * (τ - σ)) ∧
            (∀ i σ τ x, 0 ≤ σ → σ ≤ τ → τ ≤ h →
              l * (τ - σ) ≤ A i τ x - A i σ x ∧ A i τ x - A i σ x ≤ u * (τ - σ)) ∧
            (∀ i σ τ x, 0 ≤ σ → σ ≤ τ → τ ≤ h →
              |V i τ x - V i σ x - D 0 (V i) σ x * (A 0 τ x - A 0 σ x)
                - D 1 (V i) σ x * (A 1 τ x - A 1 σ x)| ≤ K x * (τ - σ) ^ 2) ∧
            (∀ i σ x, 0 ≤ σ → σ ≤ h → 0 < D i (V i) σ x → ∃ ε > 0, ∀ τ, σ ≤ τ → τ ≤ σ + ε → τ ≤ h →
              A i τ x - A i σ x = l * (τ - σ)) ∧
            (∀ i σ x, 0 ≤ σ → σ ≤ h → D i (V i) σ x < 0 → ∃ ε > 0, ∀ τ, σ ≤ τ → τ ≤ σ + ε → τ ≤ h →
              A i τ x - A i σ x = u * (τ - σ)) := by
        clear hG G
        intro h l u hh hl hlu
        have hu : 0 < u := lt_of_lt_of_le hl hlu
        obtain ⟨sel, hselpos, hselneg, hsell, hselu⟩ : ∃ sel : ℝ → ℝ, (∀ z, 0 < z → sel z = l) ∧
            (∀ z, z < 0 → sel z = u) ∧ (∀ z, l ≤ sel z) ∧ (∀ z, sel z ≤ u) := by
          refine ⟨fun z => if 0 < z then l else if z < 0 then u else l, ?_, ?_, ?_, ?_⟩
          · intro z hz; simp [hz]
          · intro z hz; simp [hz, not_lt.2 hz.le]
          · intro z
            show l ≤ ite _ _ _
            split_ifs
            exacts [le_rfl, hlu, le_rfl]
          · intro z
            show ite _ _ _ ≤ u
            split_ifs
            exacts [hlu, le_rfl, hlu]
        obtain ⟨up, hup⟩ : ∃ up : Fin 2 → State → State, ∀ i x, up i x = Function.update x i (x i + 1) :=
          ⟨_, fun _ _ => rfl⟩
        obtain ⟨w, hw⟩ : ∃ w : State → ℝ, ∀ x, w x = 2 ^ (x 0 + x 1) := ⟨_, fun _ => rfl⟩
        have h6u : 0 ≤ 6 * u := mul_nonneg (by norm_num) hu.le
        have hn1 : ∀ n : ℕ, (0:ℝ) < (n:ℝ) + 1 := fun n => Nat.cast_add_one_pos n
        have hwpos : ∀ x, 0 < w x := fun x => by rw [hw]; positivity
        have hwup : ∀ i x, w (up i x) = 2 * w x := by
          refine Fin.forall_fin_two.2 ⟨fun x => ?_, fun x => ?_⟩
          · rw [hw, hw, hup, Function.update_self, Function.update_of_ne (Fin.zero_ne_one.symm), add_right_comm,
              pow_succ, mul_comm]
          · rw [hw, hw, hup, Function.update_self, Function.update_of_ne (Fin.zero_ne_one), ← add_assoc,
              pow_succ, mul_comm]
        obtain ⟨d, hd⟩ : ∃ d : ℕ → ℝ, ∀ n, d n = 1 / ((n : ℝ) + 1) := ⟨_, fun _ => rfl⟩
        have hdpos : ∀ n, 0 < d n := fun n => by rw [hd]; exact one_div_pos.2 (hn1 n)
        have hdlim : Tendsto d atTop (𝓝 0) := by
          have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          exact this.congr (fun n => (hd n).symm)
        -- Euler scheme
        obtain ⟨W, A, hW0, hA0, hWs, hAs⟩ : ∃ W A : ℕ → ℕ → Fin 2 → State → ℝ,
            (∀ n i x, W n 0 i x = terminalCost i x) ∧ (∀ n i x, A n 0 i x = 0) ∧
            (∀ n k i x, W n (k+1) i x = W n k i x + d n *
              (sel (W n k 0 (up 0 x) - W n k 0 x) * (W n k i (up 0 x) - W n k i x)
                + sel (W n k 1 (up 1 x) - W n k 1 x) * (W n k i (up 1 x) - W n k i x))) ∧
            (∀ n k i x, A n (k+1) i x = A n k i x + d n * sel (W n k i (up i x) - W n k i x)) := by
          let W : ℕ → ℕ → Fin 2 → State → ℝ := fun n k => Nat.rec (fun i x => terminalCost i x)
            (fun _ Wk i x => Wk i x + d n *
              (sel (Wk 0 (up 0 x) - Wk 0 x) * (Wk i (up 0 x) - Wk i x)
                + sel (Wk 1 (up 1 x) - Wk 1 x) * (Wk i (up 1 x) - Wk i x))) k
          let A : ℕ → ℕ → Fin 2 → State → ℝ := fun n k => Nat.rec (fun _ _ => 0)
            (fun k Ak i x => Ak i x + d n * sel (W n k i (up i x) - W n k i x)) k
          exact ⟨W, A, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
        have hsq : ∀ n : ℕ, (n : ℝ) ^ 2 ≤ 2 * 2 ^ n := by
          intro n
          have key : n ^ 2 ≤ 2 * 2 ^ n := by
            have hj : n * n ≤ 2 * 2 ^ n ∧ 2 * n + 1 ≤ 2 * 2 ^ n := by
              induction n with
              | zero => exact ⟨Nat.zero_le _, by decide⟩
              | succ n ih =>
                obtain ⟨i1, i2⟩ := ih
                have i3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
                have e : 2 * 2 ^ (n + 1) = 2 * 2 ^ n + 2 * 2 ^ n := by rw [pow_succ, mul_two, mul_add]
                rw [e, show (n + 1) * (n + 1) = n * n + (2 * n + 1) by ring]
                exact ⟨Nat.add_le_add i1 i2, (Nat.add_right_comm (2 * n) 2 1).trans_le (Nat.add_le_add i2 (Nat.mul_le_mul_left 2 i3))⟩
            rw [pow_two]
            exact hj.1
          exact_mod_cast key
        have hterm : ∀ i x, |terminalCost i x| ≤ 2 * w x := by
          intro i x
          have h1 := hsq (x 0 + x 1)
          rw [hw]
          push_cast at h1
          have a0 : (0:ℝ) ≤ x 0 := Nat.cast_nonneg _
          have a1 : (0:ℝ) ≤ x 1 := Nat.cast_nonneg _
          have hq : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |a * (a - b)| ≤ (a + b) ^ 2 := by
            intro a b ha hb
            rw [abs_mul, abs_of_nonneg ha, pow_two]
            refine mul_le_mul (le_add_of_nonneg_right hb) ?_ (abs_nonneg _) (add_nonneg ha hb)
            have := abs_sub a b
            rwa [abs_of_nonneg ha, abs_of_nonneg hb] at this
          refine le_trans ?_ h1
          unfold terminalCost
          split_ifs
          · exact hq _ _ a0 a1
          · rw [add_comm (x 0 : ℝ)]; exact hq _ _ a1 a0
        have habs : ∀ (p q a b U : ℝ), l ≤ p → p ≤ u → l ≤ q → q ≤ u → |a| ≤ U → |b| ≤ U →
            |p * a + q * b| ≤ 2 * u * U := by
          intro p q a b U hp hp' hq hq' ha hb
          have h1 : ∀ p a : ℝ, l ≤ p → p ≤ u → |a| ≤ U → |p * a| ≤ u * U := by
            intro p a hp hp' ha
            rw [abs_mul, abs_of_pos (hl.trans_le hp)]
            exact mul_le_mul hp' ha (abs_nonneg _) hu.le
          refine (abs_add_le _ _).trans ((add_le_add (h1 p a hp hp' ha) (h1 q b hq hq' hb)).trans_eq ?_)
          rw [mul_assoc, two_mul]
        have habs' : ∀ (d p q a b U : ℝ), 0 < d → l ≤ p → p ≤ u → l ≤ q → q ≤ u → |a| ≤ U → |b| ≤ U →
            |d * (p * a + q * b)| ≤ d * (2 * u * U) := by
          intro d p q a b U hd hp hp' hq hq' ha hb
          rw [abs_mul, abs_of_pos hd]
          exact mul_le_mul_of_nonneg_left (habs p q a b U hp hp' hq hq' ha hb) hd.le
        have hid0 : ∀ c w : ℝ, c * (2 * w) + c * w = 3 * (c * w) := fun c w => by ring
        have hid1 : ∀ c w d u : ℝ, c * w + d * (2 * u * (3 * (c * w))) = c * (1 + 6 * u * d) * w :=
          fun c w d u => by ring
        have hid2 : ∀ C w d u m : ℝ, 6 * u * C * w * (m * d) + d * (2 * u * (3 * C * w)) =
          6 * u * C * w * ((m + 1) * d) := fun C w d u m => by ring
        have hid3 : ∀ C w d u m : ℝ, 6 * u * C * (2 * w) * (m * d) + 6 * u * C * w * (m * d) =
          18 * u * C * w * (m * d) := fun C w d u m => by ring
        have hid4 : ∀ q d m u Cw : ℝ, 36 * u * u * Cw * (m * d) ^ 2 + d * (2 * u * (18 * u * Cw * (m * d))) +
          36 * u * u * Cw * (d ^ 2 * (m + 1)) = 36 * u * u * Cw * ((m + 1) * d) ^ 2 := fun q d m u Cw => by ring
        have hid5 : ∀ W0 W1 D0 D1 A0 A00 A1 A10 d s0 s1 E0 E1 : ℝ,
          W1 + d * (s0 * E0 + s1 * E1) - W0 - D0 * (A0 + d * s0 - A00) - D1 * (A1 + d * s1 - A10) =
          (W1 - W0 - D0 * (A0 - A00) - D1 * (A1 - A10)) + d * (s0 * (E0 - D0) + s1 * (E1 - D1)) :=
          fun W0 W1 D0 D1 A0 A00 A1 A10 d s0 s1 E0 E1 => by ring
        have hidz : ∀ a p b q c : ℝ, a - a - p * (b - b) - q * (c - c) = 0 := fun a p b q c => by ring
        -- bound
        have hWb : ∀ n k i x, |W n k i x| ≤ 2 * (1 + 6 * u * d n) ^ k * w x := by
          intro n k
          induction k with
          | zero => intro i x; rw [hW0, pow_zero, mul_one]; exact hterm i x
          | succ k ih =>
            intro i x
            have hdn := hdpos n
            have hwx := hwpos x
            obtain ⟨c, hc⟩ : ∃ c, c = 2 * (1 + 6 * u * d n) ^ k := ⟨_, rfl⟩
            rw [← hc] at ih
            have hdiff : ∀ j, |W n k i (up j x) - W n k i x| ≤ 3 * (c * w x) := by
              intro j
              have h1 := ih i (up j x)
              have h2 := ih i x
              rw [hwup] at h1
              exact (abs_sub _ _).trans ((add_le_add h1 h2).trans_eq (hid0 _ _))
            have h4 := habs' (d n) _ _ _ _ _ hdn (hsell (W n k 0 (up 0 x) - W n k 0 x)) (hselu _)
              (hsell (W n k 1 (up 1 x) - W n k 1 x)) (hselu _) (hdiff 0) (hdiff 1)
            rw [hWs]
            refine (abs_add_le _ _).trans ?_
            have h2 := ih i x
            refine (add_le_add h2 h4).trans_eq ?_
            rw [pow_succ, ← mul_assoc 2, ← hc]
            exact hid1 _ _ _ _
        obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * Real.exp (6 * u * h) := ⟨_, rfl⟩
        have hCpos : 0 < C := by rw [hC]; positivity
        have hWC : ∀ (n k : ℕ) (i : Fin 2) (x : State), (k:ℝ) * d n ≤ h → |W n k i x| ≤ C * w x := by
          intro n k i x hk
          refine (hWb n k i x).trans ?_
          have hdn := hdpos n
          have : (1 + 6 * u * d n) ^ k ≤ Real.exp (6 * u * h) := by
            have e1 : 1 + 6 * u * d n ≤ Real.exp (6 * u * d n) := by
              rw [add_comm]; exact Real.add_one_le_exp _
            refine (pow_le_pow_left₀ (add_nonneg zero_le_one (mul_nonneg h6u hdn.le)) e1 k).trans ?_
            rw [← Real.exp_nat_mul]
            exact Real.exp_le_exp.2 ((mul_left_comm _ _ _).trans_le (mul_le_mul_of_nonneg_left hk h6u))
          rw [hC]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this zero_le_two) (hwpos x).le
        have hDC : ∀ (n k : ℕ) (i j : Fin 2) (x : State), (k:ℝ) * d n ≤ h → |W n k i (up j x) - W n k i x| ≤ 3 * C * w x := by
          intro n k i j x hk
          have h1 := hWC n k i (up j x) hk
          have h2 := hWC n k i x hk
          rw [hwup] at h1
          refine (abs_sub _ _).trans ((add_le_add h1 h2).trans_eq ?_)
          rw [hid0, mul_assoc]
        have hLip : ∀ n k m i x, ((k + m : ℕ) : ℝ) * d n ≤ h →
            |W n (k+m) i x - W n k i x| ≤ 6 * u * C * w x * (m * d n) := by
          intro n k m i x
          have hdn := hdpos n
          induction m with
          | zero => intro _; rw [Nat.cast_zero, zero_mul, mul_zero, add_zero, sub_self, abs_zero]
          | succ m ih =>
            intro hk
            have hk' : ((k + m : ℕ) : ℝ) * d n ≤ h := by
              exact (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ _)) hdn.le).trans hk
            have h4 := habs' (d n) _ _ _ _ _ hdn (hsell (W n (k+m) 0 (up 0 x) - W n (k+m) 0 x)) (hselu _)
              (hsell (W n (k+m) 1 (up 1 x) - W n (k+m) 1 x)) (hselu _)
              (hDC n (k+m) i 0 x hk') (hDC n (k+m) i 1 x hk')
            rw [← add_assoc, hWs, add_sub_right_comm]
            refine (abs_add_le _ _).trans ?_
            have h2 := ih hk'
            rw [Nat.cast_succ]
            exact (add_le_add h2 h4).trans_eq (hid2 _ _ _ _ _)
        have hLipD : ∀ n k m i j x, ((k + m : ℕ) : ℝ) * d n ≤ h →
            |(W n (k+m) i (up j x) - W n (k+m) i x) - (W n k i (up j x) - W n k i x)|
              ≤ 18 * u * C * w x * (m * d n) := by
          intro n k m i j x hk
          have h1 := hLip n k m i (up j x) hk
          have h2 := hLip n k m i x hk
          rw [hwup] at h1
          rw [sub_sub_sub_comm]
          exact (abs_sub _ _).trans ((add_le_add h1 h2).trans_eq (hid3 _ _ _ _ _))
        have hSec : ∀ n k m i x, ((k + m : ℕ) : ℝ) * d n ≤ h →
            |W n (k+m) i x - W n k i x - (W n k i (up 0 x) - W n k i x) * (A n (k+m) 0 x - A n k 0 x)
              - (W n k i (up 1 x) - W n k i x) * (A n (k+m) 1 x - A n k 1 x)|
              ≤ 36 * u * u * C * w x * (m * d n) ^ 2 := by
          intro n k m i x
          have hdn := hdpos n
          have hwx := hwpos x
          induction m with
          | zero =>
            intro _
            rw [Nat.cast_zero, zero_mul, zero_pow two_ne_zero, mul_zero]
            exact (congrArg abs (hidz _ _ _ _ _)).trans_le abs_zero.le
          | succ m ih =>
            intro hk
            have hk' : ((k + m : ℕ) : ℝ) * d n ≤ h := by
              exact (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (Nat.le_succ _)) hdn.le).trans hk
            have h4 := habs' (d n) _ _ _ _ _ hdn (hsell (W n (k+m) 0 (up 0 x) - W n (k+m) 0 x)) (hselu _)
              (hsell (W n (k+m) 1 (up 1 x) - W n (k+m) 1 x)) (hselu _)
              (hLipD n k m i 0 x hk') (hLipD n k m i 1 x hk')
            have h2 := ih hk'
            rw [← add_assoc, hWs, hAs, hAs]
            rw [hid5]
            refine (abs_add_le _ _).trans ((add_le_add h2 h4).trans ?_)
            rw [Nat.cast_succ, mul_assoc (36 * u * u), mul_assoc (18 * u), ← hid4 0]
            exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu.le) hu.le)
              (mul_nonneg hCpos.le hwx.le)) (mul_nonneg (sq_nonneg _) (hn1 m).le))
        have hAinc : ∀ n k m i x, l * (m * d n) ≤ A n (k+m) i x - A n k i x ∧
            A n (k+m) i x - A n k i x ≤ u * (m * d n) := by
          intro n k m i x
          have hdn := hdpos n
          induction m with
          | zero => rw [Nat.cast_zero, zero_mul, mul_zero, mul_zero, add_zero, sub_self]; exact ⟨le_rfl, le_rfl⟩
          | succ m ih =>
            rw [← add_assoc, hAs, Nat.cast_succ, add_mul, one_mul, mul_add, mul_add, mul_comm l (d n), mul_comm u (d n),
              add_sub_right_comm]
            have h1 := mul_le_mul_of_nonneg_left (hsell (W n (k+m) i (up i x) - W n (k+m) i x)) hdn.le
            have h2 := mul_le_mul_of_nonneg_left (hselu (W n (k+m) i (up i x) - W n (k+m) i x)) hdn.le
            exact ⟨add_le_add ih.1 h1, add_le_add ih.2 h2⟩
        -- limits
        obtain ⟨κ, hκ⟩ : ∃ κ : ℝ → ℕ → ℕ, ∀ τ n, κ τ n = ⌊τ * ((n:ℝ) + 1)⌋₊ := ⟨_, fun _ _ => rfl⟩
        have hd1 : ∀ n : ℕ, ((n:ℝ) + 1) * d n = 1 := fun n => by rw [hd]; exact mul_one_div_cancel (hn1 n).ne'
        have hκle : ∀ τ n, 0 ≤ τ → κ τ n * d n ≤ τ := by
          intro τ n hτ
          have h1 : (κ τ n : ℝ) ≤ τ * ((n:ℝ) + 1) := by
            rw [hκ]; exact Nat.floor_le (mul_nonneg hτ (hn1 n).le)
          have := mul_le_mul_of_nonneg_right h1 (hdpos n).le
          rwa [mul_assoc, hd1, mul_one] at this
        have hκge : ∀ τ n, τ - d n ≤ κ τ n * d n := by
          intro τ n
          have h1 : τ * ((n:ℝ) + 1) < κ τ n + 1 := by
            rw [hκ]; exact Nat.lt_floor_add_one _
          have := mul_le_mul_of_nonneg_right h1.le (hdpos n).le
          rw [mul_assoc, hd1, mul_one] at this
          linarith
        have hκmono : ∀ σ τ n, σ ≤ τ → ∃ m, κ τ n = κ σ n + m := by
          intro σ τ n hst
          have : κ σ n ≤ κ τ n := by
            rw [hκ, hκ]; exact Nat.floor_le_floor (mul_le_mul_of_nonneg_right hst (hn1 n).le)
          exact ⟨_, (Nat.add_sub_cancel' this).symm⟩
        have hκ0 : ∀ n, κ 0 n = 0 := fun n => by rw [hκ, zero_mul, Nat.floor_zero]
        obtain ⟨U, hU⟩ : ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop :=
          ⟨Filter.hyperfilter ℕ, Nat.hyperfilter_le_atTop⟩
        have hdU : Tendsto d U (𝓝 0) := hdlim.mono_left hU
        have hκlim : ∀ τ, 0 ≤ τ → Tendsto (fun n => (κ τ n : ℝ) * d n) U (𝓝 τ) := by
          intro τ hτ
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => τ - d n) (h := fun _ => τ) ?_
            tendsto_const_nhds (fun n => hκge τ n) (fun n => hκle τ n hτ)
          simpa using (tendsto_const_nhds (x := τ)).sub hdU
        have hlim : ∀ (g : ℕ → ℝ) (B : ℝ), (∀ n, |g n| ≤ B) → Tendsto g U (𝓝 (limUnder (U : Filter ℕ) g)) := by
          intro g B hg
          apply tendsto_nhds_limUnder
          have hc : IsCompact (Icc (-B) B) := isCompact_Icc
          obtain ⟨L, _, hL⟩ := hc.ultrafilter_le_nhds (U.map g) (by
            rw [le_principal_iff, Ultrafilter.mem_coe, Ultrafilter.mem_map]
            exact Filter.univ_mem' (fun n => abs_le.1 (hg n)))
          exact ⟨L, hL⟩
        obtain ⟨V, hV⟩ : ∃ V : Fin 2 → ℝ → State → ℝ, ∀ i τ x, V i τ x =
          limUnder (U : Filter ℕ) (fun n => W n (κ τ n) i x) := ⟨_, fun _ _ _ => rfl⟩
        obtain ⟨B, hB⟩ : ∃ B : Fin 2 → ℝ → State → ℝ, ∀ i τ x, B i τ x =
          limUnder (U : Filter ℕ) (fun n => A n (κ τ n) i x) := ⟨_, fun _ _ _ => rfl⟩
        have hκh : ∀ τ n, 0 ≤ τ → τ ≤ h → κ τ n * d n ≤ h := fun τ n h1 h2 => (hκle τ n h1).trans h2
        have hVl : ∀ i τ x, 0 ≤ τ → τ ≤ h → Tendsto (fun n => W n (κ τ n) i x) U (𝓝 (V i τ x)) := by
          intro i τ x h1 h2
          rw [hV]
          exact hlim _ (C * w x) (fun n => hWC n _ i x (hκh τ n h1 h2))
        have hBl : ∀ i τ x, 0 ≤ τ → τ ≤ h → Tendsto (fun n => A n (κ τ n) i x) U (𝓝 (B i τ x)) := by
          intro i τ x h1 h2
          rw [hB]
          refine hlim _ (u * h) (fun n => ?_)
          have h3 := hAinc n 0 (κ τ n) i x
          have h4 := hκh τ n h1 h2
          have h5 : 0 ≤ κ τ n * d n := mul_nonneg (Nat.cast_nonneg _) (hdpos n).le
          rw [hA0, zero_add, sub_zero] at h3
          rw [abs_of_nonneg (le_trans (mul_nonneg hl.le h5) h3.1)]
          exact h3.2.trans (mul_le_mul_of_nonneg_left h4 hu.le)
        have hDl : ∀ i j τ x, 0 ≤ τ → τ ≤ h →
            Tendsto (fun n => W n (κ τ n) i (up j x) - W n (κ τ n) i x) U (𝓝 (D j (V i) τ x)) := by
          intro i j τ x h1 h2
          have := (hVl i τ (up j x) h1 h2).sub (hVl i τ x h1 h2)
          rw [hup] at this
          simpa only [D, hup] using this
        have hmd : ∀ σ τ n m, κ τ n = κ σ n + m → (m : ℝ) * d n = κ τ n * d n - κ σ n * d n := by
          intro σ τ n m hm
          rw [hm]; push_cast; ring
        have hlimdiff : ∀ σ τ, 0 ≤ σ → σ ≤ τ →
            Tendsto (fun n => (κ τ n : ℝ) * d n - κ σ n * d n) U (𝓝 (τ - σ)) :=
          fun σ τ h1 h2 => (hκlim τ (h1.trans h2)).sub (hκlim σ h1)
        -- sign persistence
        have hsign : ∀ i σ x η, 0 ≤ σ → σ ≤ h → 0 < η → |D i (V i) σ x| = η → ∃ ε > 0, ∀ τ, σ ≤ τ →
            τ ≤ σ + ε → τ ≤ h → ∀ᶠ n in (U : Filter ℕ), ∀ m, κ σ n + m ≤ κ τ n →
              |(W n (κ σ n + m) i (up i x) - W n (κ σ n + m) i x) - D i (V i) σ x| < η := by
          intro i σ x η hσ hσh hη _
          have hwx := hwpos x
          obtain ⟨K2, hK2⟩ : ∃ K2, K2 = 18 * u * C * w x := ⟨_, rfl⟩
          have hK2p : 0 < K2 := by rw [hK2]; exact mul_pos (mul_pos (mul_pos (by norm_num) hu) hCpos) hwx
          obtain ⟨ε, hε, hεK⟩ := exists_pos_mul_lt (half_pos hη) (K2 * 2)
          rw [mul_assoc] at hεK
          refine ⟨ε, hε, fun τ hστ hτε hτh => ?_⟩
          have e1 : ∀ᶠ n in (U : Filter ℕ), d n < ε := hdU.eventually (gt_mem_nhds hε)
          have e2 := (hDl i i σ x hσ hσh).eventually (Metric.ball_mem_nhds _ (half_pos hη))
          filter_upwards [e1, e2] with n h1 h2 m hm
          rw [Real.dist_eq] at h2
          have hdn := hdpos n
          have hmle : ((κ σ n + m : ℕ) : ℝ) * d n ≤ κ τ n * d n :=
            mul_le_mul_of_nonneg_right (Nat.cast_le.2 hm) hdn.le
          have a1 := hκle τ n (hσ.trans hστ)
          have h3 := hLipD n (κ σ n) m i i x (hmle.trans (a1.trans hτh))
          rw [← hK2] at h3
          have h4 : (m : ℝ) * d n ≤ 2 * ε := by
            have a2 := hκge σ n
            rw [Nat.cast_add, add_mul] at hmle
            linarith only [hmle, a1, a2, h1, hτε]
          have h5 : K2 * (m * d n) ≤ η / 2 := (mul_le_mul_of_nonneg_left h4 hK2p.le).trans hεK.le
          exact lt_of_le_of_lt (abs_sub_le _ _ _)
            ((add_lt_add_of_le_of_lt (h3.trans h5) h2).trans_eq (add_halves η))
        have hAc : ∀ n k i x c M, (∀ m, m < M → sel (W n (k+m) i (up i x) - W n (k+m) i x) = c) →
            A n (k+M) i x - A n k i x = c * (M * d n) := by
          intro n k i x c M
          induction M with
          | zero => intro _; rw [Nat.cast_zero, zero_mul, mul_zero, add_zero, sub_self]
          | succ M ih =>
            intro hs
            have := ih (fun m hm => hs m (Nat.lt_succ_of_lt hm))
            rw [← add_assoc, hAs, hs M (Nat.lt_succ_self M), add_sub_right_comm, this, Nat.cast_succ, add_mul,
              one_mul, mul_add, mul_comm (d n) c]
        have hfinal : ∀ i σ x c, 0 ≤ σ → σ ≤ h → D i (V i) σ x ≠ 0 →
            (∀ z, |z - D i (V i) σ x| < |D i (V i) σ x| → sel z = c) →
            ∃ ε > 0, ∀ τ, σ ≤ τ → τ ≤ σ + ε → τ ≤ h → B i τ x - B i σ x = c * (τ - σ) := by
          intro i σ x c hσ hσh hne hsel
          obtain ⟨ε, hε, H⟩ := hsign i σ x _ hσ hσh (abs_pos.2 hne) rfl
          refine ⟨ε, hε, fun τ hστ hτε hτh => ?_⟩
          have h1 := (hBl i τ x (hσ.trans hστ) hτh).sub (hBl i σ x hσ hσh)
          have h2 := (hlimdiff σ τ hσ hστ).const_mul c
          refine tendsto_nhds_unique (h1.congr' ?_) h2
          filter_upwards [H τ hστ hτε hτh] with n hn
          obtain ⟨m, hm⟩ := hκmono σ τ n hστ
          rw [← hmd σ τ n m hm, hm]
          exact hAc n _ i x c m (fun m' hm' => hsel _ (hn m' (hm.symm ▸ Nat.add_le_add_left hm'.le _)))
        have hPw : ∀ x, 0 ≤ 6 * u * C * w x := fun x => mul_nonneg (mul_nonneg h6u hCpos.le) (hwpos x).le
        have hQw : ∀ x, 0 ≤ 36 * u * u * C * w x := fun x =>
          mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hu.le) hu.le) hCpos.le) (hwpos x).le
        refine ⟨V, B, fun x => 6 * u * C * w x + 36 * u * u * C * w x, C, hCpos.le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact fun x => add_nonneg (hPw x) (hQw x)
        · intro i x
          have h1 := hVl i 0 x le_rfl hh
          refine tendsto_nhds_unique h1 ?_
          simp only [hκ0, hW0]
          exact tendsto_const_nhds
        · intro i τ x h1 h2
          rw [← hw]
          exact le_of_tendsto (hVl i τ x h1 h2).abs (Eventually.of_forall fun n => hWC n _ i x (hκh τ n h1 h2))
        · intro i σ τ x hσ hστ hτ
          have hwx := hwpos x
          have h1 := ((hVl i τ x (hσ.trans hστ) hτ).sub (hVl i σ x hσ (hστ.trans hτ))).abs
          have h2 := (hlimdiff σ τ hσ hστ).const_mul (6 * u * C * w x)
          have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun n => by
            obtain ⟨m, hm⟩ := hκmono σ τ n hστ
            rw [← hmd σ τ n m hm, hm]
            exact hLip n _ m i x (by rw [← hm]; exact hκh τ n (hσ.trans hστ) hτ))
          refine h3.trans ?_
          rw [add_mul]
          exact le_add_of_nonneg_right (mul_nonneg (hQw x) (sub_nonneg.2 hστ))
        · intro i σ τ x hσ hστ hτ
          have h1 := (hBl i τ x (hσ.trans hστ) hτ).sub (hBl i σ x hσ (hστ.trans hτ))
          have h2 := hlimdiff σ τ hσ hστ
          constructor
          · refine le_of_tendsto_of_tendsto' (h2.const_mul l) h1 (fun n => ?_)
            obtain ⟨m, hm⟩ := hκmono σ τ n hστ
            rw [← hmd σ τ n m hm, hm]
            exact (hAinc n _ m i x).1
          · refine le_of_tendsto_of_tendsto' h1 (h2.const_mul u) (fun n => ?_)
            obtain ⟨m, hm⟩ := hκmono σ τ n hστ
            rw [← hmd σ τ n m hm, hm]
            exact (hAinc n _ m i x).2
        · intro i σ τ x hσ hστ hτ
          have hwx := hwpos x
          have hτ0 := hσ.trans hστ
          have hσh := hστ.trans hτ
          have h1 := (((((hVl i τ x hτ0 hτ).sub (hVl i σ x hσ hσh)).sub
            ((hDl i 0 σ x hσ hσh).mul ((hBl 0 τ x hτ0 hτ).sub (hBl 0 σ x hσ hσh)))).sub
            ((hDl i 1 σ x hσ hσh).mul ((hBl 1 τ x hτ0 hτ).sub (hBl 1 σ x hσ hσh))))).abs
          have h2 := ((hlimdiff σ τ hσ hστ).pow 2).const_mul (36 * u * u * C * w x)
          have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun n => by
            obtain ⟨m, hm⟩ := hκmono σ τ n hστ
            rw [← hmd σ τ n m hm, hm]
            exact hSec n _ m i x (by rw [← hm]; exact hκh τ n hτ0 hτ))
          refine h3.trans ?_
          rw [add_mul]
          exact le_add_of_nonneg_left (mul_nonneg (hPw x) (sq_nonneg _))
        · intro i σ x hσ hσh hpos
          refine hfinal i σ x l hσ hσh hpos.ne' (fun z hz => hselpos z ?_)
          rw [abs_of_pos hpos, abs_lt] at hz
          linarith [hz.1]
        · intro i σ x hσ hσh hneg
          refine hfinal i σ x u hσ hσh hneg.ne (fun z hz => hselneg z ?_)
          rw [abs_of_neg hneg, abs_lt] at hz
          linarith [hz.2]
      have ODE2 : ∀ (h l u : ℝ), 0 ≤ h → 0 < l → l ≤ u →
          ∃ (V f : Fin 2 → ℝ → State → ℝ) (C : ℝ), 0 ≤ C ∧
            (∀ i x, Continuous (fun s => V i s x)) ∧
            (∀ i x, Measurable (fun s => f i s x)) ∧
            (∀ i s x, f i s x ∈ Icc l u) ∧
            (∀ i s x, |V i s x| ≤ C * 2 ^ (x 0 + x 1)) ∧
            (∀ i x, V i h x = terminalCost i x) ∧
            (∀ i x s t, 0 ≤ s → s ≤ t → t ≤ h → V i t x - V i s x =
              ∫ r in s..t, -(f 0 r x * D 0 (V i) r x + f 1 r x * D 1 (V i) r x)) ∧
            (∀ i s x a, l ≤ a → a ≤ u → f i s x * D i (V i) s x ≤ a * D i (V i) s x) := by
        clear hG G
        intro h l u hh hl hlu
        obtain ⟨V, A, K, C, hC, hK, hV0, hVb, hVL, hAL, hMain, hpos, hneg⟩ := ODE1 h l u hh hl hlu
        have uniq : ∀ (φ : ℝ → ℝ) (φ' r K c ε : ℝ), 0 < ε → HasDerivAt φ φ' r →
            (∀ y, r - ε ≤ y → y ≤ r → |φ y - φ r - c * (y - r)| ≤ K * (y - r) ^ 2) → φ' = c := by
          intro φ φ' r K c ε hε hd hb
          have h1 : HasDerivAt (fun y => φ y - φ r - c * (y - r)) (φ' - c) r := by
            have := (hd.sub_const (φ r)).sub (((hasDerivAt_id r).sub_const r).const_mul c)
            rw [mul_one] at this
            exact this
          have h2 : HasFDerivWithinAt (fun y => φ y - φ r - c * (y - r)) (0 : ℝ →L[ℝ] ℝ) (Icc (r - ε) r) r := by
            apply Asymptotics.IsBigO.hasFDerivWithinAt (n := 2) _ (right_mem_Icc.2 (sub_le_self r hε.le)) one_lt_two
            apply Asymptotics.IsBigO.of_bound K
            filter_upwards [self_mem_nhdsWithin] with y hy
            have := hb y hy.1 hy.2
            rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_abs, sq_abs]
            exact this
          have h3 : HasDerivWithinAt (fun y => φ y - φ r - c * (y - r)) 0 (Icc (r - ε) r) r := by
            have := h2.hasDerivWithinAt
            rw [ContinuousLinearMap.zero_apply] at this
            exact this
          have h4 := (uniqueDiffOn_Icc (sub_lt_self r hε) r (right_mem_Icc.2 (sub_le_self r hε.le))).eq_deriv _
            h1.hasDerivWithinAt h3
          exact sub_eq_zero.1 h4
        set cl : ℝ → ℝ := fun s => max 0 (min h (h - s)) with hcl
        have cl0 : ∀ s, 0 ≤ cl s := fun s => le_max_left _ _
        have clh : ∀ s, cl s ≤ h := fun s => max_le hh (min_le_left _ _)
        have cle : ∀ s, 0 ≤ s → s ≤ h → cl s = h - s := by
          intro s h0 h1
          simp only [hcl]
          rw [min_eq_right (sub_le_self h h0), max_eq_right (sub_nonneg.2 h1)]
        have clL : ∀ s t, |cl s - cl t| ≤ |s - t| := by
          intro s t
          calc |cl s - cl t| ≤ |min h (h - s) - min h (h - t)| := by
                have := abs_max_sub_max_le_abs (min h (h - s)) (min h (h - t)) 0
                rw [max_comm (min h (h - s)), max_comm (min h (h - t))] at this
                exact this
            _ ≤ |(h - s) - (h - t)| := by
                have := abs_min_sub_min_le_max h (h - s) h (h - t)
                exact this.trans (max_le (by rw [sub_self, abs_zero]; exact abs_nonneg _) le_rfl)
            _ = |s - t| := by rw [sub_sub_sub_cancel_left, abs_sub_comm]
        set Wf : Fin 2 → ℝ → State → ℝ := fun i s x => V i (cl s) x with hW
        set B : Fin 2 → State → ℝ → ℝ := fun i x s => A i (cl s) x with hB
        have lipOf : ∀ (F : ℝ → ℝ) (k : ℝ), 0 ≤ k →
            (∀ σ τ, 0 ≤ σ → σ ≤ τ → τ ≤ h → |F τ - F σ| ≤ k * (τ - σ)) →
            LipschitzWith (Real.toNNReal k) (fun s => F (cl s)) := by
          intro F k hk hF
          apply LipschitzWith.of_dist_le_mul
          intro s t
          rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal k hk]
          refine le_trans ?_ (mul_le_mul_of_nonneg_left (clL s t) hk)
          rcases le_total (cl s) (cl t) with hst | hst
          · have := hF _ _ (cl0 s) hst (clh t)
            rw [abs_sub_comm, abs_sub_comm (cl s), abs_of_nonneg (sub_nonneg.2 hst)]
            exact this
          · have := hF _ _ (cl0 t) hst (clh s)
            rw [abs_of_nonneg (sub_nonneg.2 hst)]
            exact this
        have WL : ∀ i x, LipschitzWith (Real.toNNReal (K x)) (fun s => Wf i s x) := fun i x =>
          lipOf (fun τ => V i τ x) (K x) (hK x) (fun σ τ h0 h1 h2 => hVL i σ τ x h0 h1 h2)
        have BL : ∀ i x, LipschitzWith (Real.toNNReal u) (B i x) := fun i x =>
          lipOf (fun τ => A i τ x) u (hl.le.trans hlu) (fun σ τ h0 h1 h2 => by
            have := hAL i σ τ x h0 h1 h2
            rw [abs_le]
            constructor
            · exact (neg_nonpos.2 (mul_nonneg (hl.le.trans hlu) (sub_nonneg.2 h1))).trans
                ((mul_nonneg hl.le (sub_nonneg.2 h1)).trans this.1)
            · exact this.2)
        have Dc : ∀ j i x, Continuous (fun s => D j (Wf i) s x) := fun j i x => by
          unfold D
          exact (WL i _).continuous.sub (WL i _).continuous
        set f : Fin 2 → ℝ → State → ℝ := fun i s x =>
          if 0 < D i (Wf i) s x then l else if D i (Wf i) s x < 0 then u else
            max l (min u (-deriv (B i x) s)) with hf
        refine ⟨Wf, f, C, hC, fun i x => (WL i x).continuous, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i x
          refine Measurable.ite (measurableSet_lt measurable_const (Dc i i x).measurable) measurable_const ?_
          refine Measurable.ite (measurableSet_lt (Dc i i x).measurable measurable_const) measurable_const ?_
          exact measurable_const.max (measurable_const.min (measurable_deriv _).neg)
        · intro i s x
          simp only [hf]
          split_ifs
          · exact ⟨le_rfl, hlu⟩
          · exact ⟨hlu, le_rfl⟩
          · exact ⟨le_max_left _ _, max_le hlu (min_le_left _ _)⟩
        · intro i s x
          exact hVb i _ x (cl0 s) (clh s)
        · intro i x
          simp only [hW]
          rw [cle h hh le_rfl, sub_self]
          exact hV0 i x
        · intro i x s t hs hst ht
          have hac : AbsolutelyContinuousOnInterval (fun s => Wf i s x) s t :=
            ((WL i x).lipschitzOnWith).absolutelyContinuousOnInterval
          rw [← hac.integral_deriv_eq_sub]
          apply intervalIntegral.integral_congr_ae
          filter_upwards [(WL i x).ae_differentiableAt_real, (BL 0 x).ae_differentiableAt_real,
            (BL 1 x).ae_differentiableAt_real] with r hd hb0 hb1 hr
          rw [uIoc_of_le hst] at hr
          have hr0 : 0 < r := lt_of_le_of_lt hs hr.1
          have hrh : r ≤ h := hr.2.trans ht
          have hb : ∀ j, DifferentiableAt ℝ (B j x) r := by
            intro j; fin_cases j
            · exact hb0
            · exact hb1
          have hDe : ∀ j k, D j (Wf k) r x = D j (V k) (cl r) x := fun j k => rfl
          have clr := cle r hr0.le hrh
          have key : deriv (fun s => Wf i s x) r - D 0 (Wf i) r x * deriv (B 0 x) r
              - D 1 (Wf i) r x * deriv (B 1 x) r = 0 := by
            refine uniq (fun y => Wf i y x - D 0 (Wf i) r x * B 0 x y - D 1 (Wf i) r x * B 1 x y)
              _ r (K x) 0 r hr0
              ((hd.hasDerivAt.sub ((hb 0).hasDerivAt.const_mul _)).sub ((hb 1).hasDerivAt.const_mul _)) ?_
            intro y hy0 hyr
            have cly := cle y ((sub_self r) ▸ hy0) (hyr.trans hrh)
            have := hMain i (cl r) (cl y) x (cl0 r) (by rw [clr, cly]; exact sub_le_sub_left hyr h) (clh y)
            have e : (cl y - cl r) ^ 2 = (y - r) ^ 2 := by rw [clr, cly, sub_sub_sub_cancel_left, ← neg_sub, neg_sq]
            rw [e] at this
            refine le_trans (le_of_eq ?_) this
            rw [hDe, hDe]
            simp only [hW, hB]
            congr 1; ring
          have hfD : ∀ j, f j r x = - deriv (B j x) r := by
            intro j
            have aux : ∀ c ε : ℝ, 0 < ε → (∀ τ, cl r ≤ τ → τ ≤ cl r + ε → τ ≤ h →
                A j τ x - A j (cl r) x = c * (τ - cl r)) → deriv (B j x) r = -c := by
              intro c ε hε hA
              refine uniq (B j x) _ r 0 (-c) (min ε r) (lt_min hε hr0) (hb j).hasDerivAt ?_
              intro y hy0 hyr
              have hm1 := min_le_left ε r
              have hm2 := min_le_right ε r
              have hy1 : 0 ≤ y := (sub_nonneg.2 hm2).trans hy0
              have cly := cle y hy1 (hyr.trans hrh)
              have := hA (cl y) (by rw [clr, cly]; exact sub_le_sub_left hyr h) (by rw [clr, cly]; linarith) (clh y)
              simp only [hB]
              rw [this, clr, cly]
              have : c * (h - y - (h - r)) - -c * (y - r) = 0 := by ring
              rw [this]; simp
            by_cases h1 : 0 < D j (Wf j) r x
            · obtain ⟨ε, hε, hA⟩ := hpos j (cl r) x (cl0 r) (clh r) h1
              rw [aux l ε hε hA]
              simp only [hf]
              rw [if_pos h1, neg_neg]
            · by_cases h2 : D j (Wf j) r x < 0
              · obtain ⟨ε, hε, hA⟩ := hneg j (cl r) x (cl0 r) (clh r) h2
                rw [aux u ε hε hA]
                simp only [hf]
                rw [if_neg h1, if_pos h2, neg_neg]
              · simp only [hf]
                rw [if_neg h1, if_neg h2]
                have hsl : Tendsto (slope (B j x) r) (𝓝[<] r) (𝓝 (deriv (B j x) r)) :=
                  (hasDerivAt_iff_tendsto_slope.1 (hb j).hasDerivAt).mono_left
                    (nhdsWithin_mono _ (fun y hy => ne_of_lt hy))
                have hev : ∀ᶠ y in 𝓝[<] r, -u ≤ slope (B j x) r y ∧ slope (B j x) r y ≤ -l := by
                  filter_upwards [Ioo_mem_nhdsLT hr0] with y hy
                  have cly := cle y hy.1.le (hy.2.le.trans hrh)
                  have := hAL j (cl r) (cl y) x (cl0 r) (by rw [clr, cly]; exact sub_le_sub_left hy.2.le h) (clh y)
                  have hp : 0 < r - y := sub_pos.2 hy.2
                  have e : cl y - cl r = r - y := by rw [clr, cly, sub_sub_sub_cancel_left]
                  rw [e] at this
                  have e2 : slope (B j x) r y = -((A j (cl y) x - A j (cl r) x) / (r - y)) := by
                    rw [slope_def_field]
                    simp only [hB]
                    rw [← neg_sub r y, div_neg]
                  rw [e2]
                  constructor
                  · apply neg_le_neg
                    rw [div_le_iff₀ hp]; exact this.2
                  · apply neg_le_neg
                    rw [le_div_iff₀ hp]; exact this.1
                have b1 := ge_of_tendsto hsl (hev.mono fun y hy => hy.1)
                have b2 := le_of_tendsto hsl (hev.mono fun y hy => hy.2)
                rw [min_eq_right (neg_le.1 b1), max_eq_right (le_neg_of_le_neg b2)]
          rw [hfD 0, hfD 1]
          linarith [key]
        · intro i s x a hla hau
          simp only [hf]
          by_cases h1 : 0 < D i (Wf i) s x
          · rw [if_pos h1]; exact mul_le_mul_of_nonneg_right hla h1.le
          by_cases h2 : D i (Wf i) s x < 0
          · rw [if_neg h1, if_pos h2]; exact mul_le_mul_of_nonpos_right hau h2.le
          · have : D i (Wf i) s x = 0 := le_antisymm (not_lt.1 h1) (not_lt.1 h2)
            rw [this, mul_zero, mul_zero]
      have PATHS : ∀ (ω : Sample) (i : Fin 2), (∀ T : ℝ, (jumps T ω i).Finite) ∧
          (∀ t : ℝ≥0, X t ω i = (jumps t ω i).ncard) ∧
          (∀ t : ℝ≥0, preX t ω i = (jumps t ω i ∩ Iio (t : ℝ)).ncard) := by
        clear hG G ODE1 ODE2
        intro ω i
        obtain ⟨q, hq, hqv⟩ : ∃ q : ℝ → ℕ, (∀ T : ℝ, 0 ≤ T →
            NearlyUnstableHawkes.Deterministic.IsCountingProcess T (fun t (_ : Unit) => q t)) ∧
            (ω i).val = q := ⟨(ω i).val, (ω i).property, rfl⟩
        have hJ : ∀ T s, s ∈ jumps T ω i ↔ 0 < s ∧ s ≤ T ∧
            (q s : ℝ) - Function.leftLim (fun s : ℝ => (q s : ℝ)) s = 1 := by
          intro T s; simp only [jumps, hqv, Set.mem_ofPred_eq]
        have q0 : q 0 = 0 := (hq 0 le_rfl).zero ()
        have qm : ∀ s t, 0 ≤ s → s ≤ t → q s ≤ q t := fun s t hs hst =>
          (hq 0 le_rfl).monotone () (Set.mem_Ici.2 hs) (Set.mem_Ici.2 (hs.trans hst)) hst
        have hR : ∀ t, 0 ≤ t → ∃ ε > 0, ∀ s, t ≤ s → s < t + ε → q s = q t := by
          intro t ht
          have hc := (hq 0 le_rfl).right_continuous () t ht
          have h1 := Metric.continuousWithinAt_iff.1 hc 1 one_pos
          obtain ⟨δ, hδ, h2⟩ := h1
          refine ⟨δ, hδ, fun s hs hs' => ?_⟩
          have h3 := h2 (Set.mem_Ici.2 hs) (by rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hs)]; exact sub_lt_iff_lt_add'.2 hs')
          have h6 := abs_sub_lt_iff.1 ((Real.dist_eq _ _).symm.trans_lt h3)
          have h4 : (q s : ℝ) < ((q t + 1 : ℕ) : ℝ) := (sub_lt_iff_lt_add'.1 h6.1).trans_eq (Nat.cast_succ (q t)).symm
          have h5 : (q t : ℝ) < ((q s + 1 : ℕ) : ℝ) := (sub_lt_iff_lt_add'.1 h6.2).trans_eq (Nat.cast_succ (q s)).symm
          exact le_antisymm (Nat.lt_succ_iff.1 (Nat.cast_lt.1 h4)) (Nat.lt_succ_iff.1 (Nat.cast_lt.1 h5))
        have hLL : ∀ s0 t : ℝ, ∀ m : ℕ, s0 < t → (∀ s, s0 ≤ s → s < t → q s = m) →
            Function.leftLim (fun s : ℝ => (q s : ℝ)) t = m := by
          intro s0 t m hst hc
          apply leftLim_eq_of_tendsto
          apply tendsto_const_nhds.congr'
          filter_upwards [Ioo_mem_nhdsLT hst] with s hs
          rw [hc s hs.1.le hs.2]
        have hL : ∀ t, 0 < t → ∃ s0, 0 ≤ s0 ∧ s0 < t ∧ ∀ s, s0 ≤ s → s < t → q s = q s0 := by
          intro t ht
          obtain ⟨n, ⟨s0, ⟨hs0, hs0t⟩, hn⟩, hmax⟩ : ∃ n, (∃ s0, (0 ≤ s0 ∧ s0 < t) ∧ q s0 = n) ∧
              ∀ s, 0 ≤ s → s < t → q s ≤ n := by
            have hb : ∃ N, ∀ s, 0 ≤ s → s < t → q s ≤ N := ⟨q t, fun s h1 h2 => qm s t h1 h2.le⟩
            classical
            refine ⟨Nat.find hb, ?_, Nat.find_spec hb⟩
            by_contra hcon
            push Not at hcon
            rcases Nat.eq_zero_or_pos (Nat.find hb) with h0 | hpos
            · have := Nat.find_spec hb 0 le_rfl ht
              exact hcon 0 ⟨le_rfl, ht⟩ (by omega)
            · refine Nat.find_min hb (m := Nat.find hb - 1) (by omega) ?_
              intro s h1 h2
              have h3 := Nat.find_spec hb s h1 h2
              have h4 := hcon s ⟨h1, h2⟩
              omega
          refine ⟨s0, hs0, hs0t, fun s h1 h2 => ?_⟩
          exact le_antisymm ((hmax s (hs0.trans h1) h2).trans_eq hn.symm) (qm s0 s hs0 h1)
        have hU : ∀ t, 0 < t → (q t : ℝ) - Function.leftLim (fun s : ℝ => (q s : ℝ)) t ≤ 1 :=
          fun t ht => (hq t ht.le).unit_jumps () t ht le_rfl
        -- no jump at s when constant just before and at s
        have hNJ : ∀ T s0 s, s0 < s → (∀ r, s0 ≤ r → r < s → q r = q s) → s ∉ jumps T ω i := by
          intro T s0 s hs hc hmem
          have := ((hJ T s).1 hmem).2.2
          rw [hLL s0 s (q s) hs hc, sub_self] at this
          exact zero_ne_one this
        have key : ∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → q t = n → (jumps t ω i).Finite ∧ (jumps t ω i).ncard = n := by
          intro n
          induction n with
          | zero =>
            intro t ht hqt
            have he : jumps t ω i = ∅ := by
              ext s
              simp only [Set.mem_empty_iff_false, iff_false]
              intro hs
              have hs' := (hJ t s).1 hs
              refine hNJ t 0 s hs'.1 (fun r h1 h2 => ?_) hs
              have := qm r t h1 (h2.le.trans hs'.2.1)
              have h3 := qm s t hs'.1.le hs'.2.1
              rw [hqt] at this h3
              exact (Nat.le_zero.1 this).trans (Nat.le_zero.1 h3).symm
            rw [he]; simp
          | succ n ih =>
            intro t ht hqt
            obtain ⟨S, hS⟩ : ∃ S : Set ℝ, S = {s | 0 ≤ s ∧ q s = n + 1} := ⟨_, rfl⟩
            have hSmem : ∀ s, s ∈ S ↔ 0 ≤ s ∧ q s = n + 1 := fun s => by rw [hS]; rfl
            have htS : t ∈ S := (hSmem t).2 ⟨ht, hqt⟩
            have hbd : BddBelow S := ⟨0, fun s hs => ((hSmem s).1 hs).1⟩
            obtain ⟨τ, hτ⟩ : ∃ τ, τ = sInf S := ⟨_, rfl⟩
            have hτ0 : 0 ≤ τ := hτ ▸ le_csInf ⟨t, htS⟩ (fun s hs => ((hSmem s).1 hs).1)
            have hτt : τ ≤ t := hτ ▸ csInf_le hbd htS
            have hqτ : q τ = n + 1 := by
              obtain ⟨ε, hε, hc⟩ := hR τ hτ0
              obtain ⟨s, hs, hs2⟩ := exists_lt_of_csInf_lt ⟨t, htS⟩ (show sInf S < τ + ε by rw [← hτ]; exact lt_add_of_pos_right _ hε)
              have h1 : τ ≤ s := hτ ▸ csInf_le hbd hs
              rw [← hc s h1 hs2]; exact ((hSmem s).1 hs).2
            have hτpos : 0 < τ := by
              rcases hτ0.eq_or_lt with h | h
              · rw [← h, q0] at hqτ; omega
              · exact h
            obtain ⟨s0, hs0, hs0τ, hc⟩ := hL τ hτpos
            have hlim := hLL s0 τ (q s0) hs0τ hc
            have hu := hU τ hτpos
            rw [hlim, hqτ] at hu
            have h1 : q s0 ≤ n + 1 := hqτ ▸ qm s0 τ hs0 hs0τ.le
            have h2 : q s0 ≠ n + 1 := fun h => by
              have := csInf_le hbd ((hSmem s0).2 ⟨hs0, h⟩)
              rw [← hτ] at this; exact absurd this (not_le.2 hs0τ)
            have h3 : n ≤ q s0 := by
              have : ((n + 1 : ℕ) : ℝ) ≤ ((q s0 + 1 : ℕ) : ℝ) :=
                (sub_le_iff_le_add'.1 hu).trans_eq (Nat.cast_succ (q s0)).symm
              exact Nat.le_of_succ_le_succ (Nat.cast_le.1 this)
            have hqs0 : q s0 = n := le_antisymm (Nat.le_of_lt_succ (lt_of_le_of_ne h1 h2)) h3
            obtain ⟨hf, hcard⟩ := ih s0 hs0 hqs0
            have he : jumps t ω i = insert τ (jumps s0 ω i) := by
              ext s
              rw [Set.mem_insert_iff]
              constructor
              · intro hs
                have hs' := (hJ t s).1 hs
                rcases le_or_gt s s0 with h | h
                · exact Or.inr ((hJ s0 s).2 ⟨hs'.1, h, hs'.2.2⟩)
                · rcases lt_trichotomy s τ with h' | h' | h'
                  · exact absurd hs (hNJ t s0 s h (fun r hr1 hr2 => by
                      rw [hc r hr1 (hr2.trans h'), hc s h.le h']))
                  · exact Or.inl h'
                  · refine absurd hs (hNJ t τ s h' (fun r hr1 hr2 => ?_))
                    have a1 := qm τ r hτ0 hr1
                    have a2 := qm r s (hτ0.trans hr1) hr2.le
                    have a3 := qm s t hs'.1.le hs'.2.1
                    exact le_antisymm (a2) ((a3.trans_eq hqt).trans (hqτ ▸ a1))
              · rintro (rfl | hs)
                · refine (hJ t s).2 ⟨hτpos, hτt, ?_⟩
                  rw [hlim, hqτ, hqs0, Nat.cast_add, Nat.cast_one, add_sub_cancel_left]
                · have hs' := (hJ s0 s).1 hs
                  exact (hJ t s).2 ⟨hs'.1, hs'.2.1.trans (hs0τ.le.trans hτt), hs'.2.2⟩
            have hni : τ ∉ jumps s0 ω i := fun h => by
              exact absurd ((hJ s0 τ).1 h).2.1 (not_le.2 hs0τ)
            rw [he]
            exact ⟨hf.insert τ, by rw [Set.ncard_insert_of_notMem hni hf, hcard]⟩
        refine ⟨?_, ?_, ?_⟩
        · intro T
          rcases le_or_gt 0 T with h | h
          · exact (key _ T h rfl).1
          · have he : jumps T ω i = ∅ := by
              ext s
              simp only [Set.mem_empty_iff_false, iff_false]
              intro hs
              have hs' := (hJ T s).1 hs
              exact absurd (hs'.1.trans_le hs'.2.1) (not_lt.2 h.le)
            rw [he]; exact Set.finite_empty
        · intro t
          have h1 : X t ω i = q t := by simp only [X, hqv]
          rw [h1, (key _ t t.coe_nonneg rfl).2]
        · intro t
          rcases eq_or_ne t 0 with rfl | ht
          · have he : jumps ((0 : ℝ≥0) : ℝ) ω i ∩ Iio ((0 : ℝ≥0) : ℝ) = ∅ := by
              ext s
              simp only [Set.mem_empty_iff_false, iff_false]
              rintro ⟨hs, hs2⟩
              have hs' := (hJ _ s).1 hs
              have hs3 : s < ((0 : ℝ≥0) : ℝ) := hs2
              exact lt_irrefl _ (hs'.1.trans_eq' (NNReal.coe_zero) |>.trans hs3)
            rw [he]; simp [preX]
          · have htpos : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht)
            obtain ⟨s0, hs0, hs0t, hc⟩ := hL t htpos
            have hlim := hLL s0 t (q s0) hs0t hc
            have h1 : preX t ω i = q s0 := by
              simp only [preX, hqv, if_neg ht, hlim, Nat.floor_natCast]
            have he : jumps (t : ℝ) ω i ∩ Iio (t : ℝ) = jumps s0 ω i := by
              ext s
              constructor
              · rintro ⟨hs, hs2⟩
                have hs' := (hJ _ s).1 hs
                have hs3 : s < (t : ℝ) := hs2
                rcases le_or_gt s s0 with h | h
                · exact (hJ s0 s).2 ⟨hs'.1, h, hs'.2.2⟩
                · exact absurd hs (hNJ t s0 s h (fun r hr1 hr2 => by
                    rw [hc r hr1 (hr2.trans hs3), hc s h.le hs3]))
              · intro hs
                have hs' := (hJ _ s).1 hs
                exact ⟨(hJ _ s).2 ⟨hs'.1, hs'.2.1.trans hs0t.le, hs'.2.2⟩,
                  Set.mem_Iio.2 (hs'.2.1.trans_lt hs0t)⟩
            rw [h1, he, (key _ s0 hs0 rfl).2]
      have REAL : ∀ (s t v0 B : ℝ) (c v : ℝ → ℝ), s ≤ t → Measurable c → Measurable v →
          (∀ r, |c r| ≤ B) → (∀ r, |v r| ≤ B) →
          Real.exp (-∫ r in s..t, c r) * (v0 + ∫ r in s..t, v r) - v0 =
            ∫ r in s..t, Real.exp (-∫ q in s..r, c q) * (v r - c r * (v0 + ∫ q in s..r, v q)) := by
        clear hG G ODE1 ODE2 PATHS
        intro s t v0 B c v hst hc hv hcB hvB
        have hB : 0 ≤ B := (abs_nonneg _).trans (hcB 0)
        have hii : ∀ f : ℝ → ℝ, Measurable f → (∀ r, |f r| ≤ B) → ∀ p q : ℝ,
            IntervalIntegrable f volume p q := by
          intro f hf hfB p q
          refine (intervalIntegrable_const (c := B)).mono_fun hf.aestronglyMeasurable ?_
          refine Eventually.of_forall fun r => ?_
          simpa [abs_of_nonneg hB] using hfB r
        have hlip : ∀ f : ℝ → ℝ, Measurable f → (∀ r, |f r| ≤ B) → 
            LipschitzWith (Real.toNNReal B) (fun r => ∫ q in s..r, f q) := by
          intro f hf hfB
          refine LipschitzWith.of_dist_le_mul fun x y => ?_
          rw [Real.dist_eq, Real.dist_eq, intervalIntegral.integral_interval_sub_left (hii f hf hfB _ _)
            (hii f hf hfB _ _), Real.coe_toNNReal B hB]
          rw [← Real.norm_eq_abs (∫ q in y..x, f q)]
          exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => by rw [Real.norm_eq_abs]; exact hfB r)
        have hder : ∀ f : ℝ → ℝ, Measurable f → (∀ r, |f r| ≤ B) →
            ∀ᵐ x, x ∈ uIcc s t → HasDerivAt (fun r => ∫ q in s..r, f q) (f x) x := by
          intro f hf hfB
          filter_upwards [(hii f hf hfB s t).ae_hasDerivAt_integral] with x hx hxm
          exact hx hxm s left_mem_uIcc
        have hexp : ContDiff ℝ 1 Real.exp := Real.contDiff_exp
        have hlF := (hlip c hc hcB).neg
        have hEac : AbsolutelyContinuousOnInterval (fun r => Real.exp (-∫ q in s..r, c q)) s t := by
          obtain ⟨K, hK⟩ := hexp.contDiffOn.exists_lipschitzOnWith (by decide)
            (convex_Icc (-(B * (t - s))) (B * (t - s))) isCompact_Icc
          refine LipschitzOnWith.absolutelyContinuousOnInterval
            (hK.comp (hlF.lipschitzOnWith (s := uIcc s t)) ?_)
          intro r hr
          rw [uIcc_of_le hst] at hr
          have h1 : |∫ q in s..r, c q| ≤ B * |r - s| := by
            rw [← Real.norm_eq_abs (∫ q in s..r, c q)]
            exact intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => by rw [Real.norm_eq_abs]; exact hcB r)
          rw [abs_of_nonneg (sub_nonneg.2 hr.1)] at h1
          have h2 : B * (r - s) ≤ B * (t - s) := mul_le_mul_of_nonneg_left (by linarith [hr.2]) hB
          have h3 := abs_le.1 (h1.trans h2)
          constructor <;> simp only [] <;> linarith [h3.1, h3.2]
        have hUac : AbsolutelyContinuousOnInterval (fun r => v0 + ∫ q in s..r, v q) s t := by
          refine LipschitzOnWith.absolutelyContinuousOnInterval (K := Real.toNNReal B) ?_
          refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y => ?_)
          rw [dist_add_left]
          exact (hlip v hv hvB).dist_le_mul x y
        have key := hEac.integral_deriv_mul_eq_sub hUac
        simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero, one_mul, add_zero] at key
        rw [← key]
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [hder c hc hcB, hder v hv hvB] with x h1 h2 hx
        have hx' := uIoc_subset_uIcc hx
        have d1 : HasDerivAt (fun r => Real.exp (-∫ q in s..r, c q)) _ x := (h1 hx').neg.exp
        have d2 : HasDerivAt (fun r => v0 + ∫ q in s..r, v q) _ x := (h2 hx').const_add v0
        rw [d1.deriv, d2.deriv]
        simp only [Pi.neg_apply]
        ring
      have PATHSUM : ∀ (h l u rate B : ℝ) (J0 J1 : Finset ℝ) (a b : ℝ → ℝ) (V w : ℝ → State → ℝ) (x : State),
          0 ≤ h → 0 < l → 0 < rate → (∀ t ∈ J0, 0 < t ∧ t ≤ h) → (∀ t ∈ J1, 0 < t ∧ t ≤ h) → Disjoint J0 J1 →
          Measurable a → Measurable b → (∀ t, l ≤ a t ∧ a t ≤ u) → (∀ t, l ≤ b t ∧ b t ≤ u) →
          (∀ y, Measurable (fun t => w t y)) → (∀ y, ∃ B, ∀ t, |w t y| ≤ B) →
          (∀ y s t, 0 ≤ s → s ≤ t → t ≤ h → V t y - V s y = ∫ r in s..t, w r y) →
          ∀ (L : ℝ → ℝ) (Y : ℝ → State),
          (∀ t, L t = Real.exp ((∑ s ∈ J0 with s < t, Real.log (a s / rate)) +
             (∑ s ∈ J1 with s < t, Real.log (b s / rate)) - ∫ s in Icc (0:ℝ) t, ((a s - rate) + (b s - rate)))) →
          (∀ t, Y t = fun j => x j + (if j = 0 then (J0.filter (· < t)).card else (J1.filter (· < t)).card)) →
          Real.exp ((∑ s ∈ J0, Real.log (a s / rate)) +
             (∑ s ∈ J1, Real.log (b s / rate)) - ∫ s in Icc (0:ℝ) h, ((a s - rate) + (b s - rate))) *
            V h (fun j => x j + (if j = 0 then J0.card else J1.card)) =
          V 0 x + (∑ t ∈ J0, L t * (a t / rate * V t (Function.update (Y t) 0 (Y t 0 + 1)) - V t (Y t)))
            + (∑ t ∈ J1, L t * (b t / rate * V t (Function.update (Y t) 1 (Y t 1 + 1)) - V t (Y t)))
            + ∫ t in Icc (0:ℝ) h, L t * (w t (Y t) - ((a t - rate) + (b t - rate)) * V t (Y t)) := by
        clear hG G ODE1 ODE2 PATHS
        intro h l u rate B J0 J1 a b V w x hh hl hr hJ0 hJ1 hdis hma hmb ha hb hwm hwb hV L Y hL hY
        have hcm : Measurable (fun s => (a s - rate) + (b s - rate)) :=
          (hma.sub_const _).add (hmb.sub_const _)
        obtain ⟨c, hcdef⟩ : ∃ c : ℝ → ℝ, c = fun s => (a s - rate) + (b s - rate) := ⟨_, rfl⟩
        have hcm' : Measurable c := hcdef ▸ hcm
        have hcb : ∀ r, |c r| ≤ 2 * (u + rate) := by
          intro r
          rw [hcdef, abs_le]
          have := ha r
          have := hb r
          constructor <;> dsimp only <;> linarith
        have hint : ∀ (f : ℝ → ℝ) (B : ℝ), Measurable f → (∀ r, |f r| ≤ B) → ∀ p q : ℝ,
            IntervalIntegrable f volume p q := by
          intro f B hf hB p q
          refine IntervalIntegrable.mono_fun (intervalIntegrable_const (c := B)) hf.aestronglyMeasurable ?_
          refine Filter.Eventually.of_forall fun r => ?_
          simp only [Real.norm_eq_abs]
          exact (hB r).trans (le_abs_self B)
        have hcint := hint c _ hcm' hcb
        have hIcc : ∀ r, 0 ≤ r → ∫ s in Icc (0:ℝ) r, ((a s - rate) + (b s - rate)) = ∫ s in (0:ℝ)..r, c s := by
          intro r h0
          rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h0, hcdef]
        obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => L t * (w t (Y t) - ((a t - rate) + (b t - rate)) * V t (Y t)) :=
          ⟨_, rfl⟩
        obtain ⟨d0, hd0⟩ : ∃ d : ℝ → ℝ, d = fun t => L t * (a t / rate * V t (Function.update (Y t) 0 (Y t 0 + 1)) - V t (Y t)) :=
          ⟨_, rfl⟩
        obtain ⟨d1, hd1⟩ : ∃ d : ℝ → ℝ, d = fun t => L t * (b t / rate * V t (Function.update (Y t) 1 (Y t 1 + 1)) - V t (Y t)) :=
          ⟨_, rfl⟩
        obtain ⟨Sg, hSg⟩ : ∃ S : Finset ℝ → Finset ℝ → ℝ, S = fun A0 A1 =>
            (∑ s ∈ A0, Real.log (a s / rate)) + (∑ s ∈ A1, Real.log (b s / rate)) := ⟨_, rfl⟩
        obtain ⟨Yc, hYc⟩ : ∃ Yc : Finset ℝ → Finset ℝ → State, Yc = fun A0 A1 =>
            fun j => x j + (if j = 0 then A0.card else A1.card) := ⟨_, rfl⟩
        have hLS : ∀ t, 0 ≤ t → L t = Real.exp (Sg (J0.filter (· < t)) (J1.filter (· < t)) - ∫ s in (0:ℝ)..t, c s) := by
          intro t ht
          rw [hL, hIcc t ht, hSg]
        have hYS : ∀ t, Y t = Yc (J0.filter (· < t)) (J1.filter (· < t)) := by
          intro t
          rw [hY, hYc]
        -- jump-free evolution
        have KEY : ∀ (s t : ℝ) (A0 A1 : Finset ℝ), 0 ≤ s → s ≤ t → t ≤ h →
            (∀ r ∈ Ioc s t, J0.filter (· < r) = A0 ∧ J1.filter (· < r) = A1) →
            IntervalIntegrable g volume s t ∧
            Real.exp (Sg A0 A1 - ∫ q in (0:ℝ)..t, c q) * V t (Yc A0 A1) =
              Real.exp (Sg A0 A1 - ∫ q in (0:ℝ)..s, c q) * V s (Yc A0 A1) + ∫ r in s..t, g r := by
          intro s t A0 A1 hs hst hth hA
          obtain ⟨y, hy⟩ : ∃ y, y = Yc A0 A1 := ⟨_, rfl⟩
          obtain ⟨S, hS⟩ : ∃ S, S = Sg A0 A1 := ⟨_, rfl⟩
          obtain ⟨Bw, hBw⟩ := hwb y
          have hwint := hint (fun t => w t y) Bw (hwm y) hBw
          obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun r => Real.exp (S - ∫ q in (0:ℝ)..s, c q) *
            (Real.exp (-∫ q in s..r, c q) * (w r y - c r * (V s y + ∫ q in s..r, w q y))) := ⟨_, rfl⟩
          have hgF : ∀ r ∈ Ioc s t, g r = F r := by
            intro r hr'
            have hr0 : 0 ≤ r := hs.trans hr'.1.le
            have h1 := hLS r hr0
            have h2 := hYS r
            rw [(hA r hr').1, (hA r hr').2] at h1 h2
            have h3 : V r y = V s y + ∫ q in s..r, w q y := by
              have := hV y s r hs hr'.1.le (hr'.2.trans hth)
              linarith
            have h4 : (∫ q in (0:ℝ)..r, c q) = (∫ q in (0:ℝ)..s, c q) + ∫ q in s..r, c q :=
              (intervalIntegral.integral_add_adjacent_intervals (hcint _ _) (hcint _ _)).symm
            rw [hg, hF]
            dsimp only
            rw [h1, h2, ← hy, ← hS, h3, h4, ← mul_assoc, ← Real.exp_add, hcdef]
            congr 2
            ring
          have hFint : IntervalIntegrable F volume s t := by
            rw [hF]
            refine IntervalIntegrable.const_mul ?_ _
            simp_rw [mul_comm (Real.exp _)]
            refine IntervalIntegrable.mul_continuousOn ?_ ?_
            · refine (hwint s t).sub ?_
              refine IntervalIntegrable.mul_continuousOn (hcint s t) ?_
              exact (continuous_const.add (intervalIntegral.continuous_primitive hwint s)).continuousOn
            · exact (Real.continuous_exp.comp (intervalIntegral.continuous_primitive hcint s).neg).continuousOn
          have hio : Set.uIoc s t = Ioc s t := Set.uIoc_of_le hst
          have hgint : IntervalIntegrable g volume s t := by
            refine hFint.congr ?_
            rw [hio]
            exact fun r hr' => (hgF r hr').symm
          refine ⟨hgint, ?_⟩
          have hgi : ∫ r in s..t, g r = ∫ r in s..t, F r := by
            rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
            exact setIntegral_congr_fun measurableSet_Ioc hgF
          have hR := REAL s t (V s y) (max (2 * (u + rate)) Bw) c (fun t => w t y) hst hcm' (hwm y)
            (fun r => (hcb r).trans (le_max_left _ _)) (fun r => (hBw r).trans (le_max_right _ _))
          have h3 : V t y = V s y + ∫ q in s..t, w q y := by
            have := hV y s t hs hst hth
            linarith
          have h4 : (∫ q in (0:ℝ)..t, c q) = (∫ q in (0:ℝ)..s, c q) + ∫ q in s..t, c q :=
            (intervalIntegral.integral_add_adjacent_intervals (hcint _ _) (hcint _ _)).symm
          rw [hgi, hF, intervalIntegral.integral_const_mul, ← hR, ← hy, ← hS, h4, h3]
          have : Real.exp (S - ((∫ q in (0:ℝ)..s, c q) + ∫ q in s..t, c q)) =
              Real.exp (S - ∫ q in (0:ℝ)..s, c q) * Real.exp (-∫ q in s..t, c q) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [this]
          ring
        -- crossing a jump
        have JUMP : ∀ t, 0 ≤ t → t ≤ h →
            L t * V t (Y t) = V 0 x + (∑ s ∈ J0.filter (· < t), d0 s) + (∑ s ∈ J1.filter (· < t), d1 s)
              + ∫ r in (0:ℝ)..t, g r →
            Real.exp (Sg (J0.filter (· ≤ t)) (J1.filter (· ≤ t)) - ∫ q in (0:ℝ)..t, c q) *
              V t (Yc (J0.filter (· ≤ t)) (J1.filter (· ≤ t))) =
            V 0 x + (∑ s ∈ J0.filter (· ≤ t), d0 s) + (∑ s ∈ J1.filter (· ≤ t), d1 s)
              + ∫ r in (0:ℝ)..t, g r := by
          intro t ht hth hpre
          have hins : ∀ J : Finset ℝ, t ∈ J → J.filter (· ≤ t) = insert t (J.filter (· < t)) := by
            intro J htJ
            ext r
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨h1, h2⟩
              rcases h2.lt_or_eq with h3 | h3
              · exact Or.inr ⟨h1, h3⟩
              · exact Or.inl h3
            · rintro (h1 | ⟨h1, h2⟩)
              · exact ⟨h1 ▸ htJ, h1.le⟩
              · exact ⟨h1, h2.le⟩
          have hno : ∀ J : Finset ℝ, t ∉ J → J.filter (· ≤ t) = J.filter (· < t) := by
            intro J htJ
            ext r
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨h1, h2⟩
              refine ⟨h1, lt_of_le_of_ne h2 ?_⟩
              rintro rfl
              exact htJ h1
            · rintro ⟨h1, h2⟩
              exact ⟨h1, h2.le⟩
          have hnot : ∀ J : Finset ℝ, t ∉ J.filter (· < t) := by
            intro J; simp
          by_cases h0 : t ∈ J0
          · have h1 : t ∉ J1 := fun h1 => Finset.disjoint_left.mp hdis h0 h1
            rw [hins J0 h0, hno J1 h1, Finset.sum_insert (hnot J0)]
            have e1 : Sg (insert t (J0.filter (· < t))) (J1.filter (· < t)) =
                Real.log (a t / rate) + Sg (J0.filter (· < t)) (J1.filter (· < t)) := by
              rw [hSg]; dsimp only
              rw [Finset.sum_insert (hnot J0)]; ring
            have e2 : Yc (insert t (J0.filter (· < t))) (J1.filter (· < t)) =
                Function.update (Y t) 0 (Y t 0 + 1) := by
              rw [hYS t, hYc]
              funext j
              fin_cases j
              · simp [Finset.card_insert_of_notMem (hnot J0)]; ring
              · simp
            have e3 : Real.exp (Real.log (a t / rate) + Sg (J0.filter (· < t)) (J1.filter (· < t))
                - ∫ q in (0:ℝ)..t, c q) = a t / rate * L t := by
              rw [hLS t ht, add_sub_assoc, Real.exp_add, Real.exp_log (div_pos (hl.trans_le (ha t).1) hr)]
            rw [e1, e2, e3]
            have : d0 t = L t * (a t / rate * V t (Function.update (Y t) 0 (Y t 0 + 1)) - V t (Y t)) := by
              rw [hd0]
            rw [this]
            linear_combination hpre
          · by_cases h1 : t ∈ J1
            · rw [hins J1 h1, hno J0 h0, Finset.sum_insert (hnot J1)]
              have e1 : Sg (J0.filter (· < t)) (insert t (J1.filter (· < t))) =
                  Real.log (b t / rate) + Sg (J0.filter (· < t)) (J1.filter (· < t)) := by
                rw [hSg]; dsimp only
                rw [Finset.sum_insert (hnot J1)]; ring
              have e2 : Yc (J0.filter (· < t)) (insert t (J1.filter (· < t))) =
                  Function.update (Y t) 1 (Y t 1 + 1) := by
                rw [hYS t, hYc]
                funext j
                fin_cases j
                · simp
                · simp [Finset.card_insert_of_notMem (hnot J1)]; ring
              have e3 : Real.exp (Real.log (b t / rate) + Sg (J0.filter (· < t)) (J1.filter (· < t))
                  - ∫ q in (0:ℝ)..t, c q) = b t / rate * L t := by
                rw [hLS t ht, add_sub_assoc, Real.exp_add, Real.exp_log (div_pos (hl.trans_le (hb t).1) hr)]
              rw [e1, e2, e3]
              have : d1 t = L t * (b t / rate * V t (Function.update (Y t) 1 (Y t 1 + 1)) - V t (Y t)) := by
                rw [hd1]
              rw [this]
              linear_combination hpre
            · rw [hno J0 h0, hno J1 h1, ← hLS t ht, ← hYS t]
              exact hpre
        have IND : ∀ n : ℕ, ∀ t, 0 ≤ t → t ≤ h → ((J0 ∪ J1).filter (· < t)).card ≤ n →
            IntervalIntegrable g volume 0 t ∧
            L t * V t (Y t) = V 0 x + (∑ s ∈ J0.filter (· < t), d0 s) + (∑ s ∈ J1.filter (· < t), d1 s)
              + ∫ r in (0:ℝ)..t, g r := by
          intro n
          induction n with
          | zero =>
            intro t ht hth hcard
            have hemp : (J0 ∪ J1).filter (· < t) = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
            have he : ∀ r, r ≤ t → J0.filter (· < r) = ∅ ∧ J1.filter (· < r) = ∅ := by
              intro r hrt
              constructor
              · refine Finset.filter_eq_empty_iff.mpr fun q hq hqr => ?_
                exact Finset.filter_eq_empty_iff.mp hemp (Finset.mem_union_left _ hq) (hqr.trans_le hrt)
              · refine Finset.filter_eq_empty_iff.mpr fun q hq hqr => ?_
                exact Finset.filter_eq_empty_iff.mp hemp (Finset.mem_union_right _ hq) (hqr.trans_le hrt)
            obtain ⟨hi, hk⟩ := KEY 0 t ∅ ∅ le_rfl ht hth (fun r hr' => he r hr'.2)
            refine ⟨hi, ?_⟩
            rw [hLS t ht, hYS t, (he t le_rfl).1, (he t le_rfl).2, hk]
            have hYe : Yc ∅ ∅ = x := by rw [hYc]; funext j; simp
            have hSe : Sg ∅ ∅ = 0 := by rw [hSg]; simp
            rw [hYe, hSe]
            simp
          | succ n ih =>
            intro t ht hth hcard
            by_cases hemp : ((J0 ∪ J1).filter (· < t)).Nonempty
            · obtain ⟨p, hp⟩ : ∃ p, p = ((J0 ∪ J1).filter (· < t)).max' hemp := ⟨_, rfl⟩
              have hpm : p ∈ (J0 ∪ J1).filter (· < t) := hp ▸ Finset.max'_mem _ hemp
              have hpmax : ∀ q ∈ (J0 ∪ J1).filter (· < t), q ≤ p := fun q hq => hp ▸ Finset.le_max' _ q hq
              have hpt : p < t := (Finset.mem_filter.mp hpm).2
              have hp0 : 0 ≤ p := by
                rcases Finset.mem_union.mp (Finset.mem_filter.mp hpm).1 with hq | hq
                · exact (hJ0 p hq).1.le
                · exact (hJ1 p hq).1.le
              have hph : p ≤ h := hpt.le.trans hth
              have hlt : ((J0 ∪ J1).filter (· < p)).card < ((J0 ∪ J1).filter (· < t)).card := by
                refine Finset.card_lt_card ?_
                refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨p, hpm, by simp⟩
                intro q hq
                rw [Finset.mem_filter] at hq ⊢
                exact ⟨hq.1, hq.2.trans hpt⟩
              obtain ⟨hi0, hpre⟩ := ih p hp0 hph (by omega)
              have hpost := JUMP p hp0 hph hpre
              have hfe : ∀ J : Finset ℝ, J ⊆ J0 ∪ J1 → ∀ r ∈ Ioc p t, J.filter (· < r) = J.filter (· ≤ p) := by
                intro J hJ r hr'
                ext q
                simp only [Finset.mem_filter]
                constructor
                · rintro ⟨h1, h2⟩
                  exact ⟨h1, hpmax q (Finset.mem_filter.mpr ⟨hJ h1, h2.trans_le hr'.2⟩)⟩
                · rintro ⟨h1, h2⟩
                  exact ⟨h1, h2.trans_lt hr'.1⟩
              have hf0 := hfe J0 Finset.subset_union_left
              have hf1 := hfe J1 Finset.subset_union_right
              obtain ⟨hi, hk⟩ := KEY p t (J0.filter (· ≤ p)) (J1.filter (· ≤ p)) hp0 hpt.le hth
                (fun r hr' => ⟨hf0 r hr', hf1 r hr'⟩)
              refine ⟨hi0.trans hi, ?_⟩
              rw [hLS t ht, hYS t, hf0 t ⟨hpt, le_rfl⟩, hf1 t ⟨hpt, le_rfl⟩, hk, hpost,
                ← intervalIntegral.integral_add_adjacent_intervals hi0 hi]
              ring
            · refine ih t ht hth ?_
              rw [Finset.not_nonempty_iff_eq_empty.mp hemp]
              simp
        obtain ⟨-, hpre⟩ := IND _ h hh le_rfl le_rfl
        have hfin := JUMP h hh le_rfl hpre
        have e0 : J0.filter (· ≤ h) = J0 := Finset.filter_true_of_mem fun q hq => (hJ0 q hq).2
        have e1 : J1.filter (· ≤ h) = J1 := Finset.filter_true_of_mem fun q hq => (hJ1 q hq).2
        rw [e0, e1] at hfin
        rw [hIcc h hh, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh]
        rw [hSg, hYc, hg, hd0, hd1] at hfin
        exact hfin
      have INDEP : ∀ G : Game, G.Standing → ∀ s t : ℝ≥0, s ≤ t → ∀ A : Set Sample,
          MeasurableSet[naturalFiltration s] A → ∀ i,
          ∫⁻ ω in A, ((X t ω i - X s ω i : ℕ) : ℝ≥0∞) ∂G.P = ENNReal.ofReal (G.rate * (t - s)) * G.P A := by
        clear hG G ODE1 ODE2 PATHS REAL PATHSUM
        intro G hG s t hst A hA i
        obtain ⟨-, -, -, hr, -, hPr, hP⟩ := hG
        -- Poisson mean
        have hmean : ∀ r : ℝ≥0, ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂(poissonMeasure r) = r := by
          intro r
          rw [poissonMeasure, lintegral_sum_measure]
          simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
          rw [tsum_eq_zero_add' ENNReal.summable]
          have h1 : ∀ n : ℕ, ENNReal.ofReal (Real.exp (-r) * r ^ (n+1) / ((n+1).factorial : ℝ)) * ((n + 1 : ℕ) : ℝ≥0∞)
              = (r : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-r) * r ^ n / (n.factorial : ℝ)) := by
            intro n
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_coe_nnreal,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [Nat.factorial_succ]
            push_cast
            have : (n.factorial : ℝ) ≠ 0 := by positivity
            have : (n : ℝ) + 1 ≠ 0 := by positivity
            field_simp
            ring
          simp only [h1]
          rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            (hasSum_one_poissonMeasure r).summable, (hasSum_one_poissonMeasure r).tsum_eq]
          simp
        have hXm : ∀ u, Measurable (X u) := fun u =>
          Measurable.of_comap_le (le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) u)
        have hXi : ∀ u j, Measurable (fun ω => X u ω j) := fun u j => (measurable_pi_iff.1 (hXm u)) j
        have hX0 : ∀ ω j, X 0 ω j = 0 := fun ω j => ((ω j).2 0 le_rfl).zero ()
        have hXmono : ∀ ω j (u v : ℝ≥0), u ≤ v → X u ω j ≤ X v ω j := fun ω j u v huv =>
          ((ω j).2 0 le_rfl).monotone () u.2 v.2 huv
        have hfm : Measurable (fun ω => ((X t ω i - X s ω i : ℕ) : ℝ≥0∞)) := by
          exact (measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞))).comp ((hXi t i).sub (hXi s i))
        -- cylinder sets
        have hcyl : ∀ T : Finset ℝ≥0, (∀ u ∈ T, u ≤ s) → ∀ B : ℝ≥0 → Set (Fin 2 → ℕ),
            ∫⁻ ω in ⋂ u ∈ T, (X u) ⁻¹' (B u), ((X t ω i - X s ω i : ℕ) : ℝ≥0∞) ∂G.P =
              ENNReal.ofReal (G.rate * (t - s)) * G.P (⋂ u ∈ T, (X u) ⁻¹' (B u)) := by
          intro T hT B
          set T' : Finset ℝ≥0 := insert 0 (insert s T) with hT'
          obtain ⟨k, hk⟩ : ∃ k, T'.card = k := ⟨_, rfl⟩
          have hk0 : 0 < k := by rw [← hk]; exact Finset.card_pos.2 ⟨0, Finset.mem_insert_self _ _⟩
          have hT's : ∀ u ∈ T', u ≤ s := by
            intro u hu
            simp only [hT', Finset.mem_insert] at hu
            rcases hu with rfl | rfl | hu
            · exact zero_le
            · exact le_rfl
            · exact hT u hu
          set e := T'.orderEmbOfFin hk with he
          have he0 : e ⟨0, hk0⟩ = 0 := by
            obtain ⟨p, hp⟩ : ∃ p, e p = 0 := by
              have : (0 : ℝ≥0) ∈ Set.range e := by
                rw [he, Finset.range_orderEmbOfFin]; exact Finset.mem_insert_self _ _
              exact this
            have : e ⟨0, hk0⟩ ≤ e p := e.monotone (Fin.mk_le_of_le_val (Nat.zero_le _))
            rw [hp] at this
            exact le_antisymm this zero_le
          have hk1 : k - 1 < k := Nat.sub_lt hk0 Nat.one_pos
          have hel : e ⟨k-1, hk1⟩ = s := by
            obtain ⟨p, hp⟩ : ∃ p, e p = s := by
              have : s ∈ Set.range e := by
                rw [he, Finset.range_orderEmbOfFin]
                exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              exact this
            have h1 : e p ≤ e ⟨k-1, hk1⟩ := e.monotone (Fin.le_def.2 (Nat.le_sub_one_of_lt p.2))
            rw [hp] at h1
            exact le_antisymm (hT's _ (Finset.orderEmbOfFin_mem _ _ _)) h1
          set τ : Fin (k+1) → ℝ≥0 := fun j => if h : j.val < k then e ⟨j.val, h⟩ else t with hτ
          have hτm : Monotone τ := by
            intro p q hpq
            have hpq' : p.val ≤ q.val := hpq
            by_cases h2 : q.val < k
            · have h1 : p.val < k := lt_of_le_of_lt hpq' h2
              have e1 : τ p = e ⟨p.val, h1⟩ := dif_pos h1
              have e2 : τ q = e ⟨q.val, h2⟩ := dif_pos h2
              rw [e1, e2]
              exact e.monotone (Fin.le_def.2 hpq')
            · have e2 : τ q = t := dif_neg h2
              rw [e2]
              by_cases h1 : p.val < k
              · have e1 : τ p = e ⟨p.val, h1⟩ := dif_pos h1
                rw [e1]
                exact (hT's _ (Finset.orderEmbOfFin_mem _ _ _)).trans hst
              · exact le_of_eq (dif_neg h1)
          set Inc : Sample → (Fin k × Fin 2 → ℕ) := fun ω j =>
            X (τ j.1.succ) ω j.2 - X (τ j.1.castSucc) ω j.2 with hInc
          have hmap := hP k τ hτm
          rw [← hInc] at hmap
          have hIm : Measurable Inc := by
            refine measurable_pi_lambda _ fun j => ?_
            exact (hXi _ _).sub (hXi _ _)
          set q0 : Fin k × Fin 2 := (⟨k-1, hk1⟩, i) with hq0
          set S : Finset (Fin k × Fin 2) := Finset.univ.erase q0 with hS
          have hk2 : ¬ (k - 1 + 1 < k) := fun h => absurd (Nat.sub_add_cancel hk0) (Nat.ne_of_lt h)
          have h1 : τ (Fin.succ ⟨k-1, hk1⟩) = t := dif_neg hk2
          have h2 : τ (Fin.castSucc ⟨k-1, hk1⟩) = s := (dif_pos hk1).trans hel
          have hf : ∀ ω, X t ω i - X s ω i = Inc ω q0 := by
            intro ω
            simp only [hInc, hq0, h1, h2]
          have hΦ : ∀ p (hp : p < k), ∃ Φ : (S → ℕ) → (Fin 2 → ℕ), ∀ ω, X (e ⟨p, hp⟩) ω =
              Φ (fun q => Inc ω q) := by
            intro p
            induction p with
            | zero =>
              intro hp
              refine ⟨fun _ _ => 0, fun ω => ?_⟩
              rw [he0]; funext j; exact hX0 ω j
            | succ p ih =>
              intro hp
              have hp' : p < k := Nat.lt_of_succ_lt hp
              obtain ⟨Φ, hΦ⟩ := ih hp'
              have hmem : ∀ j : Fin 2, ((⟨p, hp'⟩ : Fin k), j) ∈ S := by
                intro j
                refine Finset.mem_erase.2 ⟨fun h => ?_, Finset.mem_univ _⟩
                have h' : p = k - 1 := congrArg (fun z : Fin k × Fin 2 => z.1.val) h
                exact Nat.ne_of_lt (Nat.lt_sub_of_add_lt hp) h'
              refine ⟨fun y j => Φ y j + y ⟨_, hmem j⟩, fun ω => ?_⟩
              funext j
              show X (e ⟨p + 1, hp⟩) ω j = Φ (fun q => Inc ω q) j + Inc ω (⟨p, hp'⟩, j)
              rw [← hΦ ω]
              have h1 : τ (Fin.succ ⟨p, hp'⟩) = e ⟨p+1, hp⟩ := dif_pos hp
              have h2 : τ (Fin.castSucc ⟨p, hp'⟩) = e ⟨p, hp'⟩ := dif_pos hp'
              simp only [hInc, h1, h2]
              have := hXmono ω j (e ⟨p, hp'⟩) (e ⟨p+1, hp⟩) (e.monotone (Fin.le_def.2 (Nat.le_succ p)))
              exact (Nat.add_sub_cancel' this).symm
          obtain ⟨B', hB'⟩ : ∃ B' : Set (S → ℕ), (⋂ u ∈ T, (X u) ⁻¹' (B u)) = {ω | (fun q : S => Inc ω q) ∈ B'} := by
            have hu : ∀ u ∈ T, ∃ B' : Set (S → ℕ), (X u) ⁻¹' (B u) = {ω | (fun q : S => Inc ω q) ∈ B'} := by
              intro u hu
              obtain ⟨p, hp⟩ : ∃ p, e p = u := by
                have : u ∈ Set.range e := by
                  rw [he, Finset.range_orderEmbOfFin]
                  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
                exact this
              obtain ⟨Φ, hΦ'⟩ := hΦ p.1 p.2
              refine ⟨Φ ⁻¹' (B u), ?_⟩
              ext ω
              have := hΦ' ω
              simp only [Fin.eta, hp] at this
              simp only [mem_preimage, mem_ofPred_eq, this]
            choose! F hF using hu
            refine ⟨⋂ u ∈ T, F u, ?_⟩
            ext ω
            simp only [mem_iInter, mem_ofPred_eq]
            refine forall_congr' fun u => forall_congr' fun hu => ?_
            rw [hF u hu]; rfl
          set π := Measure.pi (fun j : Fin k × Fin 2 => poissonMeasure
            (Real.toNNReal (G.rate * ((τ j.1.succ : ℝ) - (τ j.1.castSucc : ℝ))))) with hπ
          have hB'm : MeasurableSet B' := (Set.to_countable B').measurableSet
          have hgm : Measurable (fun y : S → ℕ => B'.indicator (1 : (S → ℕ) → ℝ≥0∞) y) :=
            measurable_one.indicator hB'm
          have hresm : Measurable (fun (y : Fin k × Fin 2 → ℕ) (q : S) => y q) :=
            measurable_pi_lambda _ fun q => measurable_pi_apply _
          have hind : IndepFun (fun (y : Fin k × Fin 2 → ℕ) => B'.indicator (1 : (S → ℕ) → ℝ≥0∞) (fun q : S => y q))
              (fun y => ((y q0 : ℕ) : ℝ≥0∞)) π := by
            have h1 : iIndepFun (fun (q : Fin k × Fin 2) (y : Fin k × Fin 2 → ℕ) => y q) π :=
              iIndepFun_pi (X := fun _ n => n) (fun j => aemeasurable_id)
            have h2 := h1.indepFun_finset S {q0} (Finset.disjoint_singleton_right.2 (Finset.notMem_erase _ _)) (fun q => measurable_pi_apply q)
            exact h2.comp (φ := fun y : S → ℕ => B'.indicator (1 : (S → ℕ) → ℝ≥0∞) y)
              (ψ := fun y : ({q0} : Finset (Fin k × Fin 2)) → ℕ => ((y ⟨q0, Finset.mem_singleton_self q0⟩ : ℕ) : ℝ≥0∞)) hgm
              (measurable_from_top.comp (measurable_pi_apply _))
          have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (hgm.comp hresm)
            ((measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞))).comp (measurable_pi_apply q0)) hind
          have hA' : MeasurableSet {ω | (fun q : S => Inc ω q) ∈ B'} :=
            (hresm.comp hIm) hB'm
          rw [hB', ← lintegral_indicator hA']
          have e1 : ∫⁻ ω, {ω | (fun q : S => Inc ω q) ∈ B'}.indicator (fun ω => ((X t ω i - X s ω i : ℕ) : ℝ≥0∞)) ω ∂G.P
              = ∫⁻ y, (B'.indicator (1 : (S → ℕ) → ℝ≥0∞) (fun q : S => y q)) * ((y q0 : ℕ) : ℝ≥0∞) ∂π := by
            rw [← hmap, lintegral_map _ hIm]
            · refine lintegral_congr fun ω => ?_
              by_cases h : (fun q : S => Inc ω q) ∈ B' <;> simp [Set.indicator, h, hf ω]
            · exact (hgm.comp hresm).mul ((measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞))).comp (measurable_pi_apply q0))
          have e2 : ∫⁻ y, (B'.indicator (1 : (S → ℕ) → ℝ≥0∞) (fun q : S => y q)) ∂π =
              G.P {ω | (fun q : S => Inc ω q) ∈ B'} := by
            rw [← hmap, ← lintegral_indicator_one hA']
            exact lintegral_map (hgm.comp hresm) hIm
          have e3 : ∫⁻ y, ((y q0 : ℕ) : ℝ≥0∞) ∂π = ENNReal.ofReal (G.rate * (t - s)) := by
            have h1' := (measurePreserving_eval (fun j : Fin k × Fin 2 => poissonMeasure
              (Real.toNNReal (G.rate * ((τ j.1.succ : ℝ) - (τ j.1.castSucc : ℝ))))) q0).lintegral_comp
              (measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞)))
            have h2' : ∫⁻ y, ((y q0 : ℕ) : ℝ≥0∞) ∂π = _ := h1'
            rw [h2', hmean]
            simp only [hq0, h1, h2]
            rfl
          rw [e1]
          refine hmul.trans ?_
          rw [mul_comm]
          congr 1
        -- extension
        have hle := naturalFiltration.le s
        have hgen : naturalFiltration s = MeasurableSpace.generateFrom
            (piiUnionInter (fun u : ℝ≥0 => {A | MeasurableSet[MeasurableSpace.comap (X u) inferInstance] A}) (Iic s)) := by
          exact (generateFrom_piiUnionInter_measurableSet (fun u : ℝ≥0 => MeasurableSpace.comap (X u) inferInstance) (Iic s)).symm
        have hC : ∀ A ∈ piiUnionInter (fun u : ℝ≥0 => {A | MeasurableSet[MeasurableSpace.comap (X u) inferInstance] A}) (Iic s),
            ∫⁻ ω in A, ((X t ω i - X s ω i : ℕ) : ℝ≥0∞) ∂G.P = ENNReal.ofReal (G.rate * (t - s)) * G.P A := by
          rintro A ⟨T, hT, f, hf, rfl⟩
          have : ∀ u, ∃ B : Set (Fin 2 → ℕ), u ∈ T → X u ⁻¹' B = f u := by
            intro u
            by_cases hu : u ∈ T
            · obtain ⟨B, -, hB⟩ := hf u hu
              exact ⟨B, fun _ => hB⟩
            · exact ⟨∅, fun h => (hu h).elim⟩
          choose B hB using this
          have := hcyl T (fun u hu => hT hu) B
          rwa [show (⋂ u ∈ T, (X u) ⁻¹' (B u)) = ⋂ u ∈ T, f u from
            iInter_congr fun u => iInter_congr fun hu => hB u hu] at this
        have huniv := hcyl ∅ (fun u hu => absurd hu (Finset.notMem_empty u)) (fun _ => ∅)
        simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ] at huniv
        set μ1 := G.P.withDensity (fun ω => ((X t ω i - X s ω i : ℕ) : ℝ≥0∞)) with hμ1
        set μ2 := ENNReal.ofReal (G.rate * (t - s)) • G.P with hμ2
        have hm1 : ∀ A, MeasurableSet A → μ1 A = ∫⁻ ω in A, ((X t ω i - X s ω i : ℕ) : ℝ≥0∞) ∂G.P :=
          fun A hA => withDensity_apply _ hA
        have hCm : ∀ A ∈ piiUnionInter (fun u : ℝ≥0 => {A | MeasurableSet[MeasurableSpace.comap (X u) inferInstance] A}) (Iic s),
            MeasurableSet[naturalFiltration s] A := by
          intro A hA
          rw [hgen]
          exact MeasurableSpace.measurableSet_generateFrom hA
        have hfin : IsFiniteMeasure (μ1.trim hle) := by
          refine ⟨?_⟩
          rw [trim_measurableSet_eq hle MeasurableSet.univ, hm1 _ MeasurableSet.univ, huniv]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
        have hpi : IsPiSystem (piiUnionInter (fun u : ℝ≥0 => {A | MeasurableSet[MeasurableSpace.comap (X u) inferInstance] A}) (Iic s)) :=
          isPiSystem_piiUnionInter _ (fun u => @MeasurableSpace.isPiSystem_measurableSet _ (MeasurableSpace.comap (X u) inferInstance)) _
        have heq : μ1.trim hle = μ2.trim hle := by
          refine @ext_of_generate_finite _ (naturalFiltration s) _ _ _ hgen hpi hfin ?_ ?_
          · intro A hA
            rw [trim_measurableSet_eq hle (hCm A hA), trim_measurableSet_eq hle (hCm A hA),
              hm1 _ (hle _ (hCm A hA)), hC A hA]
            rfl
          · rw [trim_measurableSet_eq hle MeasurableSet.univ, trim_measurableSet_eq hle MeasurableSet.univ,
              hm1 _ MeasurableSet.univ, huniv]
            rfl
        have := congrArg (fun m => m A) heq
        rw [trim_measurableSet_eq hle hA, trim_measurableSet_eq hle hA, hm1 _ (hle _ hA)] at this
        rw [this]
        rfl
      have COMP : ∀ G : Game, G.Standing → ∀ i, ∀ H : ℝ≥0 × Sample → ℝ≥0∞,
          Measurable[naturalFiltration.predictable] H →
          (∀ T : ℝ≥0, Measurable[naturalFiltration T] (fun ω => ∑' t : jumps T ω i, H (Real.toNNReal t, ω))) ∧
          ∫⁻ ω, ∑' t : jumps G.h ω i, H (Real.toNNReal t, ω) ∂G.P =
            ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal G.rate * H (Real.toNNReal t, ω)) ∂G.P := by
        clear hG G ODE1 ODE2 REAL PATHSUM
        intro G hG i H hH
        have hfin := fun ω T => (PATHS ω i).1 T
        have hX := fun ω => (PATHS ω i).2.1
        have hXmeas : ∀ s T : ℝ≥0, s ≤ T → Measurable[naturalFiltration T] (fun ω => X s ω i) := by
          intro s T hs
          have h1 : Measurable[naturalFiltration T] (X s) :=
            measurable_iff_comap_le.mpr (le_iSup₂ (f := fun (s : ℝ≥0) (_ : s ≤ T) => MeasurableSpace.comap (X s) inferInstance) s hs)
          exact (measurable_pi_apply i).comp h1
        have hcount : ∀ (s T : ℝ≥0) ω, s ≤ T →
            ((jumps T ω i ∩ Ioi (s : ℝ)).encard : ℝ≥0∞) = ((X T ω i - X s ω i : ℕ) : ℝ≥0∞) := by
          intro s T ω hs
          have hf : (jumps T ω i ∩ Ioi (s : ℝ)).Finite := (hfin ω T).inter_of_left _
          have hs' : (s : ℝ) ≤ T := by exact_mod_cast hs
          have hun : jumps T ω i = jumps s ω i ∪ (jumps T ω i ∩ Ioi (s : ℝ)) := by
            ext t
            simp only [jumps, mem_setOf_eq, mem_union, mem_inter_iff, mem_Ioi]
            constructor
            · rintro ⟨a, b, c⟩
              rcases le_or_gt t s with h | h
              · exact Or.inl ⟨a, h, c⟩
              · exact Or.inr ⟨⟨a, b, c⟩, h⟩
            · rintro (⟨a, b, c⟩ | ⟨h, -⟩)
              · exact ⟨a, b.trans hs', c⟩
              · exact h
          have hd : Disjoint (jumps s ω i) (jumps T ω i ∩ Ioi (s : ℝ)) := by
            rw [Set.disjoint_left]
            rintro t ⟨_, b, _⟩ ⟨_, h⟩
            exact absurd b (not_le.mpr h)
          have hc : (jumps T ω i).ncard = (jumps s ω i).ncard + (jumps T ω i ∩ Ioi (s : ℝ)).ncard := by
            rw [← Set.ncard_union_eq hd (hfin ω s) hf, ← hun]
          rw [hX, hX, hc, Nat.add_sub_cancel_left, ← hf.cast_ncard_eq]
          exact ENat.toENNReal_coe _
        letI mE : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
        set PS : Set (Set (ℝ≥0 × Sample)) :=
          {s | ∃ A, MeasurableSet[naturalFiltration ⊥] A ∧ s = {⊥} ×ˢ A} ∪
          {s | ∃ j A, MeasurableSet[naturalFiltration j] A ∧ s = Set.Ioi j ×ˢ A} with hPS
        have hgen : mE = MeasurableSpace.generateFrom PS := rfl
        have hpi : IsPiSystem PS := by
          rintro _ (⟨A, hA, rfl⟩ | ⟨j, A, hA, rfl⟩) _ (⟨B, hB, rfl⟩ | ⟨k, B, hB, rfl⟩) hne
          · left
            exact ⟨A ∩ B, hA.inter hB, by rw [Set.prod_inter_prod, inter_self]⟩
          · exfalso
            obtain ⟨⟨t, ω⟩, ⟨h1, -⟩, ⟨h2, -⟩⟩ := hne
            simp only [mem_singleton_iff, mem_Ioi] at h1 h2
            rw [h1] at h2
            exact not_lt_bot h2
          · exfalso
            obtain ⟨⟨t, ω⟩, ⟨h2, -⟩, ⟨h1, -⟩⟩ := hne
            simp only [mem_singleton_iff, mem_Ioi] at h1 h2
            rw [h1] at h2
            exact not_lt_bot h2
          · right
            refine ⟨j ⊔ k, A ∩ B, ?_, ?_⟩
            · exact MeasurableSet.inter (naturalFiltration.mono le_sup_left _ hA)
                (naturalFiltration.mono le_sup_right _ hB)
            · rw [Set.prod_inter_prod, Set.Ioi_inter_Ioi]
        have hPSm : ∀ S ∈ PS, MeasurableSet[mE] S := fun S hS => MeasurableSpace.measurableSet_generateFrom hS
        -- jump measure
        let ν : ℝ≥0 → Sample → @Measure (ℝ≥0 × Sample) mE := fun T ω =>
          Measure.sum (fun t : jumps T ω i => Measure.dirac (Real.toNNReal t, ω))
        have hν : ∀ T ω (F : ℝ≥0 × Sample → ℝ≥0∞), Measurable[mE] F →
            ∫⁻ p, F p ∂(ν T ω) = ∑' t : jumps T ω i, F (Real.toNNReal t, ω) := by
          intro T ω F hF
          simp only [ν]
          rw [lintegral_sum_measure]
          exact tsum_congr fun t => lintegral_dirac' _ hF
        have hνbot : ∀ T ω A, MeasurableSet[naturalFiltration ⊥] A → ν T ω ({⊥} ×ˢ A) = 0 := by
          intro T ω A hA
          have hm : MeasurableSet[mE] ({⊥} ×ˢ A) := hPSm _ (Or.inl ⟨A, hA, rfl⟩)
          simp only [ν]
          rw [Measure.sum_apply _ hm]
          refine ENNReal.tsum_eq_zero.mpr fun t => ?_
          rw [Measure.dirac_apply' _ hm, indicator_of_notMem]
          rintro ⟨h1, -⟩
          have h2 : Real.toNNReal (t : ℝ) = 0 := h1
          rw [Real.toNNReal_eq_zero] at h2
          exact absurd t.2.1 (not_lt.mpr h2)
        have hνIoi : ∀ T s ω A, MeasurableSet[naturalFiltration s] A →
            ν T ω (Ioi s ×ˢ A) = A.indicator (fun ω => ((jumps T ω i ∩ Ioi (s : ℝ)).encard : ℝ≥0∞)) ω := by
          intro T s ω A hA
          have hm : MeasurableSet[mE] (Ioi s ×ˢ A) := hPSm _ (Or.inr ⟨s, A, hA, rfl⟩)
          simp only [ν]
          rw [Measure.sum_apply _ hm]
          have e : ∀ t : jumps T ω i, Measure.dirac (Real.toNNReal (t : ℝ), ω) (Ioi s ×ˢ A) =
              A.indicator (fun _ => (Ioi (s : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) (t : ℝ)) ω := by
            intro t
            rw [Measure.dirac_apply' _ hm]
            by_cases hω : ω ∈ A
            · by_cases ht : (s : ℝ) < t
              · rw [indicator_of_mem (show (Real.toNNReal (t : ℝ), ω) ∈ Ioi s ×ˢ A from
                  ⟨Real.lt_toNNReal_iff_coe_lt.2 ht, hω⟩), indicator_of_mem hω, indicator_of_mem (mem_Ioi.2 ht)]
                rfl
              · rw [indicator_of_notMem (show (Real.toNNReal (t : ℝ), ω) ∉ Ioi s ×ˢ A from
                  fun h => ht (Real.lt_toNNReal_iff_coe_lt.1 h.1)), indicator_of_mem hω,
                  indicator_of_notMem (fun h => ht (mem_Ioi.1 h))]
            · rw [indicator_of_notMem (show (Real.toNNReal (t : ℝ), ω) ∉ Ioi s ×ˢ A from
                  fun h => hω h.2), indicator_of_notMem hω]
          rw [tsum_congr e]
          by_cases hω : ω ∈ A
          · simp only [indicator_of_mem hω]
            rw [← ENNReal.tsum_set_one, tsum_subtype (jumps T ω i) (fun t => (Ioi (s : ℝ)).indicator (fun _ => (1 : ℝ≥0∞)) t),
              tsum_subtype (jumps T ω i ∩ Ioi (s : ℝ)) (fun _ => (1 : ℝ≥0∞))]
            refine tsum_congr fun t => ?_
            rw [Set.indicator_indicator]
          · simp only [indicator_of_notMem hω, tsum_zero]
        have hνuniv : ∀ T ω, ν T ω univ = ((X T ω i : ℕ) : ℝ≥0∞) := by
          intro T ω
          simp only [ν]
          rw [Measure.sum_apply _ MeasurableSet.univ]
          simp only [measure_univ]
          rw [ENNReal.tsum_set_one, hX, ← (hfin ω T).cast_ncard_eq]
          exact ENat.toENNReal_coe _
        have hνfin : ∀ T ω, IsFiniteMeasure (ν T ω) := fun T ω => ⟨by
          rw [hνuniv]; exact ENNReal.natCast_lt_top _⟩
        have hνm : ∀ T : ℝ≥0, Measurable[naturalFiltration T] (ν T) := by
          intro T
          haveI := hνfin T
          refine @Measurable.measure_of_isPiSystem Sample (ℝ≥0 × Sample) (naturalFiltration T) mE (ν T) _ PS hgen hpi ?_ ?_
          · rintro S (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
            · simp only [hνbot T _ A hA]
              exact measurable_const
            · simp only [hνIoi T s _ A hA]
              rcases le_or_gt s T with hs | hs
              · simp only [hcount s T _ hs]
                refine Measurable.indicator ?_ (naturalFiltration.mono hs _ hA)
                exact (measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞))).comp
                  ((measurable_of_countable (fun p : ℕ × ℕ => p.1 - p.2)).comp ((hXmeas T T le_rfl).prodMk (hXmeas s T hs)))
              · have : ∀ ω, (jumps T ω i ∩ Ioi (s : ℝ)) = ∅ := by
                  intro ω
                  rw [Set.eq_empty_iff_forall_notMem]
                  rintro t ⟨⟨_, h, _⟩, h2⟩
                  have h3 : (T : ℝ) < s := by exact_mod_cast hs
                  have h4 : (s : ℝ) < t := h2
                  exact absurd (h4.trans_le h) h3.not_gt
                simp only [this, encard_empty, ENat.toENNReal_zero, indicator_zero]
                exact measurable_const
          · simp only [hνuniv]
            exact (measurable_from_top (f := fun n : ℕ => (n : ℝ≥0∞))).comp (hXmeas T T le_rfl)
        refine ⟨fun T => ?_, ?_⟩
        · have := @Measurable.comp _ _ _ (naturalFiltration T) _ _ _ _ (Measure.measurable_lintegral hH) (hνm T)
          refine (congrArg (Measurable[naturalFiltration T]) (funext fun ω => ?_)).mp this
          exact hν T ω H hH
        · haveI hP : IsProbabilityMeasure G.P := hG.2.2.2.2.2.1
          have hh : 0 ≤ G.h := hG.1
          have hr : 0 < G.rate := hG.2.2.2.1
          obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ) = G.h := ⟨⟨G.h, hh⟩, rfl⟩
          rw [← hT]
          have hsec : ∀ ω : Sample, Measurable[_, mE] (fun t : ℝ => (Real.toNNReal t, ω)) := by
            intro ω
            refine measurable_generateFrom ?_
            rintro S (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
            · exact MeasurableSet.inter (measurable_real_toNNReal (measurableSet_singleton _))
                (MeasurableSet.const (ω ∈ A))
            · exact MeasurableSet.inter (measurable_real_toNNReal measurableSet_Ioi)
                (MeasurableSet.const (ω ∈ A))
          let ρ : Measure ℝ := ENNReal.ofReal G.rate • volume.restrict (Ioc (0:ℝ) T)
          let ν' : Sample → @Measure (ℝ≥0 × Sample) mE := fun ω =>
            Measure.map (fun t : ℝ => (Real.toNNReal t, ω)) ρ
          have hν'bot : ∀ ω A, MeasurableSet[naturalFiltration ⊥] A → ν' ω ({⊥} ×ˢ A) = 0 := by
            intro ω A hA
            have hm : MeasurableSet[mE] ({⊥} ×ˢ A) := hPSm _ (Or.inl ⟨A, hA, rfl⟩)
            simp only [ν']
            rw [Measure.map_apply (hsec ω) hm]
            simp only [ρ, Measure.smul_apply, smul_eq_mul]
            rw [Measure.restrict_apply (hsec ω hm)]
            have : (fun t : ℝ => (Real.toNNReal t, ω)) ⁻¹' ({⊥} ×ˢ A) ∩ Ioc (0:ℝ) T = ∅ := by
              rw [Set.eq_empty_iff_forall_notMem]
              rintro t ⟨⟨h1, -⟩, h3, -⟩
              have h2 : Real.toNNReal (t : ℝ) = 0 := h1
              rw [Real.toNNReal_eq_zero] at h2
              exact absurd h3 (not_lt.mpr h2)
            rw [this, measure_empty, mul_zero]
          have hν'Ioi : ∀ s ω A, MeasurableSet[naturalFiltration s] A →
              ν' ω (Ioi s ×ˢ A) = A.indicator (fun _ => ENNReal.ofReal (G.rate * (T - s))) ω := by
            intro s ω A hA
            have hm : MeasurableSet[mE] (Ioi s ×ˢ A) := hPSm _ (Or.inr ⟨s, A, hA, rfl⟩)
            simp only [ν']
            rw [Measure.map_apply (hsec ω) hm]
            simp only [ρ, Measure.smul_apply, smul_eq_mul]
            rw [Measure.restrict_apply (hsec ω hm)]
            by_cases hω : ω ∈ A
            · have : (fun t : ℝ => (Real.toNNReal t, ω)) ⁻¹' (Ioi s ×ˢ A) ∩ Ioc (0:ℝ) T = Ioc (s : ℝ) T := by
                ext t
                have h0 : (0 : ℝ) ≤ s := s.2
                constructor
                · rintro ⟨⟨a, -⟩, b, c⟩; exact ⟨Real.lt_toNNReal_iff_coe_lt.1 a, c⟩
                · rintro ⟨a, c⟩; exact ⟨⟨Real.lt_toNNReal_iff_coe_lt.2 a, hω⟩, h0.trans_lt a, c⟩
              rw [this, Real.volume_Ioc, indicator_of_mem hω, ENNReal.ofReal_mul hr.le]
            · have : (fun t : ℝ => (Real.toNNReal t, ω)) ⁻¹' (Ioi s ×ˢ A) ∩ Ioc (0:ℝ) T = ∅ := by
                exact Set.eq_empty_iff_forall_notMem.2 fun t h => hω h.1.2
              rw [this, measure_empty, mul_zero, indicator_of_notMem hω]
          have hν'univ : ∀ ω, ν' ω univ = ENNReal.ofReal (G.rate * T) := by
            intro ω
            simp only [ν']
            rw [Measure.map_apply (hsec ω) MeasurableSet.univ]
            simp only [ρ, Measure.smul_apply, smul_eq_mul, preimage_univ, Measure.restrict_apply_univ,
              Real.volume_Ioc, sub_zero]
            rw [ENNReal.ofReal_mul hr.le]
          have hν'fin : ∀ ω, IsFiniteMeasure (ν' ω) := fun ω => ⟨by
            rw [hν'univ]; exact ENNReal.ofReal_lt_top⟩
          have hle := naturalFiltration.le
          have hν'm : Measurable ν' := by
            haveI := hν'fin
            refine Measurable.measure_of_isPiSystem hgen hpi ?_ ?_
            · rintro S (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
              · simp only [hν'bot _ A hA]
                exact measurable_const
              · simp only [hν'Ioi s _ A hA]
                exact measurable_const.indicator (hle s _ hA)
            · simp only [hν'univ]; exact measurable_const
          have hνm0 : Measurable (ν T) := (hνm T).mono (hle T) le_rfl
          have hX0 : ∀ ω, X 0 ω i = 0 := by
            intro ω
            exact (congrArg (ω i).val NNReal.coe_zero).trans (((ω i).2 0 le_rfl).zero ())
          have hbuniv : ∫⁻ ω, ν T ω univ ∂G.P = ENNReal.ofReal (G.rate * T) := by
            simp only [hνuniv]
            have := INDEP G hG 0 T bot_le univ MeasurableSet.univ i
            simp only [hX0, Nat.sub_zero, Measure.restrict_univ, NNReal.coe_zero, sub_zero, measure_univ, mul_one] at this
            exact this
          have hbind : G.P.bind (ν T) = G.P.bind ν' := by
            haveI : IsFiniteMeasure (G.P.bind (ν T)) := ⟨by
              rw [Measure.bind_apply MeasurableSet.univ hνm0.aemeasurable, hbuniv]
              exact ENNReal.ofReal_lt_top⟩
            refine ext_of_generate_finite PS hgen hpi ?_ ?_
            · rintro S hS
              rw [Measure.bind_apply (hPSm S hS) hνm0.aemeasurable,
                Measure.bind_apply (hPSm S hS) hν'm.aemeasurable]
              rcases hS with (⟨A, hA, rfl⟩ | ⟨s, A, hA, rfl⟩)
              · simp only [hνbot T _ A hA, hν'bot _ A hA]
              · simp only [hνIoi T s _ A hA, hν'Ioi s _ A hA]
                rw [lintegral_indicator (hle s _ hA), lintegral_indicator (hle s _ hA)]
                rw [setLIntegral_const]
                rcases le_or_gt s T with hs | hs
                · simp only [hcount s T _ hs]
                  exact INDEP G hG s T hs A hA i
                · have h3 : (T : ℝ) < s := by exact_mod_cast hs
                  have : ∀ ω, (jumps T ω i ∩ Ioi (s : ℝ)) = ∅ := by
                    intro ω
                    rw [Set.eq_empty_iff_forall_notMem]
                    rintro t ⟨⟨_, h, _⟩, h2⟩
                    have h4 : (s : ℝ) < t := h2
                    exact absurd (h4.trans_le h) h3.not_gt
                  rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hr.le (sub_nonpos.2 h3.le)), zero_mul]
                  simp only [this, encard_empty, ENat.toENNReal_zero, lintegral_zero]
            · rw [Measure.bind_apply MeasurableSet.univ hνm0.aemeasurable,
                Measure.bind_apply MeasurableSet.univ hν'm.aemeasurable, hbuniv]
              simp only [hν'univ]
              rw [lintegral_const, measure_univ, mul_one]
          have e1 : ∫⁻ p, H p ∂(G.P.bind (ν T)) = ∫⁻ ω, ∑' t : jumps T ω i, H (Real.toNNReal t, ω) ∂G.P := by
            rw [Measure.lintegral_bind hνm0.aemeasurable hH.aemeasurable]
            exact lintegral_congr fun ω => hν T ω H hH
          have e2 : ∫⁻ p, H p ∂(G.P.bind ν') =
              ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) T, ENNReal.ofReal G.rate * H (Real.toNNReal t, ω)) ∂G.P := by
            rw [Measure.lintegral_bind hν'm.aemeasurable hH.aemeasurable]
            refine lintegral_congr fun ω => ?_
            simp only [ν']
            rw [lintegral_map hH (hsec ω)]
            simp only [ρ]
            rw [lintegral_smul_measure]
            exact (lintegral_const_mul _ (f := fun t : ℝ => H (Real.toNNReal t, ω)) (hH.comp (hsec ω))).symm
          rw [← e1, ← e2, hbind]
      have COMPREAL : ∀ G : Game, G.Standing → ∀ i, ∀ H : ℝ≥0 × Sample → ℝ,
          Measurable[naturalFiltration.predictable] H →
          ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal |H (Real.toNNReal t, ω)|) ∂G.P ≠ ⊤ →
          Integrable (fun ω => ∑ᶠ t ∈ jumps G.h ω i, H (Real.toNNReal t, ω)) G.P ∧
          Integrable (fun ω => ∫ t in Icc (0:ℝ) G.h, H (Real.toNNReal t, ω)) G.P ∧
          ∫ ω, ∑ᶠ t ∈ jumps G.h ω i, H (Real.toNNReal t, ω) ∂G.P =
            G.rate * ∫ ω, (∫ t in Icc (0:ℝ) G.h, H (Real.toNNReal t, ω)) ∂G.P := by
        clear hG G ODE1 ODE2 REAL PATHSUM INDEP
        classical
        intro G hG i H hH hfin
        have hP : IsProbabilityMeasure G.P := hG.2.2.2.2.2.1
        have hle : naturalFiltration.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Sample)) := by
          apply MeasureTheory.measurableSpace_le_predictable_of_measurableSet
          · intro A hA
            exact (measurableSet_singleton _).prod (naturalFiltration.le _ _ hA)
          · intro t A hA
            exact measurableSet_Ioi.prod (naturalFiltration.le _ _ hA)
        have hHb : Measurable H := hH.mono hle le_rfl
        have hj : Measurable (fun p : Sample × ℝ => H (Real.toNNReal p.2, p.1)) :=
          hHb.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)
        have hjω : ∀ ω, Measurable (fun t : ℝ => H (Real.toNNReal t, ω)) := fun ω =>
          hj.comp (measurable_const.prodMk measurable_id)
        have hFabs : ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal G.rate *
            ENNReal.ofReal |H (Real.toNNReal t, ω)|) ∂G.P ≠ ⊤ := by
          have : ∀ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal G.rate *
            ENNReal.ofReal |H (Real.toNNReal t, ω)|) = ENNReal.ofReal G.rate *
              ∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal |H (Real.toNNReal t, ω)| := fun ω =>
            lintegral_const_mul _ ((hjω ω).abs.ennreal_ofReal)
          simp_rw [this]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
        -- one-sided facts
        have key : ∀ F : ℝ≥0 × Sample → ℝ, Measurable[naturalFiltration.predictable] F →
            (∀ p, ENNReal.ofReal (F p) ≤ ENNReal.ofReal |H p|) →
            Integrable (fun ω => (∑' t : jumps G.h ω i, ENNReal.ofReal (F (Real.toNNReal t, ω))).toReal) G.P ∧
            Integrable (fun ω => (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (F (Real.toNNReal t, ω))).toReal) G.P ∧
            ∫ ω, (∑' t : jumps G.h ω i, ENNReal.ofReal (F (Real.toNNReal t, ω))).toReal ∂G.P =
              G.rate * ∫ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (F (Real.toNNReal t, ω))).toReal ∂G.P := by
          intro F hF hFH
          have hFb : Measurable F := hF.mono hle le_rfl
          have hFj : Measurable (fun p : Sample × ℝ => ENNReal.ofReal (F (Real.toNNReal p.2, p.1))) :=
            (hFb.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)).ennreal_ofReal
          have hFω : ∀ ω, Measurable (fun t : ℝ => ENNReal.ofReal (F (Real.toNNReal t, ω))) := fun ω =>
            hFj.comp (measurable_const.prodMk measurable_id)
          have hIm : Measurable (fun ω => ∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (F (Real.toNNReal t, ω))) :=
            Measurable.lintegral_prod_right' hFj
          have hc := COMP G hG i (fun p => ENNReal.ofReal (F p))
            (@Measurable.ennreal_ofReal _ naturalFiltration.predictable _ hF)
          obtain ⟨hm, he⟩ := hc
          have hSm : Measurable (fun ω => ∑' t : jumps G.h ω i, ENNReal.ofReal (F (Real.toNNReal t, ω))) := by
            have := hm (Real.toNNReal G.h)
            rw [Real.coe_toNNReal _ hG.1] at this
            exact this.mono (naturalFiltration.le _) le_rfl
          have hpull : ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal G.rate * ENNReal.ofReal (F (Real.toNNReal t, ω))) ∂G.P
              = ENNReal.ofReal G.rate * ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (F (Real.toNNReal t, ω))) ∂G.P := by
            rw [← lintegral_const_mul _ hIm]
            refine lintegral_congr fun ω => ?_
            exact lintegral_const_mul _ (hFω ω)
          have hIfin : ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (F (Real.toNNReal t, ω))) ∂G.P ≠ ⊤ :=
            ne_top_of_le_ne_top hfin (lintegral_mono fun ω => lintegral_mono fun t => hFH _)
          have hSfin : ∫⁻ ω, (∑' t : jumps G.h ω i, ENNReal.ofReal (F (Real.toNNReal t, ω))) ∂G.P ≠ ⊤ := by
            rw [he, hpull]
            exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin
          refine ⟨integrable_toReal_of_lintegral_ne_top hSm.aemeasurable hSfin,
            integrable_toReal_of_lintegral_ne_top hIm.aemeasurable hIfin, ?_⟩
          rw [integral_toReal hSm.aemeasurable (ae_lt_top hSm hSfin),
            integral_toReal hIm.aemeasurable (ae_lt_top hIm hIfin), he, hpull, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal hG.2.2.2.1.le]
        obtain ⟨p1, p2, p3⟩ := key H hH (fun p => ENNReal.ofReal_le_ofReal (le_abs_self _))
        obtain ⟨n1, n2, n3⟩ := key (fun p => - H p)
          (@Measurable.comp _ _ _ naturalFiltration.predictable _ _ _ _ measurable_neg hH)
          (fun p => ENNReal.ofReal_le_ofReal (neg_le_abs _))
        have hS : (fun ω => ∑ᶠ t ∈ jumps G.h ω i, H (Real.toNNReal t, ω)) = fun ω =>
            (∑' t : jumps G.h ω i, ENNReal.ofReal (H (Real.toNNReal t, ω))).toReal -
            (∑' t : jumps G.h ω i, ENNReal.ofReal (- H (Real.toNNReal t, ω))).toReal := by
          funext ω
          have hf : (jumps G.h ω i).Finite := (PATHS ω i).1 G.h
          have : Fintype (jumps G.h ω i) := hf.fintype
          rw [tsum_fintype, tsum_fintype, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top),
            ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top), ← Finset.sum_sub_distrib,
            ← finsum_set_coe_eq_finsum_mem (jumps G.h ω i) (f := fun t => H (Real.toNNReal t, ω)), finsum_eq_sum_of_fintype]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', max_zero_sub_eq_self]
        have hIabs : Measurable (fun ω => ∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal |H (Real.toNNReal t, ω)|) :=
          Measurable.lintegral_prod_right' (f := fun p : Sample × ℝ => ENNReal.ofReal |H (Real.toNNReal p.2, p.1)|)
            hj.abs.ennreal_ofReal
        have hI : (fun ω => ∫ t in Icc (0:ℝ) G.h, H (Real.toNNReal t, ω)) =ᵐ[G.P] fun ω =>
            (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (H (Real.toNNReal t, ω))).toReal -
            (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (- H (Real.toNNReal t, ω))).toReal := by
          filter_upwards [ae_lt_top hIabs hfin] with ω hω
          rw [integral_Icc_eq_integral_Ioc]
          refine integral_eq_lintegral_pos_part_sub_lintegral_neg_part
            ⟨(hjω ω).aestronglyMeasurable, ?_⟩
          rw [hasFiniteIntegral_iff_norm]
          simpa [Real.norm_eq_abs] using hω
        refine ⟨?_, ?_, ?_⟩
        · rw [hS]; exact p1.sub n1
        · exact (p2.sub n2).congr hI.symm
        · rw [hS, integral_congr_ae hI, integral_sub p1 n1, integral_sub p2 n2, p3, n3]
          ring
      have MOM : ∀ G : Game, G.Standing → ∀ c : ℝ, 0 ≤ c →
          Integrable (fun ω => c ^ (X (Real.toNNReal G.h) ω 0 + X (Real.toNNReal G.h) ω 1)) G.P := by
        clear hG G ODE1 ODE2 PATHS REAL PATHSUM INDEP COMP COMPREAL
        intro G hG c hc
        obtain ⟨hh, -, -, hr, -, hP, hmap⟩ := hG
        have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
          measurable_iff_comap_le.mpr (le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) t)
        have hX0 : ∀ ω i, X 0 ω i = 0 := by
          intro ω i
          have := ((ω i).property 0 le_rfl).zero ()
          simpa [X] using this
        set T := Real.toNNReal G.h with hT
        have hmono : Monotone (![0, T] : Fin 2 → ℝ≥0) := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp at hij ⊢
        have key := hmap 1 ![0, T] hmono
        have hmeas : Measurable (fun ω (j : Fin 1 × Fin 2) =>
            X ((![0, T] : Fin 2 → ℝ≥0) j.1.succ) ω j.2 - X ((![0, T] : Fin 2 → ℝ≥0) j.1.castSucc) ω j.2) := by
          refine measurable_pi_lambda _ fun j => ?_
          exact ((measurable_pi_apply j.2).comp (hXm _)).sub ((measurable_pi_apply j.2).comp (hXm _))
        have hint : ∀ r : ℝ≥0, Integrable (fun n : ℕ => c ^ n) (poissonMeasure r) := by
          intro r
          rw [integrable_poissonMeasure_iff]
          have := (Real.summable_pow_div_factorial ((r : ℝ) * c)).mul_left (Real.exp (-r))
          refine this.congr fun n => ?_
          rw [Real.norm_of_nonneg (by positivity), mul_pow]
          ring
        have h1 : Integrable (fun y : Fin 1 × Fin 2 → ℕ => ∏ j, c ^ (y j)) (Measure.map (fun ω (j : Fin 1 × Fin 2) =>
            X ((![0, T] : Fin 2 → ℝ≥0) j.1.succ) ω j.2 - X ((![0, T] : Fin 2 → ℝ≥0) j.1.castSucc) ω j.2) G.P) := by
          rw [key]
          exact Integrable.fintype_prod (f := fun _ n => c ^ n) (fun j => hint _)
        have h2 := h1.comp_measurable hmeas
        refine h2.congr (Eventually.of_forall fun ω => ?_)
        simp [Function.comp, Fintype.prod_prod_type, hX0, pow_add]
      have NOCOMMON : ∀ G : Game, G.Standing →
          ∀ᵐ ω ∂G.P, Disjoint (jumps G.h ω 0) (jumps G.h ω 1) := by
        clear hG G ODE1 ODE2 REAL PATHSUM INDEP COMP COMPREAL MOM
        intro G hG
        obtain ⟨hh, -, -, hr, -, hP, hmap⟩ := hG
        have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
          measurable_iff_comap_le.mpr (le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) t)
        set T := Real.toNNReal G.h with hT
        have hTh : (T : ℝ) = G.h := Real.coe_toNNReal _ hh
        have hpo : ∀ r : ℝ≥0, poissonMeasure r {n | 1 ≤ n} ≤ r := by
          intro r
          have h1 : ({n | 1 ≤ n} : Set ℕ) = {0}ᶜ := by
            ext n; simp [Nat.one_le_iff_ne_zero]
          rw [h1, prob_compl_eq_one_sub (measurableSet_singleton 0), poissonMeasure_singleton]
          simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.exp_pos _).le, ← ENNReal.ofReal_coe_nnreal]
          apply ENNReal.ofReal_le_ofReal
          have := Real.add_one_le_exp (-(r : ℝ))
          linarith
        have hinc : ∀ s t : ℝ≥0, s ≤ t → G.P {ω | 1 ≤ X t ω 0 - X s ω 0 ∧ 1 ≤ X t ω 1 - X s ω 1} ≤
            ENNReal.ofReal (G.rate * (t - s)) * ENNReal.ofReal (G.rate * (t - s)) := by
          intro s t hst
          have hmono : Monotone (![s, t] : Fin 2 → ℝ≥0) := by
            refine Fin.monotone_iff_le_succ.2 fun i => ?_
            have hi : i = 0 := Subsingleton.elim _ _
            subst hi
            exact hst
          have key := hmap 1 ![s, t] hmono
          have hmeas : Measurable (fun ω (j : Fin 1 × Fin 2) =>
              X ((![s, t] : Fin 2 → ℝ≥0) j.1.succ) ω j.2 - X ((![s, t] : Fin 2 → ℝ≥0) j.1.castSucc) ω j.2) := by
            refine measurable_pi_lambda _ fun j => ?_
            exact ((measurable_pi_apply j.2).comp (hXm _)).sub ((measurable_pi_apply j.2).comp (hXm _))
          have h2 := congrArg (fun m : Measure (Fin 1 × Fin 2 → ℕ) => m (Set.univ.pi fun _ => {n | 1 ≤ n})) key
          rw [Measure.map_apply hmeas (MeasurableSet.univ_pi fun _ => MeasurableSet.of_discrete), Measure.pi_pi] at h2
          have h3 : {ω | 1 ≤ X t ω 0 - X s ω 0 ∧ 1 ≤ X t ω 1 - X s ω 1} =
            ((fun ω (j : Fin 1 × Fin 2) =>
              X ((![s, t] : Fin 2 → ℝ≥0) j.1.succ) ω j.2 - X ((![s, t] : Fin 2 → ℝ≥0) j.1.castSucc) ω j.2) ⁻¹'
              (Set.univ.pi fun _ => {n | 1 ≤ n})) := by
            ext ω
            constructor
            · rintro ⟨h0, h1⟩ ⟨j, l⟩ -
              have hj : j = 0 := Subsingleton.elim _ _
              subst hj
              revert l
              exact Fin.forall_fin_two.2 ⟨h0, h1⟩
            · exact fun h => ⟨h (0, 0) trivial, h (0, 1) trivial⟩
          rw [h3, h2]
          simp only [Fintype.prod_prod_type, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
            Fin.prod_univ_two]
          have h4 := hpo (Real.toNNReal (G.rate * ((t:ℝ) - s)))
          exact mul_le_mul' h4 h4
        have hbd : ∀ n : ℕ, 0 < n → G.P {ω | ¬ Disjoint (jumps G.h ω 0) (jumps G.h ω 1)} ≤
            ENNReal.ofReal ((G.rate * G.h) ^ 2 / n) := by
          intro n hn
          have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
          let τ : ℕ → ℝ≥0 := fun k => T * k / n
          have hτ : ∀ k, (τ k : ℝ) = G.h * k / n := fun k => by
            rw [show τ k = T * k / n from rfl, NNReal.coe_div, NNReal.coe_mul, hTh, NNReal.coe_natCast, NNReal.coe_natCast]
          have hsub : {ω | ¬ Disjoint (jumps G.h ω 0) (jumps G.h ω 1)} ⊆
              ⋃ k ∈ Finset.range n, {ω | 1 ≤ X (τ (k+1)) ω 0 - X (τ k) ω 0 ∧ 1 ≤ X (τ (k+1)) ω 1 - X (τ k) ω 1} := by
            intro ω hω
            obtain ⟨t, ht0, ht1⟩ := Set.not_disjoint_iff.mp hω
            have ht0' : 0 < t ∧ t ≤ G.h := ⟨ht0.1, ht0.2.1⟩
            have hhpos : 0 < G.h := lt_of_lt_of_le ht0'.1 ht0'.2
            -- k = ⌈t n / h⌉ - 1
            have hm1 : 0 < ⌈t * n / G.h⌉₊ := Nat.ceil_pos.mpr (div_pos (mul_pos ht0'.1 hn') hhpos)
            obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm1.ne'
            have hle : t * n / G.h ≤ (k + 1 : ℕ) := by rw [← Nat.succ_eq_add_one, ← hk]; exact Nat.le_ceil _
            have hlt : (k : ℝ) < t * n / G.h := by
              have : k < ⌈t * n / G.h⌉₊ := by omega
              exact Nat.lt_ceil.mp this
            have hkn : k < n := by
              have : t * n / G.h ≤ n := by
                rw [div_le_iff₀ hhpos, mul_comm (n:ℝ)]; exact mul_le_mul_of_nonneg_right ht0'.2 hn'.le
              exact Nat.cast_lt.1 (lt_of_lt_of_le hlt this)
            have hta : (τ k : ℝ) < t := by
              rw [hτ, div_lt_iff₀ hn', mul_comm G.h]; exact (lt_div_iff₀ hhpos).1 hlt
            have htb : t ≤ (τ (k+1) : ℝ) := by
              rw [hτ, le_div_iff₀ hn', mul_comm G.h]; exact (div_le_iff₀ hhpos).1 hle
            have hj : ∀ i, t ∈ jumps G.h ω i → 1 ≤ X (τ (k+1)) ω i - X (τ k) ω i := by
              intro i hi
              obtain ⟨hf, hX, -⟩ := PATHS ω i
              have : X (τ k) ω i < X (τ (k+1)) ω i := by
                rw [hX, hX]
                apply Set.ncard_lt_ncard _ (hf _)
                refine ⟨fun q hq => ⟨hq.1, hq.2.1.trans (hta.le.trans htb), hq.2.2⟩, fun hc => ?_⟩
                have := (hc ⟨hi.1, htb, hi.2.2⟩).2.1
                exact absurd this (not_le.2 hta)
              exact Nat.le_sub_of_add_le (by rw [Nat.add_comm]; exact this)
            simp only [Set.mem_iUnion]
            exact ⟨k, Finset.mem_range.mpr hkn, hj 0 ht0, hj 1 ht1⟩
          refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
          have : ∀ k ∈ Finset.range n, G.P {ω | 1 ≤ X (τ (k+1)) ω 0 - X (τ k) ω 0 ∧ 1 ≤ X (τ (k+1)) ω 1 - X (τ k) ω 1}
              ≤ ENNReal.ofReal ((G.rate * G.h / n) ^ 2) := by
            intro k _
            have hle : τ k ≤ τ (k+1) := by
              rw [← NNReal.coe_le_coe, hτ, hτ]
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left (Nat.cast_le.2 (Nat.le_succ k)) hh) hn'.le
            refine (hinc _ _ hle).trans (le_of_eq ?_)
            have : G.rate * ((τ (k+1) : ℝ) - τ k) = G.rate * G.h / n := by
              rw [hτ, hτ]; push_cast; ring
            rw [this, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg hr.le hh) hn'.le), sq]
          refine (Finset.sum_le_sum this).trans (le_of_eq ?_)
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul hn'.le]
          congr 1
          field_simp
        rw [ae_iff]
        refine le_antisymm (ge_of_tendsto (f := fun n : ℕ => ENNReal.ofReal ((G.rate * G.h) ^ 2 / n)) (x := atTop) ?_ ?_) bot_le
        · have h5 : Tendsto (fun n : ℕ => (G.rate * G.h) ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
            tendsto_const_div_atTop_nhds_zero_nat _
          simpa using ENNReal.tendsto_ofReal h5
        · filter_upwards [eventually_gt_atTop 0] with n hn using hbd n hn
      have LEFT : ∀ Z : ℝ≥0 → Sample → ℝ, (∀ t, Measurable[naturalFiltration t] (Z t)) →
          (∀ ω, ∀ t : ℝ≥0, 0 < t → Tendsto (fun s => Z s ω) (𝓝[<] t) (𝓝 (Z t ω))) →
          Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => Z p.1 p.2) := by
        clear hG G ODE1 ODE2 PATHS REAL PATHSUM INDEP COMP COMPREAL MOM NOCOMMON
        intro Z hZ hleft
        let mm : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
        let q : ℕ → ℕ → ℝ≥0 := fun n k => (k : ℝ≥0) / ((n : ℝ≥0) + 1)
        let s : ℕ → ℝ≥0 → ℝ≥0 := fun n t => q n (⌈((n : ℝ≥0) + 1) * t⌉₊ - 1)
        have hpos : ∀ n : ℕ, (0 : ℝ≥0) < (n : ℝ≥0) + 1 := fun n => by positivity
        have hsmem : ∀ n (t : ℝ≥0), 0 < t → s n t < t ∧ t ≤ s n t + 1 / ((n : ℝ≥0) + 1) := by
          intro n t ht
          have hprod : 0 < ((n : ℝ≥0) + 1) * t := mul_pos (hpos n) ht
          have hceil : 0 < ⌈((n : ℝ≥0) + 1) * t⌉₊ := Nat.ceil_pos.2 hprod
          obtain ⟨k, hk⟩ : ∃ k, ⌈((n : ℝ≥0) + 1) * t⌉₊ = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hceil).symm⟩
          have h1 : (k : ℝ≥0) < ((n : ℝ≥0) + 1) * t := by
            apply Nat.lt_ceil.1; omega
          have h2 : ((n : ℝ≥0) + 1) * t ≤ (k : ℝ≥0) + 1 := by
            have := Nat.le_ceil (((n : ℝ≥0) + 1) * t)
            rw [hk] at this; exact_mod_cast this
          have hs : s n t = (k : ℝ≥0) / ((n : ℝ≥0) + 1) := by
            simp only [s, q, hk, Nat.add_sub_cancel]
          rw [hs]
          constructor
          · rw [div_lt_iff₀ (hpos n), mul_comm]; exact h1
          · rw [← add_div, le_div_iff₀ (hpos n), mul_comm]; exact h2
        let F : ℕ → ℝ≥0 × Sample → ℝ := fun n p => if p.1 = 0 then Z 0 p.2 else Z (s n p.1) p.2
        have hF : ∀ n, Measurable (F n) := by
          intro n S hS
          have hset : F n ⁻¹' S = ({⊥} ×ˢ (Z 0 ⁻¹' S)) ∪
              ⋃ k : ℕ, (Ioc (q n k) (q n (k+1))) ×ˢ (Z (q n k) ⁻¹' S) := by
            ext ⟨t, ω⟩
            have hb : (⊥ : ℝ≥0) = 0 := rfl
            simp only [mem_preimage, mem_union, mem_prod, mem_singleton_iff, mem_iUnion, mem_Ioc, F, hb]
            by_cases ht : t = 0
            · subst ht
              simp
            · simp only [ht, if_false, false_and, false_or]
              have ht0 : 0 < t := pos_iff_ne_zero.2 ht
              constructor
              · intro h
                refine ⟨⌈((n : ℝ≥0) + 1) * t⌉₊ - 1, ⟨(hsmem n t ht0).1, ?_⟩, h⟩
                have := (hsmem n t ht0).2
                refine this.trans (le_of_eq ?_)
                simp only [s, q]
                rw [← add_div]; push_cast; rfl
              · rintro ⟨k, ⟨h1, h2⟩, h3⟩
                have : ⌈((n : ℝ≥0) + 1) * t⌉₊ = k + 1 := by
                  rw [Nat.ceil_eq_iff (by omega)]
                  simp only [q] at h1 h2
                  rw [div_lt_iff₀ (hpos n), mul_comm] at h1
                  rw [le_div_iff₀ (hpos n), mul_comm] at h2
                  exact ⟨by simpa using h1, h2⟩
                simp only [s, this, Nat.add_sub_cancel]
                exact h3
          rw [hset]
          refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun k => ?_)
          · exact measurableSet_predictable_singleton_bot_prod (hZ 0 hS)
          · exact measurableSet_predictable_Ioc_prod _ _ (hZ _ hS)
        refine measurable_of_tendsto_metrizable hF ?_
        rw [tendsto_pi_nhds]
        rintro ⟨t, ω⟩
        by_cases ht : t = 0
        · subst ht
          simp only [F, if_true]
          exact tendsto_const_nhds
        · have ht0 : 0 < t := pos_iff_ne_zero.2 ht
          simp only [F, ht, if_false]
          refine (hleft ω t ht0).comp ?_
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, Eventually.of_forall fun n => (hsmem n t ht0).1⟩
          rw [← NNReal.tendsto_coe]
          have hlim : Tendsto (fun n : ℕ => (t : ℝ) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
            simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds ?_ ?_
          · intro n
            have := (hsmem n t ht0).2
            have h' : (t : ℝ) ≤ (s n t : ℝ) + 1 / ((n : ℝ) + 1) := by exact_mod_cast this
            show (t : ℝ) - 1 / ((n : ℝ) + 1) ≤ (s n t : ℝ)
            linarith
          · intro n
            exact_mod_cast (hsmem n t ht0).1.le
      have PREX : ∀ i, Measurable[naturalFiltration.predictable]
          (fun p : ℝ≥0 × Sample => preX p.1 p.2 i) := by
        clear hG G ODE1 ODE2 REAL PATHSUM INDEP COMP COMPREAL MOM NOCOMMON
        intro i
        have key : ∀ ω, ∀ t : ℝ≥0, 0 < t → ∀ᶠ s in 𝓝[<] t, X s ω i = preX t ω i ∧ preX s ω i = preX t ω i := by
          intro ω t ht
          obtain ⟨hfin, hX, hpre⟩ := PATHS ω i
          have hJ : (jumps t ω i ∩ Iio (t : ℝ)).Finite := (hfin t).subset inter_subset_left
          have h1 : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, ∀ u ∈ jumps t ω i ∩ Iio (t : ℝ), u < (s : ℝ) := by
            rw [eventually_all_finite hJ]
            intro u hu
            have hc : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[<] t) (𝓝 (t : ℝ)) :=
              (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
            exact hc.eventually (lt_mem_nhds hu.2)
          filter_upwards [h1, self_mem_nhdsWithin] with s hs hst
          have hst' : (s : ℝ) < t := by exact_mod_cast hst
          rw [hX, hpre, hpre]
          have e1 : jumps s ω i = jumps t ω i ∩ Iio (t : ℝ) := by
            ext u
            constructor
            · rintro ⟨a, b, c⟩
              exact ⟨⟨a, b.trans hst'.le, c⟩, b.trans_lt hst'⟩
            · intro hu
              exact ⟨hu.1.1, (hs u hu).le, hu.1.2.2⟩
          have e2 : jumps s ω i ∩ Iio (s : ℝ) = jumps t ω i ∩ Iio (t : ℝ) := by
            rw [e1]
            ext u
            exact ⟨fun h => h.1, fun h => ⟨h, hs u h⟩⟩
          rw [e2, e1]
          exact ⟨rfl, rfl⟩
        have hXm : ∀ t : ℝ≥0, Measurable[naturalFiltration t] (fun ω => X t ω i) := by
          intro t
          have h0 : Measurable[naturalFiltration t] (X t) := by
            have : MeasurableSpace.comap (X t) inferInstance ≤ naturalFiltration t :=
              le_iSup_of_le t (le_iSup_of_le le_rfl le_rfl)
            exact Measurable.mono (comap_measurable (X t)) this le_rfl
          exact (measurable_pi_apply i).comp h0
        have hpm : ∀ t : ℝ≥0, Measurable[naturalFiltration t] (fun ω => (preX t ω i : ℝ)) := by
          intro t
          by_cases ht : t = 0
          · subst ht
            have : (fun ω => (preX 0 ω i : ℝ)) = fun _ => 0 := by
              funext ω; simp [preX]
            rw [this]; exact measurable_const
          · have ht0 : 0 < t := pos_iff_ne_zero.2 ht
            obtain ⟨v, hv1, hv2, hv3⟩ := exists_seq_strictMono_tendsto' ht0
            have hvlim : Tendsto v atTop (𝓝[<] t) :=
              tendsto_nhdsWithin_iff.2 ⟨hv3, Eventually.of_forall fun n => (hv2 n).2⟩
            let : MeasurableSpace Sample := naturalFiltration t
            refine measurable_of_tendsto_metrizable (f := fun n ω => (X (v n) ω i : ℝ)) ?_ ?_
            · intro n
              have := (hXm (v n)).mono (naturalFiltration.mono (hv2 n).2.le) le_rfl
              exact (measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp this
            · rw [tendsto_pi_nhds]
              intro ω
              refine tendsto_const_nhds.congr' ?_
              filter_upwards [hvlim.eventually (key ω t ht0)] with n hn
              rw [hn.1]
        have hR := LEFT (fun t ω => (preX t ω i : ℝ)) hpm (by
          intro ω t ht
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [key ω t ht] with s hs
          rw [hs.2])
        let mm : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
        have := Nat.measurable_floor.comp hR
        have e : (fun p : ℝ≥0 × Sample => preX p.1 p.2 i) =
            (fun p : ℝ≥0 × Sample => ⌊(preX p.1 p.2 i : ℝ)⌋₊) := by
          funext p; simp
        rw [e]; exact this
      have FEED : ∀ G : Game, G.Standing → ∀ f : ValueField, (∀ x, Measurable (fun s => f s x)) →
          (∀ s x, f s x ∈ Icc G.lower G.upper) → G.Feedback f := by
        clear hG G ODE1 ODE2 REAL PATHSUM INDEP COMP COMPREAL MOM NOCOMMON
        intro G hG f hm hb
        have hU : Measurable (fun p : ℝ × State => f p.1 p.2) := measurable_from_prod_countable_left hm
        refine ⟨?_, fun s _ x => hb s x, fun x => ⟨?_, ?_⟩⟩
        · exact hU.comp (measurable_subtype_coe.prodMap measurable_id)
        · have htime : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => (p.1 : ℝ)) :=
            LEFT (fun t _ => (t : ℝ)) (fun t => measurable_const) (fun ω t _ =>
              (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds)
          have hpre := PREX
          let mm : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
          have hst : Measurable (fun p : ℝ≥0 × Sample => (fun i => x i + preX p.1 p.2 i : State)) :=
            measurable_pi_iff.2 fun i => (measurable_from_top (f := fun k : ℕ => x i + k)).comp (hpre i)
          have hmain : Measurable (fun p : ℝ≥0 × Sample => if (p.1 : ℝ) ≤ G.h then
              f p.1 (fun i => x i + preX p.1 p.2 i) else G.lower) :=
            Measurable.ite (measurableSet_le htime measurable_const)
              (hU.comp (htime.prodMk hst)) measurable_const
          exact hmain.stronglyMeasurable
        · intro t ω
          unfold Game.liftFeedback
          split_ifs
          · exact hb _ _
          · exact ⟨le_rfl, hG.2.2.1⟩
      have PREDL : ∀ Lp : Game → Process → Process → Process,
          (∀ G a b (t : ℝ≥0) ω, Lp G a b t ω = Real.exp (
            (∑ᶠ s ∈ jumps G.h ω 0 ∩ Iio (t : ℝ), Real.log (a (Real.toNNReal s) ω / G.rate)) +
            (∑ᶠ s ∈ jumps G.h ω 1 ∩ Iio (t : ℝ), Real.log (b (Real.toNNReal s) ω / G.rate)) -
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)))) →
          ∀ G : Game, G.Standing → ∀ a b, G.Admissible a → G.Admissible b →
          Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => Lp G a b p.1 p.2) ∧
          Measurable (G.logLikelihood a b) := by
        clear hG G ODE1 ODE2 REAL PATHSUM INDEP COMPREAL MOM NOCOMMON PREX FEED
        intro Lp hLp G hG a b ha hb
        obtain ⟨hh, hl, hlu, hr, hru, hP⟩ := hG
        have hG : G.Standing := ⟨hh, hl, hlu, hr, hru, hP⟩
        have hfst : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => p.1) := by
          let _ : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
          refine measurable_of_Ioi ?_
          intro x
          have : (fun p : ℝ≥0 × Sample => p.1) ⁻¹' Ioi x = Ioi x ×ˢ (univ : Set Sample) := by
            ext p; simp
          rw [this]
          exact measurableSet_predictable_Ioi_prod (@MeasurableSet.univ _ (naturalFiltration x))
        have hjoint : naturalFiltration.predictable ≤ (Prod.instMeasurableSpace : MeasurableSpace (ℝ≥0 × Sample)) := by
          refine measurableSpace_le_predictable_of_measurableSet ?_ ?_
          · intro A hA
            exact (measurableSet_singleton _).prod (naturalFiltration.le _ _ hA)
          · intro i A hA
            exact measurableSet_Ioi.prod (naturalFiltration.le _ _ hA)
        -- finite sums via positive and negative parts
        have hfin : ∀ (J : Set ℝ), J.Finite → ∀ g : ℝ → ℝ, ∑ᶠ s ∈ J, g s =
            (∑' s : J, ENNReal.ofReal (g s)).toReal - (∑' s : J, ENNReal.ofReal (-g s)).toReal := by
          intro J hJ g
          have key : ∀ g : ℝ → ℝ, (∑' s : J, ENNReal.ofReal (g s)).toReal = ∑ s ∈ hJ.toFinset, max (g s) 0 := by
            intro g
            have e : (∑' s : J, ENNReal.ofReal (g s)) = ∑ s ∈ hJ.toFinset, ENNReal.ofReal (g s) := by
              rw [tsum_subtype J (fun s => ENNReal.ofReal (g s)), tsum_eq_sum (s := hJ.toFinset)]
              · refine Finset.sum_congr rfl ?_
                intro s hs
                rw [indicator_of_mem]
                simpa using hs
              · intro s hs
                rw [indicator_of_notMem]
                simpa using hs
            rw [e, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
            refine Finset.sum_congr rfl ?_
            intro s _
            rw [ENNReal.toReal_ofReal']
          rw [key g, key (fun s => -g s), ← Finset.sum_sub_distrib, finsum_mem_eq_finite_toFinset_sum _ hJ]
          refine Finset.sum_congr rfl ?_
          intro s _
          exact (max_zero_sub_eq_self (g s)).symm
        have hSg : ∀ i, ∀ g : ℝ≥0 × Sample → ℝ, Measurable[naturalFiltration.predictable] g → ∀ T : ℝ≥0,
            Measurable[naturalFiltration T] (fun ω => ∑ᶠ s ∈ jumps T ω i, g (Real.toNNReal s, ω)) := by
          intro i g hg T
          have e : (fun ω => ∑ᶠ s ∈ jumps T ω i, g (Real.toNNReal s, ω)) = fun ω =>
              (∑' s : jumps T ω i, ENNReal.ofReal (g (Real.toNNReal s, ω))).toReal -
              (∑' s : jumps T ω i, ENNReal.ofReal (-g (Real.toNNReal s, ω))).toReal := by
            funext ω
            exact hfin _ ((PATHS ω i).1 T) _
          rw [e]
          have h1 := (COMP G hG i (fun p => ENNReal.ofReal (g p))
            (ENNReal.measurable_ofReal.comp hg)).1 T
          have h2 := (COMP G hG i (fun p => ENNReal.ofReal (-g p))
            (ENNReal.measurable_ofReal.comp (measurable_neg.comp hg))).1 T
          exact (ENNReal.measurable_toReal.comp h1).sub (ENNReal.measurable_toReal.comp h2)
        have hlog : ∀ φ : Process, G.Admissible φ → Measurable[naturalFiltration.predictable]
            (fun p : ℝ≥0 × Sample => Real.log (φ p.1 p.2 / G.rate)) := by
          intro φ hφ
          have h1 : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => φ p.1 p.2) :=
            hφ.1.measurable
          exact Real.measurable_log.comp ((measurable_id.div_const G.rate).comp h1)
        have hSt : ∀ i, ∀ φ : Process, G.Admissible φ → ∀ t : ℝ≥0, Measurable[naturalFiltration t]
            (fun ω => ∑ᶠ s ∈ jumps G.h ω i ∩ Iio (t : ℝ), Real.log (φ (Real.toNNReal s) ω / G.rate)) := by
          intro i φ hφ t
          have hset : MeasurableSet[naturalFiltration.predictable]
              {p : ℝ≥0 × Sample | (p.1 : ℝ) ≤ G.h ∧ p.1 < t} := by
            have hs : MeasurableSet {q : ℝ≥0 | (q : ℝ) ≤ G.h ∧ q < t} :=
              (measurableSet_le measurable_coe_nnreal_real measurable_const).inter measurableSet_Iio
            exact hfst hs
          have hg : Measurable[naturalFiltration.predictable] ({p : ℝ≥0 × Sample | (p.1 : ℝ) ≤ G.h ∧ p.1 < t}.indicator
                  (fun p : ℝ≥0 × Sample => Real.log (φ p.1 p.2 / G.rate))) := by
            have hl0 := hlog φ hφ
            let _ : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
            exact hl0.indicator hset
          have h1 := hSg i _ hg t
          have e : (fun ω => ∑ᶠ s ∈ jumps G.h ω i ∩ Iio (t : ℝ), Real.log (φ (Real.toNNReal s) ω / G.rate))
              = (fun ω => ∑ᶠ s ∈ jumps t ω i, ({p : ℝ≥0 × Sample | (p.1 : ℝ) ≤ G.h ∧ p.1 < t}.indicator
                  (fun p : ℝ≥0 × Sample => Real.log (φ p.1 p.2 / G.rate))) (Real.toNNReal s, ω)) := by
            funext ω
            rw [finsum_mem_def, finsum_mem_def]
            refine finsum_congr ?_
            intro s
            by_cases hs : s ∈ jumps G.h ω i ∩ Iio (t : ℝ)
            · have hs2 : s ∈ jumps t ω i := ⟨hs.1.1, le_of_lt hs.2, hs.1.2.2⟩
              have hs0 : 0 < s := hs.1.1
              have hc : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0.le
              have hs3 : (Real.toNNReal s, ω) ∈ {p : ℝ≥0 × Sample | (p.1 : ℝ) ≤ G.h ∧ p.1 < t} := by
                refine ⟨?_, ?_⟩
                · show ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ G.h
                  rw [hc]; exact hs.1.2.1
                · show Real.toNNReal s < t
                  rw [← NNReal.coe_lt_coe, hc]; exact hs.2
              rw [indicator_of_mem hs, indicator_of_mem hs2, indicator_of_mem hs3]
            · rw [indicator_of_notMem hs]
              by_cases hs2 : s ∈ jumps t ω i
              · rw [indicator_of_mem hs2]
                rw [indicator_of_notMem]
                rintro ⟨h3, h4⟩
                apply hs
                have hs0 : 0 < s := hs2.1
                have hc : ((Real.toNNReal s : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0.le
                refine ⟨⟨hs0, ?_, hs2.2.2⟩, ?_⟩
                · have h3' : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ G.h := h3
                  rwa [hc] at h3'
                · have h4' : Real.toNNReal s < t := h4
                  rw [← NNReal.coe_lt_coe, hc] at h4'; exact h4'
              · rw [indicator_of_notMem hs2]
          rw [e]; exact h1
        -- integral part
        have hint : ∀ (Ω : Type) (m : MeasurableSpace Ω) (g : ℝ × Ω → ℝ), Measurable g →
            ∀ A : Set ℝ, Measurable (fun ω => ∫ s in A, g (s, ω)) := by
          intro Ω m g hg A
          exact (hg.stronglyMeasurable.integral_prod_left' (μ := volume.restrict A)).measurable
        have hI : ∀ t : ℝ≥0, Measurable[naturalFiltration t] (fun ω =>
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate))) := by
          intro t
          have hm : ∀ φ : Process, G.Admissible φ →
              @Measurable (ℝ × Sample) ℝ (@Prod.instMeasurableSpace ℝ Sample _ (naturalFiltration t)) _
                (fun q : ℝ × Sample => φ (min (Real.toNNReal q.1) t) q.2) := by
            intro φ hφ
            have h1 := (hφ.1.isStronglyProgressive t).measurable
            have h2 : @Measurable (ℝ × Sample) (Set.Iic t × Sample)
                (@Prod.instMeasurableSpace ℝ Sample _ (naturalFiltration t))
                (@Prod.instMeasurableSpace (Set.Iic t) Sample _ (naturalFiltration t))
                (fun q => (⟨min (Real.toNNReal q.1) t, mem_Iic.2 (min_le_right _ _)⟩, q.2)) := by
              letI : MeasurableSpace Sample := naturalFiltration t
              refine Measurable.prodMk ?_ measurable_snd
              refine Measurable.subtype_mk ?_
              exact (measurable_real_toNNReal.comp measurable_fst).min measurable_const
            exact h1.comp h2
          have h3 := hint Sample (naturalFiltration t)
            (fun q => (a (min (Real.toNNReal q.1) t) q.2 - G.rate) + (b (min (Real.toNNReal q.1) t) q.2 - G.rate))
            (((hm a ha).sub_const _).add ((hm b hb).sub_const _)) (Icc (0:ℝ) t)
          have e : (fun ω =>
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate))) =
            (fun ω => ∫ s in Icc (0:ℝ) t, ((a (min (Real.toNNReal s) t) ω - G.rate) + (b (min (Real.toNNReal s) t) ω - G.rate))) := by
            funext ω
            refine setIntegral_congr_fun measurableSet_Icc ?_
            intro s hs
            have : min (Real.toNNReal s) t = Real.toNNReal s := by
              refine min_eq_left ?_
              rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
              exact hs.2
            simp only [this]
          rw [e]; exact h3
        -- left continuity
        have hSl : ∀ i, ∀ φ : Process, ∀ ω, ∀ t : ℝ≥0, 0 < t → Tendsto
            (fun s : ℝ≥0 => ∑ᶠ q ∈ jumps G.h ω i ∩ Iio (s : ℝ), Real.log (φ (Real.toNNReal q) ω / G.rate)) (𝓝[<] t)
            (𝓝 (∑ᶠ q ∈ jumps G.h ω i ∩ Iio (t : ℝ), Real.log (φ (Real.toNNReal q) ω / G.rate))) := by
          intro i φ ω t ht
          refine Tendsto.congr' ?_ tendsto_const_nhds
          have h1 : ∀ᶠ s : ℝ≥0 in 𝓝[<] t, ∀ q ∈ jumps G.h ω i, q < t → q < s := by
            rw [eventually_all_finite ((PATHS ω i).1 G.h)]
            intro q hq
            by_cases hqt : q < t
            · have : Tendsto (fun s : ℝ≥0 => (s : ℝ)) (𝓝[<] t) (𝓝 (t : ℝ)) :=
                (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
              filter_upwards [this.eventually (lt_mem_nhds hqt)] with s hs _ using hs
            · exact Eventually.of_forall fun s h => absurd h hqt
          filter_upwards [h1, self_mem_nhdsWithin] with s hs hst
          have : jumps G.h ω i ∩ Iio (t : ℝ) = jumps G.h ω i ∩ Iio (s : ℝ) := by
            ext q
            constructor
            · rintro ⟨h2, h3⟩
              exact ⟨h2, hs q h2 h3⟩
            · rintro ⟨h2, h3⟩
              have hst' : (s : ℝ) < t := NNReal.coe_lt_coe.2 hst
              exact ⟨h2, lt_trans h3 hst'⟩
          rw [this]
        have hIl : ∀ ω, ∀ t : ℝ≥0, Tendsto
            (fun u : ℝ≥0 => ∫ s in Icc (0 : ℝ) u, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate))) (𝓝[<] t)
            (𝓝 (∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)))) := by
          intro ω t
          have hm : ∀ φ : Process, G.Admissible φ → Measurable (fun s : ℝ => φ (Real.toNNReal s) ω) := by
            intro φ hφ
            have h1 : Measurable (fun p : ℝ≥0 × Sample => φ p.1 p.2) := by
              have h0 : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => φ p.1 p.2) :=
                hφ.1.measurable
              exact h0.mono hjoint le_rfl
            exact h1.comp (measurable_real_toNNReal.prodMk measurable_const)
          have hf : Measurable (fun s : ℝ => (a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)) :=
            ((hm a ha).sub_const _).add ((hm b hb).sub_const _)
          have hii : ∀ p q : ℝ, IntervalIntegrable
              (fun s : ℝ => (a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)) volume p q := by
            intro p q
            refine (intervalIntegrable_const (c := 2 * G.upper + 2 * G.rate)).mono_fun
              hf.aestronglyMeasurable ?_
            refine Eventually.of_forall ?_
            intro s
            have h1 := ha.2 (Real.toNNReal s) ω
            have h2 := hb.2 (Real.toNNReal s) ω
            simp only [Real.norm_eq_abs]
            refine le_trans ?_ (le_abs_self _)
            rw [abs_le]
            constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
          have hc := intervalIntegral.continuous_primitive hii 0
          have e : ∀ u : ℝ≥0, ∫ s in Icc (0 : ℝ) u, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate))
              = ∫ s in (0:ℝ)..u, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)) := by
            intro u
            rw [intervalIntegral.integral_of_le u.coe_nonneg, integral_Icc_eq_integral_Ioc]
          simp only [e]
          exact ((hc.comp NNReal.continuous_coe).tendsto t).mono_left nhdsWithin_le_nhds
        refine ⟨?_, ?_⟩
        · have hZ := LEFT (fun t ω =>
            (∑ᶠ s ∈ jumps G.h ω 0 ∩ Iio (t : ℝ), Real.log (a (Real.toNNReal s) ω / G.rate)) +
            (∑ᶠ s ∈ jumps G.h ω 1 ∩ Iio (t : ℝ), Real.log (b (Real.toNNReal s) ω / G.rate)) -
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)))
            (fun t => ((hSt 0 a ha t).add (hSt 1 b hb t)).sub (hI t))
            (fun ω t ht => ((hSl 0 a ω t ht).add (hSl 1 b ω t ht)).sub (hIl ω t))
          have e : (fun p : ℝ≥0 × Sample => Lp G a b p.1 p.2) = fun p : ℝ≥0 × Sample => Real.exp (
            (∑ᶠ s ∈ jumps G.h p.2 0 ∩ Iio (p.1 : ℝ), Real.log (a (Real.toNNReal s) p.2 / G.rate)) +
            (∑ᶠ s ∈ jumps G.h p.2 1 ∩ Iio (p.1 : ℝ), Real.log (b (Real.toNNReal s) p.2 / G.rate)) -
            ∫ s in Icc (0 : ℝ) p.1, ((a (Real.toNNReal s) p.2 - G.rate) + (b (Real.toNNReal s) p.2 - G.rate))) := by
            funext p
            exact hLp G a b p.1 p.2
          rw [e]
          exact Real.measurable_exp.comp hZ
        · have hc : ((Real.toNNReal G.h : ℝ≥0) : ℝ) = G.h := Real.coe_toNNReal _ hh
          have h0 := (hSg 0 _ (hlog a ha) (Real.toNNReal G.h)).mono (naturalFiltration.le _) le_rfl
          have h1 := (hSg 1 _ (hlog b hb) (Real.toNNReal G.h)).mono (naturalFiltration.le _) le_rfl
          have h2 := (hI (Real.toNNReal G.h)).mono (naturalFiltration.le _) le_rfl
          rw [hc] at h0 h1 h2
          exact (h0.add h1).sub h2
      have LBOUND : ∀ Lp : Game → Process → Process → Process,
          (∀ G a b (t : ℝ≥0) ω, Lp G a b t ω = Real.exp (
            (∑ᶠ s ∈ jumps G.h ω 0 ∩ Iio (t : ℝ), Real.log (a (Real.toNNReal s) ω / G.rate)) +
            (∑ᶠ s ∈ jumps G.h ω 1 ∩ Iio (t : ℝ), Real.log (b (Real.toNNReal s) ω / G.rate)) -
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)))) →
          ∀ G : Game, G.Standing → ∀ a b, G.Admissible a → G.Admissible b → ∀ ω,
          Real.exp (G.logLikelihood a b ω) ≤ Real.exp (2 * G.rate * G.h) *
            (G.upper / G.rate) ^ (X (Real.toNNReal G.h) ω 0 + X (Real.toNNReal G.h) ω 1) ∧
          ∀ t : ℝ≥0, (t : ℝ) ≤ G.h → Lp G a b t ω ≤ Real.exp (2 * G.rate * G.h) *
            (G.upper / G.rate) ^ (X (Real.toNNReal G.h) ω 0 + X (Real.toNNReal G.h) ω 1) ∧
            preX t ω 0 ≤ X (Real.toNNReal G.h) ω 0 ∧ preX t ω 1 ≤ X (Real.toNNReal G.h) ω 1 := by
        clear hG G ODE1 ODE2 REAL PATHSUM INDEP COMP COMPREAL MOM NOCOMMON LEFT PREX FEED PREDL
        intro Lp hLp G hG a b ha hb ω
        obtain ⟨hh, hl, hlu, hr, hru, hP⟩ := hG
        have hq : 1 ≤ G.upper / G.rate := by rw [le_div_iff₀ hr]; linarith
        have hlog0 : 0 ≤ Real.log (G.upper / G.rate) := Real.log_nonneg hq
        have hlog : ∀ c : Process, G.Admissible c → ∀ t : ℝ≥0,
            Real.log (c t ω / G.rate) ≤ Real.log (G.upper / G.rate) := by
          intro c hc t
          have h1 := hc.2 t ω
          apply Real.log_le_log
          · exact div_pos (by linarith [h1.1]) hr
          · exact div_le_div_of_nonneg_right h1.2 hr.le
        have hN : ∀ i, X (Real.toNNReal G.h) ω i = (jumps G.h ω i).ncard := by
          intro i
          have := (PATHS ω i).2.1 (Real.toNNReal G.h)
          rwa [Real.coe_toNNReal _ hh] at this
        have hsum : ∀ c : Process, G.Admissible c → ∀ i, ∀ S : Set ℝ, S ⊆ jumps G.h ω i →
            (∑ᶠ s ∈ S, Real.log (c (Real.toNNReal s) ω / G.rate)) ≤
              (X (Real.toNNReal G.h) ω i : ℝ) * Real.log (G.upper / G.rate) := by
          intro c hc i S hS
          have hf : S.Finite := ((PATHS ω i).1 G.h).subset hS
          rw [finsum_mem_eq_finite_toFinset_sum _ hf]
          refine (Finset.sum_le_card_nsmul _ _ _ (fun s _ => hlog c hc _)).trans ?_
          rw [nsmul_eq_mul]
          apply mul_le_mul_of_nonneg_right _ hlog0
          rw [← Set.ncard_eq_toFinset_card _ hf, hN i]
          exact_mod_cast Set.ncard_le_ncard hS ((PATHS ω i).1 G.h)
        have hint : ∀ t : ℝ, 0 ≤ t → t ≤ G.h → -(2 * G.rate * G.h) ≤
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)) := by
          intro t ht0 hth
          have h1 : -(2 * G.rate * G.h) ≤ ∫ s in Icc (0 : ℝ) t, (-(2 * G.rate) : ℝ) := by
            rw [MeasureTheory.setIntegral_const]
            simp only [Measure.real, Real.volume_Icc, sub_zero, smul_eq_mul, ENNReal.toReal_ofReal ht0]
            nlinarith
          by_cases hi : IntegrableOn (fun s => ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate))) (Icc (0:ℝ) t)
          · refine h1.trans (integral_mono ?_ hi ?_)
            · exact integrable_const _
            · intro s
              have h2 := (ha.2 (Real.toNNReal s) ω).1
              have h3 := (hb.2 (Real.toNNReal s) ω).1
              show -(2 * G.rate) ≤ (a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)
              linarith
          · rw [integral_undef hi]
            have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hr.le) hh
            linarith
        have hexp : Real.exp (2 * G.rate * G.h) *
            (G.upper / G.rate) ^ (X (Real.toNNReal G.h) ω 0 + X (Real.toNNReal G.h) ω 1) =
            Real.exp ((X (Real.toNNReal G.h) ω 0 : ℝ) * Real.log (G.upper / G.rate) +
              (X (Real.toNNReal G.h) ω 1 : ℝ) * Real.log (G.upper / G.rate) + 2 * G.rate * G.h) := by
          rw [Real.exp_add, ← add_mul, mul_comm]
          congr 1
          rw [mul_comm, Real.exp_mul, Real.exp_log (by linarith)]
          rw [← Real.rpow_natCast]
          push_cast
          rfl
        refine ⟨?_, ?_⟩
        · rw [hexp, Real.exp_le_exp]
          unfold Game.logLikelihood
          have h1 := hsum a ha 0 _ subset_rfl
          have h2 := hsum b hb 1 _ subset_rfl
          have h3 := hint G.h hh le_rfl
          linarith
        · intro t ht
          refine ⟨?_, ?_, ?_⟩
          · rw [hLp, hexp, Real.exp_le_exp]
            have h1 := hsum a ha 0 (jumps G.h ω 0 ∩ Iio (t : ℝ)) inter_subset_left
            have h2 := hsum b hb 1 (jumps G.h ω 1 ∩ Iio (t : ℝ)) inter_subset_left
            have h3 := hint t t.2 ht
            linarith
          all_goals
            rw [(PATHS ω _).2.2 t, hN]
            apply Set.ncard_le_ncard _ ((PATHS ω _).1 G.h)
            rintro s ⟨⟨hs1, hs2, hs3⟩, hs4⟩
            exact ⟨hs1, hs2.trans ht, hs3⟩
      have VERIF1 : ∀ Lp : Game → Process → Process → Process,
          (∀ G a b (t : ℝ≥0) ω, Lp G a b t ω = Real.exp (
            (∑ᶠ s ∈ jumps G.h ω 0 ∩ Iio (t : ℝ), Real.log (a (Real.toNNReal s) ω / G.rate)) +
            (∑ᶠ s ∈ jumps G.h ω 1 ∩ Iio (t : ℝ), Real.log (b (Real.toNNReal s) ω / G.rate)) -
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)))) →
          ∀ G : Game, G.Standing → ∀ a b, G.Admissible a → G.Admissible b →
          ∀ (x : State) (V w : ℝ → State → ℝ) (C : ℝ),
          (∀ y, Continuous (fun t => V t y)) → (∀ y, Measurable (fun t => w t y)) →
          (∀ t y, |V t y| ≤ C * 2 ^ (y 0 + y 1)) → (∀ t y, |w t y| ≤ C * 2 ^ (y 0 + y 1)) →
          (∀ y s t, 0 ≤ s → s ≤ t → t ≤ G.h → V t y - V s y = ∫ r in s..t, w r y) →
          ∀ Y : ℝ≥0 → Sample → State, (∀ t ω, Y t ω = fun j => x j + preX t ω j) →
          ∀ᵐ ω ∂G.P, Real.exp (G.logLikelihood a b ω) * V G.h (fun j => x j + X (Real.toNNReal G.h) ω j) =
            V 0 x + (∑ᶠ t ∈ jumps G.h ω 0, Lp G a b (Real.toNNReal t) ω *
                (a (Real.toNNReal t) ω / G.rate * V t (Function.update (Y (Real.toNNReal t) ω) 0 (Y (Real.toNNReal t) ω 0 + 1))
                  - V t (Y (Real.toNNReal t) ω)))
            + (∑ᶠ t ∈ jumps G.h ω 1, Lp G a b (Real.toNNReal t) ω *
                (b (Real.toNNReal t) ω / G.rate * V t (Function.update (Y (Real.toNNReal t) ω) 1 (Y (Real.toNNReal t) ω 1 + 1))
                  - V t (Y (Real.toNNReal t) ω)))
            + ∫ t in Icc (0:ℝ) G.h, Lp G a b (Real.toNNReal t) ω * (w t (Y (Real.toNNReal t) ω)
                - ((a (Real.toNNReal t) ω - G.rate) + (b (Real.toNNReal t) ω - G.rate)) * V t (Y (Real.toNNReal t) ω)) := by
        clear hG G ODE1 ODE2 REAL INDEP COMP COMPREAL MOM LEFT PREX FEED PREDL LBOUND
        intro Lp hLp G hG a b ha hb x V w C hVc hwm hVb hwb hVw Y hY
        obtain ⟨hh, hl, hlu, hr, hru, hP⟩ := id hG
        filter_upwards [NOCOMMON G hG] with ω hdis
        have hpath : ∀ c : Process, G.Admissible c → Measurable (fun t : ℝ => c (Real.toNNReal t) ω) := by
          intro c hc
          have hle : naturalFiltration.predictable ≤
              (inferInstance : MeasurableSpace (ℝ≥0 × Sample)) := by
            apply measurableSpace_le_predictable_of_measurableSet
            · intro A hA
              exact (measurableSet_singleton _).prod (naturalFiltration.le _ _ hA)
            · intro i A hA
              exact measurableSet_Ioi.prod (naturalFiltration.le _ _ hA)
          have h1 : Measurable (Function.uncurry c) := (StronglyMeasurable.measurable hc.1).mono hle le_rfl
          exact h1.comp (measurable_real_toNNReal.prodMk measurable_const)
        have hfin : ∀ i, (jumps G.h ω i).Finite := fun i => (PATHS ω i).1 G.h
        have hN : ∀ i, X (Real.toNNReal G.h) ω i = (hfin i).toFinset.card := by
          intro i
          have := (PATHS ω i).2.1 (Real.toNNReal G.h)
          rw [Real.coe_toNNReal _ hh] at this
          rw [this, Set.ncard_eq_toFinset_card _ (hfin i)]
        have hpre : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ G.h → preX (Real.toNNReal t) ω i =
            ((hfin i).toFinset.filter (· < t)).card := by
          intro i t ht0 hth
          rw [(PATHS ω i).2.2, Real.coe_toNNReal _ ht0, ← Set.ncard_coe_finset]
          congr 1
          ext s
          simp only [mem_inter_iff, mem_Iio, Finset.coe_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨h1, h2, h3⟩, h4⟩
            exact ⟨⟨h1, h2.trans hth, h3⟩, h4⟩
          · rintro ⟨⟨h1, h2, h3⟩, h4⟩
            exact ⟨⟨h1, h4.le, h3⟩, h4⟩
        have hsumpre : ∀ i, ∀ t : ℝ, ∀ f : ℝ → ℝ, (∑ᶠ s ∈ jumps G.h ω i ∩ Iio t, f s) =
            ∑ s ∈ (hfin i).toFinset with s < t, f s := by
          intro i t f
          have hset : jumps G.h ω i ∩ Iio t = ↑((hfin i).toFinset.filter (· < t)) := by
            ext s
            simp
          rw [hset, finsum_mem_coe_finset]
        have hsumfull : ∀ i, ∀ f : ℝ → ℝ, (∑ᶠ s ∈ jumps G.h ω i, f s) =
            ∑ s ∈ (hfin i).toFinset, f s := fun i f => finsum_mem_eq_finite_toFinset_sum _ (hfin i)
        have key := PATHSUM G.h G.lower G.upper G.rate 0 (hfin 0).toFinset (hfin 1).toFinset
          (fun t => a (Real.toNNReal t) ω) (fun t => b (Real.toNNReal t) ω) V w x hh hl hr
          (by intro t ht; rw [Set.Finite.mem_toFinset] at ht; exact ⟨ht.1, ht.2.1⟩)
          (by intro t ht; rw [Set.Finite.mem_toFinset] at ht; exact ⟨ht.1, ht.2.1⟩)
          (by rw [Finset.disjoint_left]; intro t h0 h1
              rw [Set.Finite.mem_toFinset] at h0 h1
              exact Set.disjoint_left.mp hdis h0 h1)
          (hpath a ha) (hpath b hb) (fun t => ha.2 _ _) (fun t => hb.2 _ _) hwm
          (fun y => ⟨_, fun t => hwb t y⟩) hVw _ _ (fun t => rfl) (fun t => rfl)
        have hL : ∀ t : ℝ, 0 ≤ t → Lp G a b (Real.toNNReal t) ω = Real.exp
            ((∑ s ∈ (hfin 0).toFinset with s < t, Real.log (a (Real.toNNReal s) ω / G.rate)) +
             (∑ s ∈ (hfin 1).toFinset with s < t, Real.log (b (Real.toNNReal s) ω / G.rate)) -
             ∫ s in Icc (0:ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate))) := by
          intro t ht
          rw [hLp, Real.coe_toNNReal _ ht, hsumpre 0 t, hsumpre 1 t]
        have hYY : ∀ t : ℝ, 0 ≤ t → t ≤ G.h → Y (Real.toNNReal t) ω = fun j => x j +
            (if j = 0 then ((hfin 0).toFinset.filter (· < t)).card
              else ((hfin 1).toFinset.filter (· < t)).card) := by
          intro t ht hth
          rw [hY]
          funext j
          rw [hpre j t ht hth]
          fin_cases j <;> simp
        have hXX : (fun j => x j + X (Real.toNNReal G.h) ω j) =
            (fun j => x j + (if j = 0 then (hfin 0).toFinset.card else (hfin 1).toFinset.card)) := by
          funext j
          rw [hN j]
          fin_cases j <;> simp
        have hLL : G.logLikelihood a b ω = (∑ s ∈ (hfin 0).toFinset, Real.log (a (Real.toNNReal s) ω / G.rate)) +
             (∑ s ∈ (hfin 1).toFinset, Real.log (b (Real.toNNReal s) ω / G.rate)) -
             ∫ s in Icc (0:ℝ) G.h, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)) := by
          unfold Game.logLikelihood
          rw [hsumfull 0, hsumfull 1]
        rw [hLL, hXX, key, hsumfull 0, hsumfull 1]
        congr 1
        · congr 1
          · congr 1
            apply Finset.sum_congr rfl
            intro t ht
            rw [Set.Finite.mem_toFinset] at ht
            rw [hL t ht.1.le, hYY t ht.1.le ht.2.1]
          · apply Finset.sum_congr rfl
            intro t ht
            rw [Set.Finite.mem_toFinset] at ht
            rw [hL t ht.1.le, hYY t ht.1.le ht.2.1]
        · apply setIntegral_congr_fun measurableSet_Icc
          intro t ht
          show _ = _
          beta_reduce
          rw [hL t ht.1, hYY t ht.1 ht.2]
      have VERIF2 : ∀ Lp : Game → Process → Process → Process,
          (∀ G a b (t : ℝ≥0) ω, Lp G a b t ω = Real.exp (
            (∑ᶠ s ∈ jumps G.h ω 0 ∩ Iio (t : ℝ), Real.log (a (Real.toNNReal s) ω / G.rate)) +
            (∑ᶠ s ∈ jumps G.h ω 1 ∩ Iio (t : ℝ), Real.log (b (Real.toNNReal s) ω / G.rate)) -
            ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)))) →
          ∀ G : Game, G.Standing → ∀ a b, G.Admissible a → G.Admissible b →
          ∀ (x : State) (V w : ℝ → State → ℝ) (C : ℝ),
          (∀ y, Continuous (fun t => V t y)) → (∀ y, Measurable (fun t => w t y)) →
          (∀ t y, |V t y| ≤ C * 2 ^ (y 0 + y 1)) → (∀ t y, |w t y| ≤ C * 2 ^ (y 0 + y 1)) →
          (∀ y s t, 0 ≤ s → s ≤ t → t ≤ G.h → V t y - V s y = ∫ r in s..t, w r y) →
          ∀ Y : ℝ≥0 → Sample → State, (∀ t ω, Y t ω = fun j => x j + preX t ω j) →
          ∫ ω, Real.exp (G.logLikelihood a b ω) * V G.h (fun j => x j + X (Real.toNNReal G.h) ω j) ∂G.P =
            V 0 x + ∫ ω, (∫ t in Icc (0:ℝ) G.h, Lp G a b (Real.toNNReal t) ω *
              (a (Real.toNNReal t) ω * D 0 V t (Y (Real.toNNReal t) ω)
                + b (Real.toNNReal t) ω * D 1 V t (Y (Real.toNNReal t) ω)
                + w t (Y (Real.toNNReal t) ω))) ∂G.P := by
        clear hG G ODE1 ODE2 PATHS REAL PATHSUM INDEP COMP NOCOMMON LEFT FEED
        intro Lp hLp G hG a b ha hb x V w C hVc hwm hVb hwb hVw Y hY
        have hh : 0 ≤ G.h := hG.1
        have hl : 0 < G.lower := hG.2.1
        have hr : 0 < G.rate := hG.2.2.2.1
        have hru : G.rate < G.upper := hG.2.2.2.2.1
        haveI hP : IsProbabilityMeasure G.P := hG.2.2.2.2.2.1
        have hu : 0 < G.upper := hr.trans hru
        have h02 : (0:ℝ) < 2 := zero_lt_two
        have hC : 0 ≤ C := by
          have h1 := (abs_nonneg (V 0 x)).trans (hVb 0 x)
          exact le_of_mul_le_mul_right ((zero_mul _).trans_le h1) (pow_pos h02 (x 0 + x 1))
        have hq : 1 ≤ G.upper / G.rate := (one_le_div hr).mpr hru.le
        have hq0 : 0 < G.upper / G.rate := div_pos hu hr
        have hle : naturalFiltration.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Sample)) := by
          refine measurableSpace_le_predictable_of_measurableSet ?_ ?_
          · intro A hA
            exact (measurableSet_singleton _).prod (naturalFiltration.le _ _ hA)
          · intro i A hA
            exact measurableSet_Ioi.prod (naturalFiltration.le _ _ hA)
        have hsec : ∀ H : ℝ≥0 × Sample → ℝ, Measurable[naturalFiltration.predictable] H → ∀ ω,
            Measurable (fun t : ℝ => H (Real.toNNReal t, ω)) := by
          intro H hH ω
          have h1 : Measurable H := hH.mono hle le_rfl
          exact h1.comp ((measurable_real_toNNReal).prodMk measurable_const)
        have hfst : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => p.1) := by
          letI : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
          refine measurable_of_Ioi (fun c => ?_)
          have : (fun p : ℝ≥0 × Sample => p.1) ⁻¹' Ioi c = Ioi c ×ˢ (univ : Set Sample) := by
            ext p; simp
          rw [this]
          exact measurableSet_predictable_Ioi_prod MeasurableSet.univ
        set N : Sample → ℕ := fun ω => X (Real.toNNReal G.h) ω 0 + X (Real.toNNReal G.h) ω 1 with hN
        set E : ℝ := Real.exp (2 * G.rate * G.h) with hE
        have hE0 : 0 < E := Real.exp_pos _
        have hLB := LBOUND Lp hLp G hG a b ha hb
        have hL0 : ∀ t ω, 0 ≤ Lp G a b t ω := by intro t ω; rw [hLp]; exact (Real.exp_pos _).le
        obtain ⟨hLm, -⟩ := PREDL Lp hLp G hG a b ha hb
        have hMOM := MOM G hG (G.upper / G.rate * 2) (mul_pos hq0 h02).le
        -- generic consequence of the bound
        have key : ∀ H : ℝ≥0 × Sample → ℝ, Measurable[naturalFiltration.predictable] H → ∀ M : ℝ, 0 ≤ M →
            (∀ (t : ℝ≥0) ω, (t : ℝ) ≤ G.h → |H (t, ω)| ≤ M * (G.upper / G.rate * 2) ^ N ω) →
            (∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal |H (Real.toNNReal t, ω)|) ∂G.P ≠ ⊤) ∧
            ∀ ω, IntegrableOn (fun t : ℝ => H (Real.toNNReal t, ω)) (Icc 0 G.h) := by
          intro H hH M hM hB
          constructor
          · have h1 : ∫⁻ ω, (∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal |H (Real.toNNReal t, ω)|) ∂G.P ≤
                ∫⁻ ω, ENNReal.ofReal (M * (G.upper / G.rate * 2) ^ N ω) * ENNReal.ofReal G.h ∂G.P := by
              refine lintegral_mono fun ω => ?_
              calc ∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal |H (Real.toNNReal t, ω)|
                  ≤ ∫⁻ t in Ioc (0:ℝ) G.h, ENNReal.ofReal (M * (G.upper / G.rate * 2) ^ N ω) := by
                    refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
                    refine ENNReal.ofReal_le_ofReal (hB _ _ ?_)
                    rw [Real.coe_toNNReal _ ht.1.le]; exact ht.2
                _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
            refine ne_top_of_le_ne_top ?_ h1
            have h2 : Integrable (fun ω => M * (G.upper / G.rate * 2) ^ N ω) G.P := hMOM.const_mul M
            rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
            exact ENNReal.mul_ne_top h2.lintegral_lt_top.ne ENNReal.ofReal_ne_top
          · intro ω
            refine Measure.integrableOn_of_bounded (M := M * (G.upper / G.rate * 2) ^ N ω) ?_
              (hsec H hH ω).aestronglyMeasurable ?_
            · exact measure_Icc_lt_top.ne
            · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
              rw [Real.norm_eq_abs]
              refine hB _ _ ?_
              rw [Real.coe_toNNReal _ ht.1]; exact ht.2
        -- measurability
        have hYm : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => Y p.1 p.2) := by
          have h1 : (fun p : ℝ≥0 × Sample => Y p.1 p.2) = fun p j => x j + preX p.1 p.2 j := by
            funext p; rw [hY]
          rw [h1]
          refine @measurable_pi_lambda _ _ _ naturalFiltration.predictable _ _ (fun j => ?_)
          exact @Measurable.comp _ _ _ naturalFiltration.predictable _ _ (fun n : ℕ => x j + n) _ (measurable_of_countable _) (PREX j)
        have hcomb : ∀ F : ℝ → State → ℝ, (∀ y, Measurable (fun t => F t y)) →
            ∀ g : State → State, Measurable[naturalFiltration.predictable]
              (fun p : ℝ≥0 × Sample => F p.1 (g (Y p.1 p.2))) := by
          intro F hF g
          have h1 : Measurable (fun q : ℝ × State => F q.1 q.2) :=
            measurable_from_prod_countable_left hF
          have h2 : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => ((p.1 : ℝ), g (Y p.1 p.2))) := by
            have m1 : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => (p.1 : ℝ)) :=
              @Measurable.comp _ _ _ naturalFiltration.predictable _ _ _ _ measurable_coe_nnreal_real hfst
            have m2 : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => g (Y p.1 p.2)) :=
              @Measurable.comp _ _ _ naturalFiltration.predictable _ _ _ _ (measurable_of_countable g) hYm
            letI : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
            exact m1.prodMk m2
          exact @Measurable.comp _ _ _ naturalFiltration.predictable _ _ _ _ h1 h2
        have ham : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => a p.1 p.2) :=
          ha.1.measurable
        have hbm : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => b p.1 p.2) :=
          hb.1.measurable
        have hVm : ∀ y, Measurable (fun t => V t y) := fun y => (hVc y).measurable
        -- growth
        have hYb : ∀ (t : ℝ≥0) ω, (t : ℝ) ≤ G.h → (2:ℝ) ^ (Y t ω 0 + Y t ω 1) ≤ 2 ^ (x 0 + x 1) * 2 ^ N ω := by
          intro t ω ht
          obtain ⟨-, h0, h1⟩ := (hLB ω).2 t ht
          rw [← pow_add, hY]
          refine pow_le_pow_right₀ (by norm_num) ?_
          simp only [hN]; omega
        have hLK : ∀ (t : ℝ≥0) ω, (t : ℝ) ≤ G.h → Lp G a b t ω ≤ E * (G.upper / G.rate) ^ N ω :=
          fun t ω ht => ((hLB ω).2 t ht).1
        set Z : ℝ := 2 ^ (x 0 + x 1) with hZ
        have hZ0 : 0 < Z := pow_pos h02 _
        have hmul : ∀ (t : ℝ≥0) ω (R K : ℝ), (t : ℝ) ≤ G.h → 0 ≤ K → |R| ≤ K * 2 ^ (Y t ω 0 + Y t ω 1) →
            |Lp G a b t ω * R| ≤ (E * K * Z) * (G.upper / G.rate * 2) ^ N ω := by
          intro t ω R K ht hK hR
          rw [abs_mul, abs_of_nonneg (hL0 t ω)]
          calc Lp G a b t ω * |R| ≤ (E * (G.upper / G.rate) ^ N ω) * (K * (Z * 2 ^ N ω)) := by
                refine mul_le_mul (hLK t ω ht) (hR.trans ?_) (abs_nonneg _) (mul_nonneg hE0.le (pow_nonneg hq0.le _))
                exact mul_le_mul_of_nonneg_left (hYb t ω ht) hK
            _ = _ := by rw [mul_pow]; ring
        have hup : ∀ (y : State) (i : Fin 2), Function.update y i (y i + 1) 0 + Function.update y i (y i + 1) 1
            = y 0 + y 1 + 1 := by
          intro y i
          rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
          · rw [Function.update_self, Function.update_of_ne (show (1 : Fin 2) ≠ 0 from one_ne_zero)]; omega
          · rw [Function.update_self, Function.update_of_ne (show (0 : Fin 2) ≠ 1 from zero_ne_one)]; omega
        have hab1 : ∀ c : Process, G.Admissible c → ∀ t ω, |c t ω| ≤ G.upper := by
          intro c hc t ω
          rw [abs_of_nonneg (hl.le.trans (hc.2 t ω).1)]
          exact (hc.2 t ω).2
        let J : Fin 2 → Process → ℝ≥0 × Sample → ℝ := fun i c p => Lp G a b p.1 p.2 *
          (c p.1 p.2 / G.rate * V p.1 (Function.update (Y p.1 p.2) i (Y p.1 p.2 i + 1)) - V p.1 (Y p.1 p.2))
        let Hc : ℝ≥0 × Sample → ℝ := fun p => Lp G a b p.1 p.2 * (w p.1 (Y p.1 p.2)
          - ((a p.1 p.2 - G.rate) + (b p.1 p.2 - G.rate)) * V p.1 (Y p.1 p.2))
        have hJm : ∀ i c, G.Admissible c → Measurable[naturalFiltration.predictable] (J i c) := by
          intro i c hc
          have hcm : Measurable[naturalFiltration.predictable] (fun p : ℝ≥0 × Sample => c p.1 p.2) :=
            hc.1.measurable
          letI : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
          exact hLm.mul (((hcm.div_const _).mul (hcomb V hVm (fun y => Function.update y i (y i + 1)))).sub
            (hcomb V hVm id))
        have hHcm : Measurable[naturalFiltration.predictable] Hc := by
          letI : MeasurableSpace (ℝ≥0 × Sample) := naturalFiltration.predictable
          exact hLm.mul ((hcomb w hwm id).sub
            (((ham.sub_const _).add (hbm.sub_const _)).mul (hcomb V hVm id)))
        obtain ⟨K0, hK0⟩ : ∃ K0, K0 = G.upper / G.rate * (C * 2) + C := ⟨_, rfl⟩
        obtain ⟨K1, hK1⟩ : ∃ K1, K1 = C + (2 * (G.upper + G.rate)) * C := ⟨_, rfl⟩
        have hK00 : 0 ≤ K0 := hK0 ▸ add_nonneg (mul_nonneg hq0.le (mul_nonneg hC h02.le)) hC
        have hur : 0 ≤ 2 * (G.upper + G.rate) := mul_nonneg h02.le (add_pos hu hr).le
        have hK10 : 0 ≤ K1 := hK1 ▸ add_nonneg hC (mul_nonneg hur hC)
        have hM0 : 0 ≤ E * K0 * Z := mul_nonneg (mul_nonneg hE0.le hK00) hZ0.le
        have hM1 : 0 ≤ E * K1 * Z := mul_nonneg (mul_nonneg hE0.le hK10) hZ0.le
        have hJb : ∀ i c, G.Admissible c → ∀ (t : ℝ≥0) ω, (t : ℝ) ≤ G.h →
            |J i c (t, ω)| ≤ (E * K0 * Z) * (G.upper / G.rate * 2) ^ N ω := by
          intro i c hc t ω ht
          refine hmul t ω _ _ ht hK00 ?_
          have h1 := hVb t (Function.update (Y t ω) i (Y t ω i + 1))
          rw [hup, pow_succ] at h1
          have h2 := hVb t (Y t ω)
          have h3 : |c t ω / G.rate| ≤ G.upper / G.rate := by
            rw [abs_div, abs_of_pos hr]
            exact div_le_div_of_nonneg_right (hab1 c hc t ω) hr.le
          calc |c t ω / G.rate * V t (Function.update (Y t ω) i (Y t ω i + 1)) - V t (Y t ω)|
              ≤ |c t ω / G.rate * V t (Function.update (Y t ω) i (Y t ω i + 1))| + |V t (Y t ω)| := abs_sub _ _
            _ ≤ G.upper / G.rate * (C * (2 ^ (Y t ω 0 + Y t ω 1) * 2)) + C * 2 ^ (Y t ω 0 + Y t ω 1) := by
                rw [abs_mul]
                exact add_le_add (mul_le_mul h3 h1 (abs_nonneg _) hq0.le) h2
            _ = _ := by
                rw [hK0]
                generalize (2:ℝ) ^ (Y t ω 0 + Y t ω 1) = P0
                generalize G.upper / G.rate = q
                ring
        have hHcb : ∀ (t : ℝ≥0) ω, (t : ℝ) ≤ G.h →
            |Hc (t, ω)| ≤ (E * K1 * Z) * (G.upper / G.rate * 2) ^ N ω := by
          intro t ω ht
          refine hmul t ω _ _ ht hK10 ?_
          have h1 := hwb t (Y t ω)
          have h2 := hVb t (Y t ω)
          have h3 : |(a t ω - G.rate) + (b t ω - G.rate)| ≤ 2 * (G.upper + G.rate) := by
            have e1 : ∀ c : Process, G.Admissible c → |c t ω - G.rate| ≤ G.upper + G.rate := fun c hc =>
              (abs_sub _ _).trans (add_le_add (hab1 c hc t ω) (abs_of_pos hr).le)
            rw [two_mul]
            exact (abs_add_le _ _).trans (add_le_add (e1 a ha) (e1 b hb))
          calc |w t (Y t ω) - ((a t ω - G.rate) + (b t ω - G.rate)) * V t (Y t ω)|
              ≤ |w t (Y t ω)| + |((a t ω - G.rate) + (b t ω - G.rate)) * V t (Y t ω)| := abs_sub _ _
            _ ≤ C * 2 ^ (Y t ω 0 + Y t ω 1) + 2 * (G.upper + G.rate) * (C * 2 ^ (Y t ω 0 + Y t ω 1)) := by
                rw [abs_mul]
                exact add_le_add h1 (mul_le_mul h3 h2 (abs_nonneg _) hur)
            _ = _ := by rw [hK1, add_mul, mul_assoc _ C]
        obtain ⟨k0, i0⟩ := key _ (hJm 0 a ha) _ hM0 (hJb 0 a ha)
        obtain ⟨k1, i1⟩ := key _ (hJm 1 b hb) _ hM0 (hJb 1 b hb)
        obtain ⟨kc, ic⟩ := key _ hHcm _ hM1 hHcb
        obtain ⟨p0, r0, e0⟩ := COMPREAL G hG 0 _ (hJm 0 a ha) k0
        obtain ⟨p1, r1, e1⟩ := COMPREAL G hG 1 _ (hJm 1 b hb) k1
        obtain ⟨-, rc, -⟩ := COMPREAL G hG 0 _ hHcm kc
        have hV1 := VERIF1 Lp hLp G hG a b ha hb x V w C hVc hwm hVb hwb hVw Y hY
        have step1 : ∫ ω, Real.exp (G.logLikelihood a b ω) * V G.h (fun j => x j + X (Real.toNNReal G.h) ω j) ∂G.P
            = ∫ ω, (V 0 x + (∑ᶠ t ∈ jumps G.h ω 0, J 0 a (Real.toNNReal t, ω))
              + (∑ᶠ t ∈ jumps G.h ω 1, J 1 b (Real.toNNReal t, ω))
              + ∫ t in Icc (0:ℝ) G.h, Hc (Real.toNNReal t, ω)) ∂G.P := by
          refine integral_congr_ae ?_
          filter_upwards [hV1] with ω hω
          rw [hω]
          have hjt : ∀ i, ∀ t ∈ jumps G.h ω i, ((Real.toNNReal t : ℝ≥0) : ℝ) = t :=
            fun i t ht => Real.coe_toNNReal _ ht.1.le
          refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg (V 0 x + ·) ?_) ?_) ?_
          · refine finsum_mem_congr rfl fun t ht => ?_
            simp only [J, hjt 0 t ht]
          · refine finsum_mem_congr rfl fun t ht => ?_
            simp only [J, hjt 1 t ht]
          · refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
            simp only [Hc, Real.coe_toNNReal t ht.1]
        have q0 : Integrable (fun ω => V 0 x + (∑ᶠ t ∈ jumps G.h ω 0, J 0 a (Real.toNNReal t, ω))) G.P :=
          Integrable.add (f := fun _ => V 0 x) (integrable_const (V 0 x)) p0
        have q1 : Integrable (fun ω => V 0 x + (∑ᶠ t ∈ jumps G.h ω 0, J 0 a (Real.toNNReal t, ω))
              + (∑ᶠ t ∈ jumps G.h ω 1, J 1 b (Real.toNNReal t, ω))) G.P := q0.add p1
        rw [step1, integral_add q1 rc, integral_add q0 p1, integral_add (integrable_const (V 0 x)) p0, e0, e1,
          integral_const, ← integral_const_mul, ← integral_const_mul]
        have alg : ∀ L a' b' r v0 v1 v w : ℝ, L * (r * a' * (v0 - v) + r * b' * (v1 - v) + w) =
            r * (L * (a' * v0 - v)) + r * (L * (b' * v1 - v)) + L * (w - ((r * a' - r) + (r * b' - r)) * v) := by
          intros; ring
        have step2 : ∀ ω, (∫ t in Icc (0:ℝ) G.h, Lp G a b (Real.toNNReal t) ω *
              (a (Real.toNNReal t) ω * D 0 V t (Y (Real.toNNReal t) ω)
                + b (Real.toNNReal t) ω * D 1 V t (Y (Real.toNNReal t) ω)
                + w t (Y (Real.toNNReal t) ω))) =
            G.rate * (∫ t in Icc (0:ℝ) G.h, J 0 a (Real.toNNReal t, ω))
            + G.rate * (∫ t in Icc (0:ℝ) G.h, J 1 b (Real.toNNReal t, ω))
            + ∫ t in Icc (0:ℝ) G.h, Hc (Real.toNNReal t, ω) := by
          intro ω
          rw [← integral_const_mul, ← integral_const_mul]
          have j0 := (i0 ω).const_mul G.rate
          have j1 := (i1 ω).const_mul G.rate
          have j01 : Integrable (fun t : ℝ => G.rate * J 0 a (Real.toNNReal t, ω)
            + G.rate * J 1 b (Real.toNNReal t, ω)) (volume.restrict (Icc 0 G.h)) := j0.add j1
          rw [← integral_add j0 j1, ← integral_add j01 (ic ω)]
          refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
          have e1 := mul_div_cancel₀ (a (Real.toNNReal t) ω) hr.ne'
          have e2 := mul_div_cancel₀ (b (Real.toNNReal t) ω) hr.ne'
          simp only [J, Hc, Real.coe_toNNReal t ht.1, D]
          generalize a (Real.toNNReal t) ω / G.rate = a' at e1 ⊢
          generalize b (Real.toNNReal t) ω / G.rate = b' at e2 ⊢
          rw [← e1, ← e2]
          exact alg _ _ _ _ _ _ _ _
        simp_rw [step2]
        have s0 := r0.const_mul G.rate
        have s1 := r1.const_mul G.rate
        have s01 : Integrable (fun ω => G.rate * (∫ t in Icc (0:ℝ) G.h, J 0 a (Real.toNNReal t, ω))
            + G.rate * (∫ t in Icc (0:ℝ) G.h, J 1 b (Real.toNNReal t, ω))) G.P := s0.add s1
        rw [integral_add s01 rc, integral_add s0 s1]
        simp only [probReal_univ, one_smul]
        ring
      clear ODE1 PATHS REAL PATHSUM INDEP COMP COMPREAL NOCOMMON LEFT PREX VERIF1
      obtain ⟨Lp, hLp⟩ : ∃ Lp : Game → Process → Process → Process,
        (∀ G a b (t : ℝ≥0) ω, Lp G a b t ω = Real.exp (
          (∑ᶠ s ∈ jumps G.h ω 0 ∩ Iio (t : ℝ), Real.log (a (Real.toNNReal s) ω / G.rate)) +
          (∑ᶠ s ∈ jumps G.h ω 1 ∩ Iio (t : ℝ), Real.log (b (Real.toNNReal s) ω / G.rate)) -
          ∫ s in Icc (0 : ℝ) t, ((a (Real.toNNReal s) ω - G.rate) + (b (Real.toNNReal s) ω - G.rate)))) :=
        ⟨fun G a b t ω => _, fun _ _ _ _ _ => rfl⟩
      have hLp0 : ∀ a b t ω, 0 ≤ Lp G a b t ω := fun a b t ω => by rw [hLp]; positivity
      obtain ⟨hh, hl, hlu, hr, hru, hP⟩ := id hG
      have : IsProbabilityMeasure G.P := hP.1
      have hu0 : 0 < G.upper := hl.trans_le hlu
      have hmeasL := PREDL Lp hLp G hG
      have hexpm : ∀ a b, G.Admissible a → G.Admissible b →
          Measurable (fun ω => Real.exp (G.logLikelihood a b ω)) := fun a b ha hb =>
        Real.measurable_exp.comp (hmeasL a b ha hb).2
      have hXm : ∀ t : ℝ≥0, Measurable (X t) := fun t =>
        Measurable.mono (comap_measurable _) (le_iSup (fun r : ℝ≥0 => MeasurableSpace.comap (X r) inferInstance) t) le_rfl
      have hfm : ∀ (g : State → ℝ) (x : State),
          Measurable (fun ω => g (fun j => x j + X (Real.toNNReal G.h) ω j)) := fun g x =>
        (measurable_of_countable (fun y : State => g (fun j => x j + y j))).comp (hXm (Real.toNNReal G.h))
      have hint : ∀ a b, G.Admissible a → G.Admissible b → ∀ (g : State → ℝ) (C : ℝ),
          (∀ y, |g y| ≤ C * 2 ^ (y 0 + y 1)) → ∀ x : State,
          Integrable (fun ω => Real.exp (G.logLikelihood a b ω) *
            g (fun j => x j + X (Real.toNNReal G.h) ω j)) G.P := by
        intro a b ha hb g C hg x
        have hm := (MOM G hG (G.upper / G.rate * 2) (by positivity)).const_mul
          (Real.exp (2 * G.rate * G.h) * (C * 2 ^ (x 0 + x 1)))
        refine hm.mono' (((hexpm a b ha hb).mul (hfm g x)).aestronglyMeasurable) ?_
        filter_upwards with ω
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have h1 := (LBOUND Lp hLp G hG a b ha hb ω).1
        have h2 := hg (fun j => x j + X (Real.toNNReal G.h) ω j)
        calc _ ≤ _ := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ = _ := by rw [mul_pow]; ring
      have hterm : ∀ i : Fin 2, ∀ y : State, |terminalCost i y| ≤ 8 * 2 ^ (y 0 + y 1) := by
        have hp : ∀ n : ℕ, (n:ℝ) ^ 2 + 4 * n + 6 ≤ 8 * 2 ^ n := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
            rw [pow_succ (2:ℝ) n]
            push_cast
            have : (0:ℝ) ≤ n := Nat.cast_nonneg n
            have e : ((n:ℝ) + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
            rw [e]
            have e2 : (0:ℝ) ≤ (n:ℝ) ^ 2 := sq_nonneg _
            linarith
        intro i y
        have h1 := hp (y 0 + y 1)
        push_cast at h1
        have h2 : (0:ℝ) ≤ y 0 := Nat.cast_nonneg _
        have h3 : (0:ℝ) ≤ y 1 := Nat.cast_nonneg _
        refine le_trans ?_ h1
        unfold terminalCost
        have a1 := mul_nonneg h2 h3
        have a2 := mul_nonneg h2 h2
        have a3 := mul_nonneg h3 h3
        have e0 : ((y 0 : ℝ) + y 1) ^ 2 = (y 0 : ℝ) * y 0 + 2 * ((y 0 : ℝ) * y 1) + (y 1 : ℝ) * y 1 := by ring
        rw [e0]
        split_ifs
        · rw [mul_sub, abs_le]
          constructor <;> linarith
        · rw [mul_sub, mul_comm (y 1 : ℝ) (y 0), abs_le]
          constructor <;> linarith
      have hone : ∀ a b, G.Admissible a → G.Admissible b →
          ∫ ω, Real.exp (G.logLikelihood a b ω) ∂G.P = 1 := by
        intro a b ha hb
        have := VERIF2 Lp hLp G hG a b ha hb 0 (fun _ _ => 1) (fun _ _ => 0) 1
          (fun _ => continuous_const) (fun _ => measurable_const)
          (fun t y => by simpa using one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
          (fun t y => by simp) (fun y s t _ _ _ => by simp) _ (fun t ω => rfl)
        simpa [D] using this
      have hexpi : ∀ a b, G.Admissible a → G.Admissible b →
          Integrable (fun ω => Real.exp (G.logLikelihood a b ω)) G.P := by
        intro a b ha hb
        simpa using hint a b ha hb (fun _ => 1) 1
          (fun y => by simpa using one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) 0
      have hdm : ∀ a b, G.Admissible a → G.Admissible b →
          Measurable (fun ω => ENNReal.ofReal (Real.exp (G.logLikelihood a b ω))) := fun a b ha hb =>
        (hexpm a b ha hb).ennreal_ofReal
      have hWD : G.WellDefined := by
        intro a b ha hb
        refine ⟨⟨?_⟩, fun i x => ?_⟩
        · rw [Game.law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
            ← ofReal_integral_eq_lintegral_ofReal (hexpi a b ha hb)
              (Eventually.of_forall fun ω => (Real.exp_pos _).le), hone a b ha hb, ENNReal.ofReal_one]
        · rw [Game.law, integrable_withDensity_iff_integrable_smul' (hdm a b ha hb)
            (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
          refine (hint a b ha hb (terminalCost i) 8 (hterm i) x).congr ?_
          filter_upwards with ω
          rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
          rfl
      refine ⟨hWD, ?_⟩
      obtain ⟨V, f, C, hC, hVc, hfmeas, hfI, hVb, hVh, hVI, hopt⟩ := ODE2 G.h G.lower G.upper hh hl hlu
      have hF : ∀ i, G.Feedback (f i) := fun i => FEED G hG (f i) (hfmeas i) (hfI i)
      have hDb : ∀ i j s x, |D j (V i) s x| ≤ 3 * C * 2 ^ (x 0 + x 1) := by
        intro i j s x
        have h1 := hVb i s (Function.update x j (x j + 1))
        have h2 := hVb i s x
        have h3 : (Function.update x j (x j + 1)) 0 + (Function.update x j (x j + 1)) 1 = x 0 + x 1 + 1 := by
          fin_cases j <;> simp [Function.update] <;> omega
        rw [h3, pow_succ] at h1
        unfold D
        have := abs_sub (V i s (Function.update x j (x j + 1))) (V i s x)
        linarith
      have hcost : ∀ i x a b, G.Admissible a → G.Admissible b → G.cost i x a b =
          V i 0 x + ∫ ω, (∫ t in Icc (0:ℝ) G.h, Lp G a b (Real.toNNReal t) ω *
            ((a (Real.toNNReal t) ω - f 0 t (fun j => x j + preX (Real.toNNReal t) ω j)) *
                D 0 (V i) t (fun j => x j + preX (Real.toNNReal t) ω j)
              + (b (Real.toNNReal t) ω - f 1 t (fun j => x j + preX (Real.toNNReal t) ω j)) *
                D 1 (V i) t (fun j => x j + preX (Real.toNNReal t) ω j))) ∂G.P := by
        intro i x a b ha hb
        have hv := VERIF2 Lp hLp G hG a b ha hb x (V i)
          (fun s y => -(f 0 s y * D 0 (V i) s y + f 1 s y * D 1 (V i) s y)) (C + 6 * G.upper * C)
          (hVc i) (fun y => by
            have hD : ∀ j, Measurable (fun s => D j (V i) s y) := fun j =>
              ((hVc i _).sub (hVc i _)).measurable
            exact (((hfmeas 0 y).mul (hD 0)).add ((hfmeas 1 y).mul (hD 1))).neg)
          (fun t y => (hVb i t y).trans (by
            have : 0 ≤ 6 * G.upper * C := by have := hl.le.trans hlu; positivity
            gcongr; linarith))
          (fun t y => by
            have hu := hl.le.trans hlu
            have h0 : ∀ j : Fin 2, |f j t y * D j (V i) t y| ≤ G.upper * (3 * C * 2 ^ (y 0 + y 1)) := by
              intro j
              rw [abs_mul]
              have hf1 := hfI j t y
              refine mul_le_mul ?_ (hDb i j t y) (abs_nonneg _) hu
              rw [abs_of_pos (hl.trans_le hf1.1)]
              exact hf1.2
            rw [abs_neg]
            refine (abs_add_le _ _).trans ?_
            have h1 := h0 0
            have h2 := h0 1
            have h3 : 0 ≤ C * 2 ^ (y 0 + y 1) := by positivity
            have e : (C + 6 * G.upper * C) * 2 ^ (y 0 + y 1) = C * 2 ^ (y 0 + y 1) +
              2 * (G.upper * (3 * C * 2 ^ (y 0 + y 1))) := by ring
            rw [e]
            linarith)
          (hVI i) (fun t ω => fun j => x j + preX t ω j) (fun t ω => rfl)
        have hc : G.cost i x a b = ∫ ω, Real.exp (G.logLikelihood a b ω) *
            V i G.h (fun j => x j + X (Real.toNNReal G.h) ω j) ∂G.P := by
          unfold Game.cost Game.law
          rw [integral_withDensity_eq_integral_toReal_smul (hdm a b ha hb)
            (Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)]
          refine integral_congr_ae ?_
          filter_upwards with ω
          rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, hVh]
          rfl
        rw [hc, hv]
        congr 1
        refine integral_congr_ae ?_
        filter_upwards with ω
        refine integral_congr_ae ?_
        filter_upwards with t
        ring
      have hlift : ∀ i x ω, ∀ t ∈ Icc (0:ℝ) G.h, G.liftFeedback (f i) x (Real.toNNReal t) ω =
          f i t (fun j => x j + preX (Real.toNNReal t) ω j) := by
        intro i x ω t ht
        unfold Game.liftFeedback
        rw [Real.coe_toNNReal t ht.1, if_pos ht.2]
      have heq : ∀ i x, G.cost i x (G.liftFeedback (f 0) x) (G.liftFeedback (f 1) x) = V i 0 x := by
        intro i x
        rw [hcost i x _ _ ((hF 0).2.2 x) ((hF 1).2.2 x)]
        have : ∀ ω, (∫ t in Icc (0:ℝ) G.h, Lp G (G.liftFeedback (f 0) x) (G.liftFeedback (f 1) x) (Real.toNNReal t) ω *
            ((G.liftFeedback (f 0) x (Real.toNNReal t) ω - f 0 t (fun j => x j + preX (Real.toNNReal t) ω j)) *
                D 0 (V i) t (fun j => x j + preX (Real.toNNReal t) ω j)
              + (G.liftFeedback (f 1) x (Real.toNNReal t) ω - f 1 t (fun j => x j + preX (Real.toNNReal t) ω j)) *
                D 1 (V i) t (fun j => x j + preX (Real.toNNReal t) ω j))) = 0 := by
          intro ω
          rw [setIntegral_congr_fun (g := fun _ => (0:ℝ)) measurableSet_Icc]
          · simp
          · intro t ht
            simp only [hlift _ x ω t ht]
            ring
        simp [this]
      refine ⟨f 0, f 1, hF 0, hF 1, fun x => ⟨⟨⟨_, (hF 0).2.2 x, rfl⟩, ?_⟩, ⟨⟨_, (hF 1).2.2 x, rfl⟩, ?_⟩⟩⟩
      · rintro c ⟨a, ha, rfl⟩
        rw [heq 0 x, hcost 0 x _ _ ha ((hF 1).2.2 x)]
        refine le_add_of_nonneg_right (integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun t ht => ?_)
        refine mul_nonneg (hLp0 _ _ _ _) ?_
        have h1 := hopt 0 t (fun j => x j + preX (Real.toNNReal t) ω j) _ (ha.2 (Real.toNNReal t) ω).1 (ha.2 (Real.toNNReal t) ω).2
        simp only [hlift _ x ω t ht]
        linarith
      · rintro c ⟨a, ha, rfl⟩
        rw [heq 1 x, hcost 1 x _ _ ((hF 0).2.2 x) ha]
        refine le_add_of_nonneg_right (integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun t ht => ?_)
        refine mul_nonneg (hLp0 _ _ _ _) ?_
        have h1 := hopt 1 t (fun j => x j + preX (Real.toNNReal t) ω j) _ (ha.2 (Real.toNNReal t) ω).1 (ha.2 (Real.toNNReal t) ω).2
        simp only [hlift _ x ω t ht]
        linarith
