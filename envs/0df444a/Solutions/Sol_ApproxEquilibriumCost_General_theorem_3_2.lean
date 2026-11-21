-- Prove2me | solution 1 for ApproxEquilibriumCost.General.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:35.400043+00:00
-- url     : https://prove2.me/submissions/0f8ae605-f6c5-4b8f-9186-021be6a9965a

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_PolynomialLatencies
import Definitions.Def_ApproxEquilibriumCost_General_Parameters
import Theorems.Thm_ApproxEquilibriumCost_General_lemma_2_2
import Theorems.Thm_ApproxEquilibriumCost_General_lemma_3_6
import Theorems.Thm_ApproxEquilibriumCost_General_rho_spec

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.T32
open ApproxEquilibriumCost.General

theorem mu_zero (d : ℕ) : mu d 0 = 0 := by simp [mu]

theorem mu_le_self (d : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : mu d t ≤ t := by
  unfold mu
  have : 0 ≤ Real.rpow (1 - t) (1 / (d : ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith

theorem poly_lower (d : ℕ) (a : Fin (d + 1) → ℝ) (ha : ∀ j, 0 ≤ a j) (X X' : ℝ)
    (hX' : 0 ≤ X') (hXX : X' ≤ X) (hX : 0 < X) :
    (X' / X) ^ d * (∑ j, a j * X ^ (j : ℕ)) ≤ ∑ j, a j * X' ^ (j : ℕ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  set t := X' / X with ht
  have ht0 : 0 ≤ t := div_nonneg hX' hX.le
  have ht1 : t ≤ 1 := (div_le_one hX).2 hXX
  have hXt : X' = t * X := by rw [ht]; field_simp
  have hjd : t ^ d ≤ t ^ (j : ℕ) :=
    pow_le_pow_of_le_one ht0 ht1 (Nat.lt_succ_iff.1 j.2)
  have hnn : 0 ≤ a j * X ^ (j : ℕ) := mul_nonneg (ha j) (by positivity)
  calc t ^ d * (a j * X ^ (j : ℕ)) = a j * X ^ (j : ℕ) * t ^ d := by ring
    _ ≤ a j * X ^ (j : ℕ) * t ^ (j : ℕ) := mul_le_mul_of_nonneg_left hjd hnn
    _ = a j * (t * X) ^ (j : ℕ) := by rw [mul_pow]; ring
    _ = a j * X' ^ (j : ℕ) := by rw [hXt]

theorem mu_bound (d : ℕ) (hd : 1 ≤ d) (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (h : a ^ d ≤ 1 - q) : mu d q ≤ q * (1 - a) := by
  unfold mu
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have h1 : a ≤ Real.rpow (1 - q) (1 / (d : ℝ)) := by
    have := Real.rpow_le_rpow (by positivity) h (by positivity : (0 : ℝ) ≤ 1 / (d : ℝ))
    rw [one_div, Real.pow_rpow_inv_natCast ha (by omega)] at this
    simpa [one_div] using this
  exact mul_le_mul_of_nonneg_left (by linarith) hq

theorem elem (d : ℕ) (hd : 1 ≤ d) (X X' L L' C : ℝ) (hC : 0 < C) (hX' : 0 ≤ X') (hXX : X' < X)
    (hL : 0 < L) (hL' : 0 ≤ L') (hLL : L' ≤ L) (hpow : (X' / X) ^ d * L ≤ L') :
    (X * L / C) * mu d (1 - L' / L) ≤ (X - X') * (L - L') / C := by
  have hX : 0 < X := by linarith
  have hq0 : 0 ≤ 1 - L' / L := by
    have : L' / L ≤ 1 := (div_le_one hL).2 hLL
    linarith
  have hb := mu_bound d hd (X' / X) (1 - L' / L) (div_nonneg hX' hX.le) hq0 (by
    have : (X' / X) ^ d ≤ L' / L := by rw [le_div_iff₀ hL]; exact hpow
    linarith)
  have hw : 0 ≤ X * L / C := by positivity
  calc (X * L / C) * mu d (1 - L' / L) ≤ (X * L / C) * ((1 - L' / L) * (1 - X' / X)) :=
        mul_le_mul_of_nonneg_left hb hw
    _ = (X - X') * (L - L') / C := by field_simp

theorem key_ineq (d : ℕ) (hd : 1 ≤ d) {n : ℕ} (x y : Fin n → ℝ) (Lf : Fin n → ℝ → ℝ)
    (hx : ∀ e, 0 ≤ x e) (hy : ∀ e, 0 ≤ y e) (hL0 : ∀ e t, 0 ≤ t → 0 ≤ Lf e t)
    (hLm : ∀ e, MonotoneOn (Lf e) (Set.Ici 0))
    (hpoly : ∀ e, ∃ a : Fin (d + 1) → ℝ, (∀ j, 0 ≤ a j) ∧
      ∀ t, 0 ≤ t → Lf e t = ∑ j, a j * t ^ (j : ℕ))
    (C : ℝ) (hC : 0 < C) (hCdef : C = ∑ e, x e * Lf e (x e))
    (hT0 : 0 ≤ C - ∑ e, x e * Lf e (y e)) (hcr : 0 ≤ ∑ e, x e * Lf e (y e)) :
    mu d ((C - ∑ e, x e * Lf e (y e)) / C) ≤
      (∑ e, (y e - x e) * (Lf e (y e) - Lf e (x e))) / C := by
  obtain ⟨_, hsm, hconv, _⟩ := lemma_3_6 d hd
  have hmono : ∀ (e : Fin n), x e ≤ y e → Lf e (x e) ≤ Lf e (y e) :=
    fun e h => hLm e (hx e) (hy e) h
  have hD0 : ∀ e, 0 ≤ (y e - x e) * (Lf e (y e) - Lf e (x e)) := by
    intro e
    rcases le_total (x e) (y e) with h | h
    · exact mul_nonneg (by linarith) (by linarith [hmono e h])
    · have h2 : Lf e (y e) ≤ Lf e (x e) := hLm e (hy e) (hx e) h
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  set w : Fin n → ℝ := fun e => x e * Lf e (x e) / C with hwdef
  set q : Fin n → ℝ := fun e =>
    if (y e < x e ∧ 0 < Lf e (x e)) then 1 - Lf e (y e) / Lf e (x e) else 0 with hqdef
  have hw0 : ∀ e, 0 ≤ w e := fun e =>
    div_nonneg (mul_nonneg (hx e) (hL0 e _ (hx e))) hC.le
  have hw1 : ∑ e, w e = 1 := by
    simp only [hwdef]; rw [← Finset.sum_div, ← hCdef]; exact div_self hC.ne'
  have hqI : ∀ e, q e ∈ Set.Icc (0 : ℝ) 1 := by
    intro e
    simp only [hqdef]
    split_ifs with h
    · have hle : Lf e (y e) ≤ Lf e (x e) := hLm e (hy e) (hx e) h.1.le
      have h1 : Lf e (y e) / Lf e (x e) ≤ 1 := (div_le_one h.2).2 hle
      have h2 : 0 ≤ Lf e (y e) / Lf e (x e) := div_nonneg (hL0 e _ (hy e)) h.2.le
      exact ⟨by linarith, by linarith⟩
    · exact ⟨le_refl _, zero_le_one⟩
  have hper1 : ∀ e, x e * (Lf e (x e) - Lf e (y e)) ≤ C * (w e * q e) := by
    intro e
    by_cases h : y e < x e ∧ 0 < Lf e (x e)
    · have : C * (w e * q e) = x e * (Lf e (x e) - Lf e (y e)) := by
        have := h.2.ne'
        simp only [hwdef, hqdef, if_pos h]
        field_simp
      rw [this]
    · have hq : q e = 0 := by simp only [hqdef]; rw [if_neg h]
      rw [hq, mul_zero, mul_zero]
      by_cases hyx : y e < x e
      · have hL : Lf e (x e) = 0 := by
          have : ¬ (0 < Lf e (x e)) := fun h2 => h ⟨hyx, h2⟩
          exact le_antisymm (not_lt.1 this) (hL0 e _ (hx e))
        apply mul_nonpos_of_nonneg_of_nonpos (hx e)
        rw [hL]; linarith [hL0 e _ (hy e)]
      · exact mul_nonpos_of_nonneg_of_nonpos (hx e)
          (by linarith [hmono e (not_lt.1 hyx)])
  have hper2 : ∀ e, w e * mu d (q e) ≤
      (y e - x e) * (Lf e (y e) - Lf e (x e)) / C := by
    intro e
    by_cases h : y e < x e ∧ 0 < Lf e (x e)
    · have hq : q e = 1 - Lf e (y e) / Lf e (x e) := by simp only [hqdef]; rw [if_pos h]
      rw [hq]
      obtain ⟨a, ha0, hal⟩ := hpoly e
      have hpow : (y e / x e) ^ d * Lf e (x e) ≤ Lf e (y e) := by
        rw [hal _ (hx e), hal _ (hy e)]
        exact poly_lower d a ha0 (x e) (y e) (hy e) h.1.le (by linarith [h.1, hy e])
      have := elem d hd (x e) (y e) (Lf e (x e)) (Lf e (y e)) C hC (hy e) h.1 h.2
        (hL0 e _ (hy e)) (hLm e (hy e) (hx e) h.1.le) hpow
      have e2 : (y e - x e) * (Lf e (y e) - Lf e (x e)) =
          (x e - y e) * (Lf e (x e) - Lf e (y e)) := by ring
      rw [e2]
      exact this
    · have hq : q e = 0 := by simp only [hqdef]; rw [if_neg h]
      rw [hq, mu_zero, mul_zero]
      exact div_nonneg (hD0 e) hC.le
  have hsum : (C - ∑ e, x e * Lf e (y e)) / C ≤ ∑ e, w e * q e := by
    rw [div_le_iff₀ hC]
    have e1 : C - ∑ e, x e * Lf e (y e) = ∑ e, x e * (Lf e (x e) - Lf e (y e)) := by
      conv_lhs => rw [hCdef]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro e _; ring
    rw [e1, mul_comm, Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _ => by linarith [hper1 e])
  have hT1 : (C - ∑ e, x e * Lf e (y e)) / C ≤ 1 := by
    rw [div_le_one hC]; linarith
  have hT0' : 0 ≤ (C - ∑ e, x e * Lf e (y e)) / C := div_nonneg hT0 hC.le
  have hS1 : ∑ e, w e * q e ≤ 1 := by
    calc ∑ e, w e * q e ≤ ∑ e, w e * 1 :=
          Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (hqI e).2 (hw0 e))
      _ = 1 := by simp [hw1]
  have hS0 : 0 ≤ ∑ e, w e * q e :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hw0 e) (hqI e).1)
  calc mu d ((C - ∑ e, x e * Lf e (y e)) / C) ≤ mu d (∑ e, w e * q e) :=
        hsm.monotoneOn ⟨hT0', hT1⟩ ⟨hS0, hS1⟩ hsum
    _ = mu d (∑ e, w e • q e) := by simp only [smul_eq_mul]
    _ ≤ ∑ e, w e • mu d (q e) :=
        hconv.map_sum_le (fun e _ => hw0 e) hw1 (fun e _ => hqI e)
    _ = ∑ e, w e * mu d (q e) := by simp only [smul_eq_mul]
    _ ≤ ∑ e, (y e - x e) * (Lf e (y e) - Lf e (x e)) / C :=
        Finset.sum_le_sum (fun e _ => hper2 e)
    _ = _ := by rw [Finset.sum_div]

end ApproxEquilibriumCost.Dev.T32

namespace ApproxEquilibriumCost.Dev.T32
open ApproxEquilibriumCost.General

theorem load_nonneg {n k : ℕ} (G : Game n k) (g : Flow G) (hg : ∀ r, 0 ≤ g r) (e : Fin n) :
    0 ≤ load G g e := by
  unfold load KellyStochasticNetworks.linkFlow
  apply Finset.sum_nonneg
  intro r _
  apply mul_nonneg _ (hg r)
  unfold incidence
  split_ifs <;> norm_num

end ApproxEquilibriumCost.Dev.T32

namespace ApproxEquilibriumCost.General

theorem chk_theorem_3_2 {n k : ℕ} (G : Game n k) (d : ℕ) (hd : 1 ≤ d)
    (hpoly : HasPolynomialLatencies G d) (f f' : Flow G)
    (hf : IsNash G f) (hcost : 0 < cost G f)
    (ε : ℝ) (hε : 0 ≤ ε) (hf' : IsApproxNash G ε f')
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hgap : (cost G f - crossCost G f' f) / cost G f ≤ τ) :
    let θ := min τ (min (rho d ε) (criticalPoint d))
    1 - θ + mu d θ ≤ cost G f' / cost G f := by
  intro θ
  obtain ⟨_, hsm, hconv, _, hanti, _, hcrit, hmin, _⟩ := lemma_3_6 d hd
  obtain ⟨hr1, hr2, _⟩ := rho_spec d hd ε hε
  obtain ⟨p1, _, p3⟩ := lemma_2_2 G f f' hf.1 hf'.1 ε hε
  have p1 := p1 hf
  have p3 := p3 hf hf'
  have hx : ∀ e, 0 ≤ load G f e := Dev.T32.load_nonneg G f hf.1.1
  have hy : ∀ e, 0 ≤ load G f' e := Dev.T32.load_nonneg G f' hf'.1.1
  have hcr : 0 ≤ crossCost G f' f :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hx e) (G.latency_nonnegative e _ (hy e)))
  have hD0 : ∀ e, 0 ≤ (load G f' e - load G f e) *
      (G.latency e (load G f' e) - G.latency e (load G f e)) := by
    intro e
    rcases le_total (load G f e) (load G f' e) with h | h
    · exact mul_nonneg (by linarith)
        (by linarith [G.latency_monotone e (hx e) (hy e) h])
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
        (by linarith [G.latency_monotone e (hy e) (hx e) h])
  have hDeq : (∑ e, (load G f' e - load G f e) *
        (G.latency e (load G f' e) - G.latency e (load G f e))) =
      (cost G f' - crossCost G f' f) + (cost G f - crossCost G f f') := by
    unfold cost crossCost
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro e _; ring
  have hDnn := Finset.sum_nonneg (fun e (_ : e ∈ Finset.univ) => hD0 e)
  set C := cost G f with hC
  set cr := crossCost G f' f with hcrdef
  set D := (∑ e, (load G f' e - load G f e) *
        (G.latency e (load G f' e) - G.latency e (load G f e))) with hDdef
  have hR : D ≤ cost G f' - cr := by rw [hDeq]; linarith
  have hθ0 : 0 ≤ θ := le_min hτ (le_min hr1.1 hcrit.1)
  have hθc : θ ≤ criticalPoint d := le_trans (min_le_right _ _) (min_le_right _ _)
  have hθ1 : θ ≤ 1 := hθc.trans hcrit.2
  have hθm : mu d θ ≤ θ := Dev.T32.mu_le_self d θ hθ0 hθ1
  by_cases hT : C - cr ≤ 0
  · rw [le_div_iff₀ hcost]
    have : C ≤ cost G f' := by linarith
    nlinarith
  · push Not at hT
    set s := (C - cr) / C with hs
    have hs0 : 0 < s := div_pos hT hcost
    have hs1 : s ≤ 1 := by
      rw [hs, div_le_one hcost]; linarith
    have hsC : s * C = C - cr := by rw [hs]; field_simp
    have key := Dev.T32.key_ineq d hd (fun e => load G f e) (fun e => load G f' e) G.latency
      hx hy G.latency_nonnegative G.latency_monotone
      (by
        obtain ⟨a, ha, hal⟩ := hpoly
        intro e
        exact ⟨a e, ha e, fun t ht => hal e t ht⟩)
      C hcost rfl (by show 0 ≤ C - cr; linarith) hcr
    have hmus : mu d s * C ≤ D := by
      have := (le_div_iff₀ hcost).1 key
      exact this
    have hmus2 : mu d s ≤ ε * (1 - s) := by
      have h1 : 1 - s = cr / C := by rw [hs]; field_simp; ring
      have h2 : mu d s * C ≤ ε * cr := by linarith
      rw [h1, ← mul_div_assoc, le_div_iff₀ hcost]
      exact h2
    have hsr : s ≤ rho d ε := by
      by_contra hlt
      push Not at hlt
      have := hsm ⟨hr1.1, hr1.2.le⟩ ⟨hs0.le, hs1⟩ hlt
      nlinarith
    have hst : s ≤ τ := hgap
    have hFs : 1 - s + mu d s ≤ cost G f' / C := by
      rw [le_div_iff₀ hcost]
      nlinarith
    refine le_trans ?_ hFs
    by_cases hsc : s ≤ criticalPoint d
    · have hsθ : s ≤ θ := le_min hst (le_min hsr hsc)
      have := hanti ⟨hs0.le, hsc⟩ ⟨hθ0, hθc⟩ hsθ
      simpa using this
    · push Not at hsc
      have h1 : min (rho d ε) (criticalPoint d) = criticalPoint d :=
        min_eq_right (hsc.le.trans hsr)
      have h2 : θ = criticalPoint d := by
        show min τ (min (rho d ε) (criticalPoint d)) = _
        rw [h1]; exact min_eq_right (hsc.le.trans hst)
      rw [h2]
      exact hmin s ⟨hs0.le, hs1⟩

end ApproxEquilibriumCost.General
end

theorem solution : type_of% @ApproxEquilibriumCost.General.chk_theorem_3_2 := @ApproxEquilibriumCost.General.chk_theorem_3_2
