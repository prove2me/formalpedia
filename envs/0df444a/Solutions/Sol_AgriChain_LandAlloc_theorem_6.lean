-- Prove2me | solution 1 for AgriChain.LandAlloc.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T08:55:05.550115+00:00
-- url     : https://prove2.me/submissions/bd3dab65-1ef7-4b06-9d5d-91c5797b922c

import Mathlib
import Definitions.Def_AgriChain_LandAlloc_Model

set_option autoImplicit false

namespace AgriLA6

open AgriChain.LandAlloc

/-- normalized winning price at total normalized harvest `T` -/
noncomputable def w (m po T : ℝ) : ℝ := m - (m - po) * min 1 (max (T - 1) 0)

noncomputable def p (m po t1 t2 : ℝ) : ℝ :=
  w m po (t1 + t2) * min t1 1 + po * min (max (t1 - 1) 0) (max (1 - t2) 0)

noncomputable def q (m po t1 t2 : ℝ) : ℝ :=
  w m po (t1 + t2) * min t2 (max (1 - t1) 0) + po * min (max (t2 - max (1 - t1) 0) 0) 1

lemma w_ge (m po T : ℝ) (hpo : po ≤ m) : po ≤ w m po T := by
  unfold w
  have h1 : min 1 (max (T - 1) 0) ≤ 1 := min_le_left _ _
  nlinarith

lemma w_le (m po T : ℝ) (hpo : po ≤ m) : w m po T ≤ m := by
  unfold w
  have h1 : 0 ≤ min 1 (max (T - 1) 0) := le_min (by norm_num) (le_max_right _ _)
  nlinarith

/-- the key identity: `min K Y * (m - W) = (m - po) * min K (max (Y - K) 0)` -/
lemma key_ab (m po K Y : ℝ) (hK : 0 < K) (hY : 0 ≤ Y) :
    min K Y * (m - w m po (Y / K)) = (m - po) * min K (max (Y - K) 0) := by
  unfold w
  rcases le_total Y K with h | h
  · have e1 : max (Y / K - 1) 0 = 0 := by
      apply max_eq_right
      have : Y / K ≤ 1 := (div_le_one hK).2 h
      linarith
    have e2 : max (Y - K) 0 = 0 := max_eq_right (by linarith)
    rw [e1, e2, min_eq_right (zero_le_one' ℝ), min_eq_right hK.le]; ring
  · rcases le_total Y (2 * K) with h' | h'
    · have e0 : min K Y = K := min_eq_left h
      have e1 : max (Y / K - 1) 0 = Y / K - 1 := by
        apply max_eq_left
        have : 1 ≤ Y / K := (one_le_div hK).2 h
        linarith
      have e1' : min 1 (Y / K - 1) = Y / K - 1 := by
        apply min_eq_right
        have : Y / K ≤ 2 := (div_le_iff₀ hK).2 (by linarith)
        linarith
      have e2 : max (Y - K) 0 = Y - K := max_eq_left (by linarith)
      have e2' : min K (Y - K) = Y - K := min_eq_right (by linarith)
      rw [e0, e1, e1', e2, e2']
      field_simp
      ring
    · have e0 : min K Y = K := min_eq_left h
      have e1 : max (Y / K - 1) 0 = Y / K - 1 := by
        apply max_eq_left
        have : 1 ≤ Y / K := (one_le_div hK).2 h
        linarith
      have e1' : min 1 (Y / K - 1) = 1 := by
        apply min_eq_left
        have : 2 ≤ Y / K := (le_div_iff₀ hK).2 (by linarith)
        linarith
      have e2 : max (Y - K) 0 = Y - K := max_eq_left (by linarith)
      have e2' : min K (Y - K) = K := min_eq_left (by linarith)
      rw [e0, e1, e1', e2, e2']
      ring

lemma key_zero (m po K Y : ℝ) (hK : 0 < K) (hY : 0 ≤ Y) (h0 : min K Y = 0) :
    w m po (Y / K) = m := by
  have hY0 : Y = 0 := by
    rcases min_choice K Y with h | h
    · rw [h] at h0; linarith
    · rw [h] at h0; exact h0
  subst hY0
  unfold w
  simp

lemma wtpSet1_mem (pe po c K y1 y2 x : ℝ) :
    x ∈ wtpSet1 (symChain pe po c K) y1 y2 ↔ po ≤ x ∧ x ≤ pe - c ∧ ∀ p2 : ℝ, po < p2 →
      0 ≤ (if po ≤ x then (pe - c - x) * min K (y1 + y2) else
            (pe - c - x) * min K (max (y1 + y2 - K) 0)) -
          (if p2 ≤ po then (pe - c - po) * min K (y1 + y2) else
            (pe - c - po) * min K (max (y1 + y2 - K) 0)) := Iff.rfl

lemma wtpSet2_mem (pe po c K y1 y2 x : ℝ) :
    x ∈ wtpSet2 (symChain pe po c K) y1 y2 ↔ po ≤ x ∧ x ≤ pe - c ∧ ∀ p1 : ℝ, po ≤ p1 →
      0 ≤ (if x ≤ po then (pe - c - x) * min K (max (y1 + y2 - K) 0) else
            (pe - c - x) * min K (y1 + y2)) -
          (if po ≤ p1 then (pe - c - po) * min K (max (y1 + y2 - K) 0) else
            (pe - c - po) * min K (y1 + y2)) := Iff.rfl

lemma wtpSet1_eq (pe po c K y1 y2 : ℝ) (hK : 0 < K) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) :
    wtpSet1 (symChain pe po c K) y1 y2 = Set.Icc po (w (pe - c) po ((y1 + y2) / K)) := by
  have hab := key_ab (pe - c) po K (y1 + y2) hK (by linarith)
  have hz := key_zero (pe - c) po K (y1 + y2) hK (by linarith)
  have hWge := w_ge (pe - c) po ((y1 + y2) / K) hpo
  have hWle := w_le (pe - c) po ((y1 + y2) / K) hpo
  have ha : 0 ≤ min K (y1 + y2) := le_min hK.le (by linarith)
  ext x
  rw [wtpSet1_mem, Set.mem_Icc]
  constructor
  · rintro ⟨hx1, hx2, hx3⟩
    refine ⟨hx1, ?_⟩
    have h3 := hx3 (po + 1) (by linarith)
    rw [if_pos hx1, if_neg (by linarith)] at h3
    rcases eq_or_lt_of_le ha with h | h
    · rw [hz h.symm]; exact hx2
    · by_contra hc
      push_neg at hc
      nlinarith
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, le_trans hx2 hWle, ?_⟩
    intro p2 hp2
    rw [if_pos hx1, if_neg (by linarith)]
    nlinarith

lemma wtpSet2_eq (pe po c K y1 y2 : ℝ) (hK : 0 < K) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) :
    wtpSet2 (symChain pe po c K) y1 y2 = Set.Icc po (w (pe - c) po ((y1 + y2) / K)) := by
  have hab := key_ab (pe - c) po K (y1 + y2) hK (by linarith)
  have hz := key_zero (pe - c) po K (y1 + y2) hK (by linarith)
  have hWge := w_ge (pe - c) po ((y1 + y2) / K) hpo
  have hWle := w_le (pe - c) po ((y1 + y2) / K) hpo
  have ha : 0 ≤ min K (y1 + y2) := le_min hK.le (by linarith)
  ext x
  rw [wtpSet2_mem, Set.mem_Icc]
  constructor
  · rintro ⟨hx1, hx2, hx3⟩
    refine ⟨hx1, ?_⟩
    have h3 := hx3 po le_rfl
    rw [if_pos le_rfl] at h3
    by_cases hxp : x ≤ po
    · linarith
    · rw [if_neg hxp] at h3
      rcases eq_or_lt_of_le ha with h | h
      · rw [hz h.symm]; exact hx2
      · by_contra hc
        push_neg at hc
        nlinarith
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, le_trans hx2 hWle, ?_⟩
    intro p1 hp1
    rw [if_pos hp1]
    by_cases hxp : x ≤ po
    · rw [if_pos hxp]
      have : x = po := le_antisymm hxp hx1
      subst this; simp
    · rw [if_neg hxp]
      nlinarith

lemma wtp1_eq (pe po c K y1 y2 : ℝ) (hK : 0 < K) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) :
    wtp1 (symChain pe po c K) y1 y2 = w (pe - c) po ((y1 + y2) / K) := by
  unfold wtp1
  rw [wtpSet1_eq pe po c K y1 y2 hK hpo h1 h2]
  exact csSup_Icc (w_ge _ _ _ hpo)

lemma wtp2_eq (pe po c K y1 y2 : ℝ) (hK : 0 < K) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ y1) (h2 : 0 ≤ y2) :
    wtp2 (symChain pe po c K) y1 y2 = w (pe - c) po ((y1 + y2) / K) := by
  unfold wtp2
  rw [wtpSet2_eq pe po c K y1 y2 hK hpo h1 h2]
  exact csSup_Icc (w_ge _ _ _ hpo)

lemma f1_eq (pe po c K t1 t2 : ℝ) (hK : 0 < K) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) :
    f1 (symChain pe po c K) (K * t1) (K * t2) = K * p (pe - c) po t1 t2 := by
  have hy1 : 0 ≤ K * t1 := mul_nonneg hK.le h1
  have hy2 : 0 ≤ K * t2 := mul_nonneg hK.le h2
  have hw1 := wtp1_eq pe po c K _ _ hK hpo hy1 hy2
  have hw2 := wtp2_eq pe po c K _ _ hK hpo hy1 hy2
  have hle : wtp2 (symChain pe po c K) (K * t1) (K * t2) ≤
      wtp1 (symChain pe po c K) (K * t1) (K * t2) := by rw [hw1, hw2]
  have hT : (K * t1 + K * t2) / K = t1 + t2 := by field_simp
  have hmin : ∀ a b : ℝ, min (K * a) (K * b) = K * min a b :=
    fun a b => (mul_min_of_nonneg a b hK.le).symm
  have hmax : ∀ a : ℝ, max (K * a) 0 = K * max a 0 := by
    intro a
    have := (mul_max_of_nonneg a 0 hK.le).symm
    simpa using this
  unfold f1 finalPrices s11 s12
  rw [if_pos hle, if_pos hle, if_pos hle, hw2, hT]
  simp only [symChain]
  have e1 : min (K * t1) K = K * min t1 1 := by rw [← hmin, mul_one]
  have e2 : max (K * t1 - K) 0 = K * max (t1 - 1) 0 := by
    rw [← hmax]; ring_nf
  have e3 : max (K - K * t2) 0 = K * max (1 - t2) 0 := by
    rw [← hmax]; ring_nf
  rw [e1, e2, e3, hmin]
  unfold p
  ring

lemma f2_eq (pe po c K t1 t2 : ℝ) (hK : 0 < K) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) :
    f2 (symChain pe po c K) (K * t1) (K * t2) = K * q (pe - c) po t1 t2 := by
  have hy1 : 0 ≤ K * t1 := mul_nonneg hK.le h1
  have hy2 : 0 ≤ K * t2 := mul_nonneg hK.le h2
  have hw1 := wtp1_eq pe po c K _ _ hK hpo hy1 hy2
  have hw2 := wtp2_eq pe po c K _ _ hK hpo hy1 hy2
  have hle : wtp2 (symChain pe po c K) (K * t1) (K * t2) ≤
      wtp1 (symChain pe po c K) (K * t1) (K * t2) := by rw [hw1, hw2]
  have hT : (K * t1 + K * t2) / K = t1 + t2 := by field_simp
  have hmin : ∀ a b : ℝ, min (K * a) (K * b) = K * min a b :=
    fun a b => (mul_min_of_nonneg a b hK.le).symm
  have hmax : ∀ a : ℝ, max (K * a) 0 = K * max a 0 := by
    intro a
    have := (mul_max_of_nonneg a 0 hK.le).symm
    simpa using this
  unfold f2 finalPrices s21 s22
  rw [if_pos hle, if_pos hle, if_pos hle, hw2, hT]
  simp only [symChain]
  have e3 : max (K - K * t1) 0 = K * max (1 - t1) 0 := by
    rw [← hmax]; ring_nf
  have e4 : K * t2 - K * max (1 - t1) 0 = K * (t2 - max (1 - t1) 0) := by ring
  have e5 : min (K * max (t2 - max (1 - t1) 0) 0) K = K * min (max (t2 - max (1 - t1) 0) 0) 1 := by
    rw [← hmin, mul_one]
  rw [e3, e4, hmax, e5, hmin]
  unfold q
  ring

-- CORE
section core
variable (m po h u : ℝ)

noncomputable def G1 (t1 t2 : ℝ) : ℝ := h ^ 2 * p m po t1 t2 + h * (1 - h) * p m po t1 0 - u * t1
noncomputable def G2 (t1 t2 : ℝ) : ℝ := h ^ 2 * q m po t1 t2 + h * (1 - h) * p m po t2 0 - u * t2

variable {m po h u}

lemma w_le1 {T : ℝ} (hT : T ≤ 1) : w m po T = m := by
  unfold w
  rw [max_eq_right (by linarith), min_eq_right (zero_le_one' ℝ)]; ring

lemma w_mid {T : ℝ} (h1 : 1 ≤ T) (h2 : T ≤ 2) : w m po T = m - (m - po) * (T - 1) := by
  unfold w
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

lemma w_ge2 {T : ℝ} (h2 : 2 ≤ T) : w m po T = po := by
  unfold w
  rw [max_eq_left (by linarith), min_eq_left (by linarith)]; ring

lemma w_anti (hpo : po ≤ m) {T T' : ℝ} (hT : T ≤ T') : w m po T' ≤ w m po T := by
  unfold w
  have : min 1 (max (T - 1) 0) ≤ min 1 (max (T' - 1) 0) :=
    min_le_min_left _ (max_le_max (by linarith) le_rfl)
  nlinarith

lemma phi_le1 {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : p m po t 0 = m * t := by
  unfold p
  rw [w_le1 (by linarith), min_eq_left h1, max_eq_right (by linarith),
    min_eq_left (by norm_num)]; ring

lemma phi_mid {t : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) : p m po t 0 = m - (m - 2 * po) * (t - 1) := by
  unfold p
  rw [add_zero, w_mid h1 h2, min_eq_right h1, max_eq_left (by linarith),
    max_eq_left (by norm_num), min_eq_left (by linarith)]; ring

lemma phi_ge2 {t : ℝ} (h2 : 2 ≤ t) : p m po t 0 = 2 * po := by
  unfold p
  rw [add_zero, w_ge2 h2, min_eq_right (by linarith), max_eq_left (by linarith),
    max_eq_left (by norm_num), min_eq_right (by linarith)]; ring

lemma phi_lip (h0 : 0 ≤ po) (hpo : po ≤ m) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    p m po t 0 - p m po s 0 ≤ m * (t - s) := by
  rcases le_total s 1 with hs1 | hs1
  · rcases le_total t 1 with ht1 | ht1
    · rw [phi_le1 (by linarith) ht1, phi_le1 hs hs1]; nlinarith
    · rcases le_total t 2 with ht2 | ht2
      · rw [phi_mid ht1 ht2, phi_le1 hs hs1]; nlinarith
      · rw [phi_ge2 ht2, phi_le1 hs hs1]; nlinarith
  · rcases le_total s 2 with hs2 | hs2
    · rcases le_total t 2 with ht2 | ht2
      · rw [phi_mid (by linarith) ht2, phi_mid hs1 hs2]; nlinarith
      · rw [phi_ge2 ht2, phi_mid hs1 hs2]; nlinarith
    · rw [phi_ge2 (by linarith), phi_ge2 hs2]; nlinarith

/-- tail of `φ` beyond 1 -/
lemma phi_tail {k : ℝ} (hk : 0 ≤ k) (hu : 0 < u) (hku : k * (2 * po - m) < u) {t : ℝ}
    (ht : 1 < t) : k * (p m po t 0 - p m po 1 0) < u * (t - 1) := by
  have e1 : p m po 1 0 = m := by rw [phi_le1 (by norm_num) le_rfl]; ring
  rw [e1]
  rcases le_total t 2 with ht2 | ht2
  · rw [phi_mid ht.le ht2]
    have : k * (2 * po - m) * (t - 1) < u * (t - 1) := mul_lt_mul_of_pos_right hku (by linarith)
    nlinarith
  · rw [phi_ge2 ht2]
    have : k * (2 * po - m) * 1 < u * 1 := mul_lt_mul_of_pos_right hku (by linarith)
    nlinarith

lemma p_zero_left {t : ℝ} (ht : 0 ≤ t) : p m po 0 t = 0 := by
  unfold p
  rw [min_eq_left (zero_le_one' ℝ), max_eq_right (by norm_num),
    min_eq_left (le_max_right _ _)]; ring

lemma q_zero_right {t : ℝ} (ht : 0 ≤ t) : q m po t 0 = 0 := by
  unfold q
  rw [min_eq_left (le_max_right _ _), zero_sub, max_eq_right (by simp),
    min_eq_left (zero_le_one' ℝ)]; ring

lemma q_zero_left {t : ℝ} (ht : 0 ≤ t) : q m po 0 t = p m po t 0 := by
  unfold q p
  simp only [sub_zero, zero_add, add_zero]
  rw [max_eq_left (zero_le_one' ℝ), min_comm (max (t - 1) 0) 1]

lemma p_low {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (h12 : t1 + t2 ≤ 1) :
    p m po t1 t2 = m * t1 := by
  unfold p
  rw [w_le1 h12, min_eq_left (by linarith), max_eq_right (by linarith),
    min_eq_left (le_max_right _ _)]; ring

lemma q_low {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (h12 : t1 + t2 ≤ 1) :
    q m po t1 t2 = m * t2 := by
  unfold q
  rw [w_le1 h12, max_eq_left (by linarith : (0:ℝ) ≤ 1 - t1), min_eq_left (by linarith),
    max_eq_right (by linarith), min_eq_left (zero_le_one' ℝ)]; ring

lemma G1_low {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (h12 : t1 + t2 ≤ 1) :
    G1 m po h u t1 t2 = (h * m - u) * t1 := by
  unfold G1
  rw [p_low h1 h2 h12, phi_le1 h1 (by linarith)]; ring

lemma G2_low {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (h12 : t1 + t2 ≤ 1) :
    G2 m po h u t1 t2 = (h * m - u) * t2 := by
  unfold G2
  rw [q_low h1 h2 h12, phi_le1 h2 (by linarith)]; ring

/-- below the capacity line, farmer 1 gains by raising output to it -/
lemma Y1 (hum : u < h * m) {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (h12 : t1 + t2 < 1) :
    G1 m po h u t1 t2 < G1 m po h u (1 - t2) t2 := by
  rw [G1_low h1 h2 h12.le, G1_low (by linarith) h2 (by linarith)]
  nlinarith


/-! ### pieces of `p` and `q` -/

lemma pA {t b : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (hb : 0 ≤ b) : p m po t b = w m po (t + b) * t := by
  unfold p
  rw [min_eq_left h1, max_eq_right (by linarith), min_eq_left (le_max_right _ _)]; ring

lemma pB {t b : ℝ} (h1 : 1 ≤ t) (hb : 0 ≤ b) (h2 : t + b ≤ 2) :
    p m po t b = w m po (t + b) + po * (t - 1) := by
  unfold p
  rw [min_eq_right h1, max_eq_left (by linarith), max_eq_left (by linarith),
    min_eq_left (by linarith)]; ring

lemma pC {t b : ℝ} (h1 : 1 ≤ t) (hb : 0 ≤ b) (h2 : 2 ≤ t + b) :
    p m po t b = po + po * max (1 - b) 0 := by
  unfold p
  rw [w_ge2 h2, min_eq_right h1, max_eq_left (by linarith : (0:ℝ) ≤ t - 1),
    min_eq_right (max_le (by linarith) (by linarith))]; ring

lemma qA {t1 t2 : ℝ} (h1 : 1 ≤ t1) (h2 : 0 ≤ t2) : q m po t1 t2 = po * min t2 1 := by
  unfold q
  rw [max_eq_right (by linarith : 1 - t1 ≤ 0), min_eq_right h2, sub_zero, max_eq_left h2]; ring

lemma qC {t1 t2 : ℝ} (h0 : 0 ≤ t1) (h1 : t1 ≤ 1) (hY1 : 1 ≤ t1 + t2) (hY2 : t1 + t2 ≤ 2) :
    q m po t1 t2 = w m po (t1 + t2) * (1 - t1) + po * (t1 + t2 - 1) := by
  unfold q
  rw [max_eq_left (by linarith : (0:ℝ) ≤ 1 - t1), min_eq_right (by linarith : 1 - t1 ≤ t2),
    max_eq_left (by linarith : (0:ℝ) ≤ t2 - (1 - t1)), min_eq_left (by linarith : t2 - (1 - t1) ≤ 1)]
  ring

lemma qD {t1 t2 : ℝ} (h0 : 0 ≤ t1) (h1 : t1 ≤ 1) (hY2 : 2 ≤ t1 + t2) :
    q m po t1 t2 = po * (1 - t1) + po := by
  unfold q
  rw [w_ge2 hY2, max_eq_left (by linarith : (0:ℝ) ≤ 1 - t1), min_eq_right (by linarith : 1 - t1 ≤ t2),
    max_eq_left (by linarith : (0:ℝ) ≤ t2 - (1 - t1)), min_eq_right (by linarith : (1:ℝ) ≤ t2 - (1 - t1))]
  ring

lemma phi_one : p m po 1 0 = m := by rw [phi_le1 (by norm_num) le_rfl]; ring

/-! ### part 3 -/

section part3
variable (hh0 : 0 < h) (hh1 : h < 1) (h0 : 0 ≤ po) (hpo : po ≤ m) (hu : 0 < u) (hum : u < h * m)
  (ha3 : h ^ 2 * (m - 2 * po) - h * (1 - h) * m + u ≤ 0)
  (hb3 : 0 < u + h * (1 - h) * (m - 2 * po))
include hh0 hh1 h0 hpo hu hum ha3 hb3

lemma s1_pos : 0 < h ^ 2 * po + h * (1 - h) * m - u := by
  rcases eq_or_lt_of_le hpo with he | hlt
  · subst he; nlinarith
  · have : 0 < h ^ 2 * (m - po) := by positivity
    nlinarith

lemma A3 {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 1 ≤ t2) (hne : t1 ≠ 1) :
    G1 m po h u t1 t2 < G1 m po h u 1 t2 := by
  unfold G1
  have hp1 : p m po 1 t2 = po := by
    rw [pC le_rfl (by linarith) (by linarith), max_eq_right (by linarith)]; ring
  rw [hp1, phi_one]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [pA h1 hlt.le (by linarith), phi_le1 h1 hlt.le]
    have hw : w m po (t1 + t2) ≤ w m po (1 + t1) := w_anti hpo (by linarith)
    rw [w_mid (T := 1 + t1) (by linarith) (by linarith)] at hw
    have key : h ^ 2 * (w m po (t1 + t2) * t1) ≤ h ^ 2 * ((m - (m - po) * (1 + t1 - 1)) * t1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hw h1
    have hB : 0 < h ^ 2 * (po - (m - po) * t1) + h * (1 - h) * m - u := by
      rcases eq_or_lt_of_le hpo with he | hlt'
      · subst he; nlinarith
      · have : 0 < h ^ 2 * (m - po) * (1 - t1) := by
          have : 0 < 1 - t1 := by linarith
          positivity
        nlinarith
    nlinarith [mul_pos (sub_pos.2 hlt) hB]
  · rw [pC hgt.le (by linarith) (by linarith), max_eq_right (by linarith)]
    have := phi_tail (m := m) (po := po) (u := u) (k := h * (1 - h))
      (by nlinarith) hu (by nlinarith) hgt
    rw [phi_one] at this
    nlinarith

lemma B3 {t1 t2 : ℝ} (h1 : 1 ≤ t1) (h2 : 0 ≤ t2) (hne : t2 ≠ 1) :
    G2 m po h u t1 t2 < G2 m po h u t1 1 := by
  unfold G2
  rw [qA h1 h2, qA h1 zero_le_one, phi_one, min_self]
  have hs := s1_pos hh0 hh1 h0 hpo hu hum ha3 hb3
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [min_eq_left hlt.le, phi_le1 h2 hlt.le]
    nlinarith [mul_pos (sub_pos.2 hlt) hs]
  · rw [min_eq_right hgt.le]
    have := phi_tail (m := m) (po := po) (u := u) (k := h * (1 - h))
      (by nlinarith) hu (by nlinarith) hgt
    rw [phi_one] at this
    nlinarith

lemma C3 {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (ht1 : t1 < 1) (ht2 : t2 < 1)
    (hY : 1 ≤ t1 + t2) : G2 m po h u t1 t2 < G2 m po h u t1 1 := by
  unfold G2
  rw [qC h1 ht1.le hY (by linarith), qC h1 ht1.le (by linarith) (by linarith), phi_one,
    phi_le1 h2 ht2.le, w_mid hY (by linarith), w_mid (by linarith) (by linarith)]
  have hB : 0 < h ^ 2 * (po - (m - po) * (1 - t1)) + h * (1 - h) * m - u := by
    rcases eq_or_lt_of_le hpo with he | hlt'
    · subst he; nlinarith
    · have : 0 < h ^ 2 * (m - po) * t1 := by
        have : 0 < t1 := by linarith
        positivity
      nlinarith
  nlinarith [mul_pos (sub_pos.2 ht2) hB]

end part3

/-! ### part 4 -/

section part4
variable (hh0 : 0 < h) (hh1 : h < 1) (h0 : 0 ≤ po) (hpo : po ≤ m) (hu : 0 < u)
  (h4 : u < h * (1 - h) * (2 * po - m))
include hh0 hh1 h0 hpo hu h4

lemma m_le_2po : m ≤ 2 * po := by
  by_contra hc
  push_neg at hc
  have : 0 < h * (1 - h) := by nlinarith
  nlinarith [mul_pos this (sub_pos.2 hc)]

lemma p_bound4 {t b : ℝ} (ht : 0 ≤ t) (hb : 0 ≤ b) : p m po t b ≤ po * (1 + max (1 - b) 0) := by
  have h2m := m_le_2po hh0 hh1 h0 hpo hu h4
  rcases le_total 1 b with hb1 | hb1
  · rw [max_eq_right (by linarith)]
    rcases le_total t 1 with ht1 | ht1
    · rw [pA ht ht1 hb]
      have hw : w m po (t + b) ≤ w m po (1 + t) := w_anti hpo (by linarith)
      rw [w_mid (T := 1 + t) (by linarith) (by linarith)] at hw
      have k1 : w m po (t + b) * t ≤ (m - (m - po) * (1 + t - 1)) * t := mul_le_mul_of_nonneg_right hw ht
      have k2 : 0 ≤ (1 - t) * (po - (m - po) * t) := by
        apply mul_nonneg (by linarith)
        nlinarith
      nlinarith
    · rw [pC ht1 hb (by linarith), max_eq_right (by linarith)]; ring_nf; linarith
  · rw [max_eq_left (by linarith)]
    rcases le_total t 1 with ht1 | ht1
    · rcases le_total (t + b) 1 with hY | hY
      · rw [p_low ht hb hY]; nlinarith
      · rw [pA ht ht1 hb, w_mid hY (by linarith)]
        have k2 : 0 ≤ (1 - (t + b - 1)) * (po - (m - po) * t) := by
          apply mul_nonneg (by linarith)
          nlinarith
        nlinarith
    · rcases le_total (t + b) 2 with hY | hY
      · rw [pB ht1 hb hY, w_mid (by linarith) hY]
        nlinarith
      · rw [pC ht1 hb hY, max_eq_left (by linarith)]
        exact le_of_eq (by ring)

lemma q_bound4 {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) :
    q m po t1 t2 ≤ po * (max (1 - t1) 0 + 1) := by
  have h2m := m_le_2po hh0 hh1 h0 hpo hu h4
  rcases le_total 1 t1 with ht1 | ht1
  · rw [qA ht1 h2, max_eq_right (by linarith)]
    have : min t2 1 ≤ 1 := min_le_right _ _
    nlinarith
  · rw [max_eq_left (by linarith)]
    rcases le_total (t1 + t2) 1 with hY | hY
    · rw [q_low h1 h2 hY]; nlinarith
    · rcases le_total (t1 + t2) 2 with hY2 | hY2
      · rw [qC h1 ht1 hY hY2, w_mid hY hY2]
        have k2 : 0 ≤ (1 - (t1 + t2 - 1)) * (po - (m - po) * (1 - t1)) := by
          apply mul_nonneg (by linarith)
          nlinarith
        nlinarith
      · rw [qD h1 ht1 hY2]
        exact le_of_eq (by ring)

lemma g_inc {t : ℝ} (ht : 0 ≤ t) (ht2 : t < 2) :
    h * (1 - h) * p m po t 0 - u * t < h * (1 - h) * (2 * po) - u * 2 := by
  have hk : 0 < h * (1 - h) := by nlinarith
  rcases le_total t 1 with ht1 | ht1
  · rw [phi_le1 ht ht1]
    have : 0 ≤ h * (1 - h) * m - u := by nlinarith
    nlinarith [mul_nonneg this (by linarith : (0:ℝ) ≤ 1 - t)]
  · rw [phi_mid ht1 ht2.le]
    nlinarith [mul_pos (by linarith : (0:ℝ) < 2 - t) (by linarith : 0 < h * (1 - h) * (2 * po - m) - u)]

lemma D4 {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (hne : t1 ≠ 2) :
    G1 m po h u t1 t2 < G1 m po h u 2 t2 := by
  unfold G1
  rw [pC (t := 2) (by norm_num) h2 (by linarith), phi_ge2 (t := 2) le_rfl]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have k1 := p_bound4 hh0 hh1 h0 hpo hu h4 h1 h2
    have k2 := g_inc hh0 hh1 h0 hpo hu h4 h1 hlt
    have : h ^ 2 * p m po t1 t2 ≤ h ^ 2 * (po * (1 + max (1 - t2) 0)) :=
      mul_le_mul_of_nonneg_left k1 (by positivity)
    nlinarith
  · rw [pC (t := t1) (by linarith) h2 (by linarith), phi_ge2 hgt.le]
    nlinarith

lemma E4 {t1 t2 : ℝ} (h1 : 0 ≤ t1) (h2 : 0 ≤ t2) (hne : t2 ≠ 2) :
    G2 m po h u t1 t2 < G2 m po h u t1 2 := by
  have hq2 : ∀ s, 2 ≤ s → q m po t1 s = po * (max (1 - t1) 0 + 1) := by
    intro s hs
    rcases le_total 1 t1 with ht1 | ht1
    · rw [qA ht1 (by linarith), max_eq_right (by linarith), min_eq_right (by linarith)]; ring
    · rw [qD h1 ht1 (by linarith), max_eq_left (by linarith)]; ring
  unfold G2
  rw [hq2 2 le_rfl, phi_ge2 le_rfl]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have k1 := q_bound4 hh0 hh1 h0 hpo hu h4 h1 h2
    have k2 := g_inc hh0 hh1 h0 hpo hu h4 h2 hlt
    have : h ^ 2 * q m po t1 t2 ≤ h ^ 2 * (po * (max (1 - t1) 0 + 1)) :=
      mul_le_mul_of_nonneg_left k1 (by positivity)
    nlinarith
  · rw [hq2 t2 hgt.le, phi_ge2 hgt.le]
    nlinarith

end part4

/-! ### part 1 -/

lemma w_le_m (T : ℝ) (hpo : po ≤ m) : w m po T ≤ m := by
  unfold w
  have : 0 ≤ min 1 (max (T - 1) 0) := le_min (by norm_num) (le_max_right _ _)
  nlinarith

lemma w_ge_po (T : ℝ) (hpo : po ≤ m) : po ≤ w m po T := by
  unfold w
  have : min 1 (max (T - 1) 0) ≤ 1 := min_le_left _ _
  nlinarith

section part1
variable (hh0 : 0 < h) (hh1 : h < 1) (h0 : 0 ≤ po) (hpo : po ≤ m) (hu : 0 < u) (hum : u < h * m)
  (h1p : h ^ 2 * po + h * (1 - h) * m < u)
include hh0 hh1 h0 hpo hu hum h1p

lemma q_dec_bound {t1 t2 : ℝ} (h1 : 0 ≤ t1) (hr : max (1 - t1) 0 ≤ t2) :
    q m po t1 t2 - q m po t1 (max (1 - t1) 0) ≤ po * (t2 - max (1 - t1) 0) := by
  have h2 : 0 ≤ t2 := le_trans (le_max_right _ _) hr
  rcases le_total 1 t1 with ht1 | ht1
  · rw [max_eq_right (by linarith), qA ht1 h2, qA ht1 le_rfl]
    have : min t2 1 ≤ t2 := min_le_left _ _
    simp only [min_eq_left (zero_le_one' ℝ)]
    nlinarith
  · rw [max_eq_left (by linarith)] at hr ⊢
    rw [qC (t2 := 1 - t1) h1 ht1 (by linarith) (by linarith), w_le1 (T := t1 + (1 - t1)) (by linarith)]
    rcases le_total (t1 + t2) 2 with hY2 | hY2
    · rw [qC h1 ht1 (by linarith) hY2]
      have := w_le_m (t1 + t2) hpo
      nlinarith [mul_le_mul_of_nonneg_right this (by linarith : (0:ℝ) ≤ 1 - t1)]
    · rw [qD h1 ht1 hY2]
      nlinarith

lemma F2dec {t1 t2 : ℝ} (h1 : 0 ≤ t1) (hr : max (1 - t1) 0 < t2) :
    G2 m po h u t1 t2 < G2 m po h u t1 (max (1 - t1) 0) := by
  unfold G2
  have k1 := q_dec_bound hh0 hh1 h0 hpo hu hum h1p h1 hr.le
  have k2 := phi_lip h0 hpo (le_max_right (1 - t1) 0) hr.le
  have k1' := mul_le_mul_of_nonneg_left k1 (by positivity : (0:ℝ) ≤ h ^ 2)
  have k2' := mul_le_mul_of_nonneg_left k2 (by nlinarith : (0:ℝ) ≤ h * (1 - h))
  have hd : 0 < t2 - max (1 - t1) 0 := by linarith
  nlinarith [mul_pos hd (by linarith : 0 < u - (h ^ 2 * po + h * (1 - h) * m))]

lemma F1tail {t : ℝ} (ht : 1 < t) : G1 m po h u t 0 < G1 m po h u 1 0 := by
  unfold G1
  have hk : h * (2 * po - m) < u := by
    nlinarith [mul_nonneg (by nlinarith : (0:ℝ) ≤ h * (2 - h)) (sub_nonneg.2 hpo)]
  have := phi_tail (m := m) (po := po) (u := u) (k := h) hh0.le hu hk ht
  rw [phi_one] at this ⊢
  nlinarith

lemma Seg1 {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hseg : h * m - u ≤ h ^ 2 * (m - po) * a)
    (ht : 0 ≤ t) : G1 m po h u t (1 - a) ≤ G1 m po h u a (1 - a) := by
  have hb0 : 0 ≤ 1 - a := by linarith
  have hGa : G1 m po h u a (1 - a) = (h * m - u) * a := G1_low ha0 hb0 (by linarith)
  have mid : ∀ s, a ≤ s → s ≤ 1 → G1 m po h u s (1 - a) ≤ (h * m - u) * a := by
    intro s hs1 hs2
    unfold G1
    rw [pA (by linarith) hs2 hb0, phi_le1 (by linarith) hs2, w_mid (by linarith) (by linarith)]
    have e : 0 ≤ (s - a) * (h ^ 2 * (m - po) * (s - a)) := by
      apply mul_nonneg (by linarith)
      apply mul_nonneg (by nlinarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hseg (by linarith : (0:ℝ) ≤ s - a)]
  rw [hGa]
  rcases le_total t a with hta | hta
  · rw [G1_low ht hb0 (by linarith)]
    nlinarith
  · rcases le_total t 1 with ht1 | ht1
    · exact mid t hta ht1
    · have h1a := mid 1 ha1 le_rfl
      have hp1 : p m po 1 (1 - a) = w m po (1 + (1 - a)) := by
        rw [pA zero_le_one le_rfl hb0]; ring
      have hpt : p m po t (1 - a) - p m po 1 (1 - a) ≤ po * (t - 1) := by
        rw [hp1]
        rcases le_total (t + (1 - a)) 2 with hY | hY
        · rw [pB ht1 hb0 hY]
          have := w_anti hpo (show 1 + (1 - a) ≤ t + (1 - a) by linarith) (m := m) (po := po)
          linarith
        · rw [pC ht1 hb0 hY, max_eq_left (by linarith)]
          have := w_ge_po (m := m) (1 + (1 - a)) hpo
          nlinarith
      have k2 := phi_lip h0 hpo zero_le_one ht1
      rw [phi_one] at k2
      have : G1 m po h u t (1 - a) - G1 m po h u 1 (1 - a) ≤
          (h ^ 2 * po + h * (1 - h) * m - u) * (t - 1) := by
        unfold G1
        rw [phi_one]
        have k1' := mul_le_mul_of_nonneg_left hpt (by positivity : (0:ℝ) ≤ h ^ 2)
        have k2' := mul_le_mul_of_nonneg_left k2 (by nlinarith : (0:ℝ) ≤ h * (1 - h))
        nlinarith
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t - 1)
        (by linarith : 0 ≤ u - (h ^ 2 * po + h * (1 - h) * m))]

lemma Seg2 {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    G2 m po h u a t ≤ G2 m po h u a (1 - a) := by
  have hb0 : 0 ≤ 1 - a := by linarith
  rw [G2_low ha0 hb0 (by linarith)]
  rcases le_total t (1 - a) with hta | hta
  · rw [G2_low ha0 ht (by linarith)]
    nlinarith
  · rcases eq_or_lt_of_le hta with he | hlt
    · rw [← he, G2_low ha0 hb0 (by linarith)]
    · have := F2dec hh0 hh1 h0 hpo hu hum h1p ha0 (by rw [max_eq_left hb0]; exact hlt)
      rw [max_eq_left hb0, G2_low ha0 hb0 (by linarith)] at this
      linarith

end part1

end core


/-! ### from the model to the normalized payoffs -/

section bridge2
open AgriChain.LandAlloc

lemma F1_eq (pe po c K U A h H x1 x2 : ℝ) (hK : 0 < K) (hH : 0 < H) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) :
    F1 (symChain pe po c K) (IID h H) U A x1 x2 =
      K * G1 (pe - c) po h (U / H) (x1 * H / K) (x2 * H / K) + A := by
  have ht1 : 0 ≤ x1 * H / K := by positivity
  have ht2 : 0 ≤ x2 * H / K := by positivity
  have e1 : x1 * H = K * (x1 * H / K) := by field_simp
  have e2 : x2 * H = K * (x2 * H / K) := by field_simp
  have a1 := f1_eq pe po c K _ _ hK hpo ht1 ht2
  have a2 := f1_eq pe po c K _ _ hK hpo ht1 le_rfl
  have a3 := f1_eq pe po c K _ _ hK hpo le_rfl ht2
  have a4 := f1_eq pe po c K _ _ hK hpo le_rfl le_rfl
  rw [mul_zero] at a2 a3 a4
  unfold F1
  show h ^ 2 * f1 (symChain pe po c K) (x1 * H) (x2 * H) + h * (1 - h) * f1 (symChain pe po c K) (x1 * H) 0 +
    (1 - h) * h * f1 (symChain pe po c K) 0 (x2 * H) + (1 - h) ^ 2 * f1 (symChain pe po c K) 0 0 -
    x1 * U + A = _
  rw [e1, e2, a1, a2, a3, a4, p_zero_left ht2, p_zero_left le_rfl]
  unfold G1
  field_simp
  ring

lemma F2_eq (pe po c K U A h H x1 x2 : ℝ) (hK : 0 < K) (hH : 0 < H) (hpo : po ≤ pe - c)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) :
    F2 (symChain pe po c K) (IID h H) U A x1 x2 =
      K * G2 (pe - c) po h (U / H) (x1 * H / K) (x2 * H / K) + A := by
  have ht1 : 0 ≤ x1 * H / K := by positivity
  have ht2 : 0 ≤ x2 * H / K := by positivity
  have e1 : x1 * H = K * (x1 * H / K) := by field_simp
  have e2 : x2 * H = K * (x2 * H / K) := by field_simp
  have a1 := f2_eq pe po c K _ _ hK hpo ht1 ht2
  have a2 := f2_eq pe po c K _ _ hK hpo ht1 le_rfl
  have a3 := f2_eq pe po c K _ _ hK hpo le_rfl ht2
  have a4 := f2_eq pe po c K _ _ hK hpo le_rfl le_rfl
  rw [mul_zero] at a2 a3 a4
  unfold F2
  show h ^ 2 * f2 (symChain pe po c K) (x1 * H) (x2 * H) + h * (1 - h) * f2 (symChain pe po c K) (x1 * H) 0 +
    (1 - h) * h * f2 (symChain pe po c K) 0 (x2 * H) + (1 - h) ^ 2 * f2 (symChain pe po c K) 0 0 -
    x2 * U + A = _
  rw [e1, e2, a1, a2, a3, a4, q_zero_right ht1, q_zero_right le_rfl, q_zero_left ht2]
  unfold G2
  field_simp
  ring

lemma isEq_iff (C : Chain) (Y : AON) (U1 U2 A1 A2 L1 L2 x1 x2 : ℝ) :
    IsEq C Y U1 U2 A1 A2 L1 L2 x1 x2 ↔
      ((0 ≤ x1 ∧ x1 ≤ L1) ∧ (0 ≤ x2 ∧ x2 ≤ L2)) ∧
      (∀ x, 0 ≤ x → x ≤ L1 → F1 C Y U1 A1 x x2 ≤ F1 C Y U1 A1 x1 x2) ∧
      (∀ x, 0 ≤ x → x ≤ L2 → F2 C Y U2 A2 x1 x ≤ F2 C Y U2 A2 x1 x2) := by
  have u0 : ∀ x : ℝ, Function.update (β := fun _ : Fin 2 => ℝ) ![x1, x2] 0 x = ![x, x2] := by
    intro x; ext i; fin_cases i <;> simp
  have u1 : ∀ x : ℝ, Function.update (β := fun _ : Fin 2 => ℝ) ![x1, x2] 1 x = ![x1, x] := by
    intro x; ext i; fin_cases i <;> simp
  unfold IsEq CarbonDoubleCount.Planner.IsPureNash
  constructor
  · rintro ⟨hf, hd⟩
    have f0 := hf 0
    have f1' := hf 1
    simp only [Set.mem_Icc] at f0 f1'
    refine ⟨⟨by simpa using f0, by simpa using f1'⟩, ?_, ?_⟩
    · intro x hx0 hx1
      have := hd 0 x (by simp only [Set.mem_Icc]; simpa using ⟨hx0, hx1⟩)
      rw [u0] at this
      simpa [payoff] using this
    · intro x hx0 hx1
      have := hd 1 x (by simp only [Set.mem_Icc]; simpa using ⟨hx0, hx1⟩)
      rw [u1] at this
      simpa [payoff] using this
  · rintro ⟨⟨h1, h2⟩, hd1, hd2⟩
    refine ⟨?_, ?_⟩
    · intro n
      fin_cases n
      · simpa [Set.mem_Icc] using h1
      · simpa [Set.mem_Icc] using h2
    · intro n x hx
      fin_cases n
      · simp only [Set.mem_Icc] at hx
        have hx' : 0 ≤ x ∧ x ≤ L1 := by simpa using hx
        show payoff C Y U1 U2 A1 A2 0 (Function.update ![x1, x2] 0 x) ≤ payoff C Y U1 U2 A1 A2 0 ![x1, x2]
        rw [u0]
        simpa [payoff] using hd1 x hx'.1 hx'.2
      · simp only [Set.mem_Icc] at hx
        have hx' : 0 ≤ x ∧ x ≤ L2 := by simpa using hx
        show payoff C Y U1 U2 A1 A2 1 (Function.update ![x1, x2] 1 x) ≤ payoff C Y U1 U2 A1 A2 1 ![x1, x2]
        rw [u1]
        simpa [payoff] using hd2 x hx'.1 hx'.2

lemma eq_iff_G (pe po c K U A h H L1 L2 x1 x2 : ℝ) (hK : 0 < K) (hH : 0 < H)
    (hpo : po ≤ pe - c) :
    IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 ↔
      ((0 ≤ x1 ∧ x1 ≤ L1) ∧ (0 ≤ x2 ∧ x2 ≤ L2)) ∧
      (∀ x, 0 ≤ x → x ≤ L1 → G1 (pe - c) po h (U / H) (x * H / K) (x2 * H / K) ≤
        G1 (pe - c) po h (U / H) (x1 * H / K) (x2 * H / K)) ∧
      (∀ x, 0 ≤ x → x ≤ L2 → G2 (pe - c) po h (U / H) (x1 * H / K) (x * H / K) ≤
        G2 (pe - c) po h (U / H) (x1 * H / K) (x2 * H / K)) := by
  rw [isEq_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd1, hd2⟩
    refine ⟨⟨h1, h2⟩, ?_, ?_⟩
    · intro x hx0 hx1
      have := hd1 x hx0 hx1
      rw [F1_eq pe po c K U A h H _ _ hK hH hpo hx0 h2.1,
        F1_eq pe po c K U A h H _ _ hK hH hpo h1.1 h2.1] at this
      exact (mul_le_mul_iff_of_pos_left hK).1 (by linarith)
    · intro x hx0 hx1
      have := hd2 x hx0 hx1
      rw [F2_eq pe po c K U A h H _ _ hK hH hpo h1.1 hx0,
        F2_eq pe po c K U A h H _ _ hK hH hpo h1.1 h2.1] at this
      exact (mul_le_mul_iff_of_pos_left hK).1 (by linarith)
  · rintro ⟨⟨h1, h2⟩, hd1, hd2⟩
    refine ⟨⟨h1, h2⟩, ?_, ?_⟩
    · intro x hx0 hx1
      rw [F1_eq pe po c K U A h H _ _ hK hH hpo hx0 h2.1,
        F1_eq pe po c K U A h H _ _ hK hH hpo h1.1 h2.1]
      have := mul_le_mul_of_nonneg_left (hd1 x hx0 hx1) hK.le
      linarith
    · intro x hx0 hx1
      rw [F2_eq pe po c K U A h H _ _ hK hH hpo h1.1 hx0,
        F2_eq pe po c K U A h H _ _ hK hH hpo h1.1 h2.1]
      have := mul_le_mul_of_nonneg_left (hd2 x hx0 hx1) hK.le
      linarith

end bridge2

end AgriLA6

open AgriChain.LandAlloc in
theorem solution (pe po c K U A h H L1 L2 : ℝ)
    (hh : 0 < h ∧ h < 1) (hH : 0 < H) (hK : 0 < K) (hU : 0 < U)
    (hpo : 0 ≤ po ∧ po ≤ pe - c) (hL : 2 * K / H ≤ L1 ∧ 2 * K / H ≤ L2)
    (hpart : U / (h * H) < pe - c) :
    -- part 1: under-production, a continuum of equilibria on x₁ + x₂ = K/H
    (po < U / (h ^ 2 * H) - (1 - h) / h * (pe - c) →
      (∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 →
        x1 + x2 = K / H) ∧
      ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Icc a b,
        IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 t (K / H - t)) ∧
    -- part 3: full production, (K/H, K/H) is the unique equilibrium
    ((2 * h - 1) / (2 * h) * (pe - c) + U / (2 * h ^ 2 * H) ≤ po →
      po < ((pe - c) + U / (h * (1 - h) * H)) / 2 →
      ∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 ↔
        (x1 = K / H ∧ x2 = K / H)) ∧
    -- part 4: over-production, (2K/H, 2K/H) is the unique equilibrium (strict threshold)
    (((pe - c) + U / (h * (1 - h) * H)) / 2 < po →
      ∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 ↔
        (x1 = 2 * K / H ∧ x2 = 2 * K / H)) := by
  obtain ⟨hh0, hh1⟩ := hh
  obtain ⟨h0, hpo'⟩ := hpo
  obtain ⟨hL1, hL2⟩ := hL
  set m := pe - c with hm
  set u := U / H with hu_def
  have hu : 0 < u := by positivity
  have hum : u < h * m := by
    have e : U / (h * H) = u / h := by rw [hu_def]; field_simp
    rw [e, div_lt_iff₀ hh0] at hpart
    linarith
  have hk : 0 < h * (1 - h) := by nlinarith
  have eK : U / (h * (1 - h) * H) = u / (h * (1 - h)) := by
    rw [hu_def]; field_simp
  -- deviations of size at most 2 (in normalized units) are feasible
  have dev : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 2 → ∀ L : ℝ, 2 * K / H ≤ L →
      0 ≤ τ * K / H ∧ τ * K / H ≤ L ∧ τ * K / H * H / K = τ := by
    intro τ h0' h2' L hL
    refine ⟨by positivity, ?_, by field_simp⟩
    have : τ * K / H ≤ 2 * K / H := by
      apply div_le_div_of_nonneg_right _ hH.le
      nlinarith
    linarith
  have tback : ∀ x : ℝ, x * H / K = 1 → x = K / H := by
    intro x hx
    field_simp at hx ⊢
    linarith
  have tback2 : ∀ x : ℝ, x * H / K = 2 → x = 2 * K / H := by
    intro x hx
    field_simp at hx ⊢
    linarith
  have tK : K / H * H / K = 1 := by field_simp
  have t2K : 2 * K / H * H / K = 2 := by field_simp
  have hKL1 : K / H ≤ L1 := by
    have : K / H ≤ 2 * K / H := div_le_div_of_nonneg_right (by linarith) hH.le
    linarith
  have hKL2 : K / H ≤ L2 := by
    have : K / H ≤ 2 * K / H := div_le_div_of_nonneg_right (by linarith) hH.le
    linarith
  -- unpack an equilibrium into normalized deviation inequalities
  have unpack : ∀ x1 x2 : ℝ, IsEq (symChain pe po c K) (IID h H) U U A A L1 L2 x1 x2 →
      0 ≤ x1 * H / K ∧ 0 ≤ x2 * H / K ∧
      (∀ τ, 0 ≤ τ → τ ≤ 2 → AgriLA6.G1 m po h u τ (x2 * H / K) ≤ AgriLA6.G1 m po h u (x1 * H / K) (x2 * H / K)) ∧
      (∀ τ, 0 ≤ τ → τ ≤ 2 → AgriLA6.G2 m po h u (x1 * H / K) τ ≤ AgriLA6.G2 m po h u (x1 * H / K) (x2 * H / K)) := by
    intro x1 x2 hE
    obtain ⟨⟨⟨a1, _⟩, ⟨a2, _⟩⟩, d1, d2⟩ := (AgriLA6.eq_iff_G pe po c K U A h H L1 L2 x1 x2 hK hH hpo').1 hE
    refine ⟨by positivity, by positivity, ?_, ?_⟩
    · intro τ h0' h2'
      obtain ⟨b0, b1, b2⟩ := dev τ h0' h2' L1 hL1
      have := d1 _ b0 b1
      rwa [b2] at this
    · intro τ h0' h2'
      obtain ⟨b0, b1, b2⟩ := dev τ h0' h2' L2 hL2
      have := d2 _ b0 b1
      rwa [b2] at this
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    intro H1
    have h1p : h ^ 2 * po + h * (1 - h) * m < u := by
      have e : U / (h ^ 2 * H) = u / h ^ 2 := by rw [hu_def]; field_simp
      rw [e] at H1
      have key : h ^ 2 * (u / h ^ 2 - (1 - h) / h * m) = u - h * (1 - h) * m := by
        field_simp
      have := mul_lt_mul_of_pos_left H1 (by positivity : (0:ℝ) < h ^ 2)
      linarith
    have hmpo : po < m := by nlinarith
    refine ⟨?_, ?_⟩
    · intro x1 x2 hE
      obtain ⟨a1, a2, d1, d2⟩ := unpack x1 x2 hE
      set t1 := x1 * H / K with ht1
      set t2 := x2 * H / K with ht2
      have hY : 1 ≤ t1 + t2 := by
        by_contra hc
        push_neg at hc
        have := AgriLA6.Y1 (po := po) hum a1 a2 hc
        have := d1 (1 - t2) (by linarith) (by linarith)
        linarith
      have hsum : t1 + t2 = 1 := by
        by_contra hne
        have hgt : 1 < t1 + t2 := lt_of_le_of_ne hY (Ne.symm hne)
        rcases le_total t1 1 with h11 | h11
        · have hr : max (1 - t1) 0 = 1 - t1 := max_eq_left (by linarith)
          have := AgriLA6.F2dec (t2 := t2) hh0 hh1 h0 hpo' hu hum h1p a1 (by rw [hr]; linarith)
          have := d2 (max (1 - t1) 0) (le_max_right _ _) (by rw [hr]; linarith)
          linarith
        · have hr : max (1 - t1) 0 = 0 := max_eq_right (by linarith)
          rcases eq_or_lt_of_le a2 with h20 | h20
          · have ht1' : 1 < t1 := by linarith
            have := AgriLA6.F1tail hh0 hh1 h0 hpo' hu hum h1p ht1'
            have := d1 1 zero_le_one (by norm_num)
            rw [← h20] at this
            linarith
          · have := AgriLA6.F2dec (t2 := t2) hh0 hh1 h0 hpo' hu hum h1p a1 (by rw [hr]; linarith)
            have := d2 (max (1 - t1) 0) (le_max_right _ _) (by rw [hr]; norm_num)
            linarith
      have : (x1 + x2) * H / K = 1 := by rw [add_mul, add_div]; linarith
      exact tback _ this
    · set as := (h * m - u) / (h ^ 2 * (m - po)) with has
      have hd : 0 < h ^ 2 * (m - po) := by
        have : 0 < m - po := by linarith
        positivity
      have has0 : 0 < as := div_pos (by linarith) hd
      have has1 : as < 1 := by
        rw [div_lt_one hd]
        nlinarith
      refine ⟨as * K / H, K / H, ?_, ?_⟩
      · apply div_lt_div_of_pos_right _ hH
        nlinarith
      · rintro t ⟨ht0, ht1⟩
        set τ := t * H / K with hτ
        have hτ0 : as ≤ τ := by
          rw [hτ]
          rw [le_div_iff₀ hK]
          have := (div_le_iff₀ hH).1 ht0
          linarith
        have hτ1 : τ ≤ 1 := by
          rw [hτ, div_le_one hK]
          have := (le_div_iff₀ hH).1 ht1
          linarith
        have hseg : h * m - u ≤ h ^ 2 * (m - po) * τ := by
          have := mul_le_mul_of_nonneg_left hτ0 hd.le
          rw [has, mul_div_cancel₀ _ hd.ne'] at this
          linarith
        have e2 : (K / H - t) * H / K = 1 - τ := by
          rw [hτ]; field_simp
        have ht0' : 0 ≤ t := le_trans (by positivity) ht0
        apply (AgriLA6.eq_iff_G pe po c K U A h H L1 L2 _ _ hK hH hpo').2
        refine ⟨⟨⟨ht0', le_trans ht1 hKL1⟩, ⟨by linarith, by linarith⟩⟩, ?_, ?_⟩
        · intro x hx0 _
          rw [e2]
          exact AgriLA6.Seg1 hh0 hh1 h0 hpo' hu hum h1p (by linarith) hτ1 hseg (by positivity)
        · intro x hx0 _
          rw [e2]
          exact AgriLA6.Seg2 hh0 hh1 h0 hpo' hu hum h1p (by linarith) hτ1 (by positivity)
  · -- part 3
    intro H3a H3b
    have ha3 : h ^ 2 * (m - 2 * po) - h * (1 - h) * m + u ≤ 0 := by
      have e : U / (2 * h ^ 2 * H) = u / (2 * h ^ 2) := by rw [hu_def]; field_simp
      rw [e] at H3a
      have key : 2 * h ^ 2 * ((2 * h - 1) / (2 * h) * m + u / (2 * h ^ 2)) =
          (2 * h - 1) * h * m + u := by
        field_simp <;> ring
      have := mul_le_mul_of_nonneg_left H3a (by positivity : (0:ℝ) ≤ 2 * h ^ 2)
      nlinarith
    have hb3 : 0 < u + h * (1 - h) * (m - 2 * po) := by
      rw [eK] at H3b
      have key : h * (1 - h) * (m + u / (h * (1 - h))) = h * (1 - h) * m + u := by
        have hne1 : (1 : ℝ) - h ≠ 0 := by linarith
        have hne2 : h * (1 - h) ≠ 0 := ne_of_gt hk
        field_simp <;> ring
      have := mul_lt_mul_of_pos_left H3b hk
      nlinarith
    intro x1 x2
    constructor
    · intro hE
      obtain ⟨a1, a2, d1, d2⟩ := unpack x1 x2 hE
      set t1 := x1 * H / K with ht1
      set t2 := x2 * H / K with ht2
      have hY : 1 ≤ t1 + t2 := by
        by_contra hc
        push_neg at hc
        have := AgriLA6.Y1 (po := po) hum a1 a2 hc
        have := d1 (1 - t2) (by linarith) (by linarith)
        linarith
      have key : t1 = 1 ∧ t2 = 1 := by
        rcases le_or_gt 1 t1 with h11 | h11
        · have e2 : t2 = 1 := by
            by_contra hne
            have := AgriLA6.B3 hh0 hh1 h0 hpo' hu hum ha3 hb3 h11 a2 hne
            have := d2 1 zero_le_one (by norm_num)
            linarith
          refine ⟨?_, e2⟩
          by_contra hne
          have := AgriLA6.A3 hh0 hh1 h0 hpo' hu hum ha3 hb3 a1 (le_of_eq e2.symm) hne
          have := d1 1 zero_le_one (by norm_num)
          linarith
        · exfalso
          rcases le_or_gt 1 t2 with h22 | h22
          · have := AgriLA6.A3 hh0 hh1 h0 hpo' hu hum ha3 hb3 a1 h22 (ne_of_lt h11)
            have := d1 1 zero_le_one (by norm_num)
            linarith
          · have := AgriLA6.C3 hh0 hh1 h0 hpo' hu hum ha3 hb3 a1 a2 h11 h22 hY
            have := d2 1 zero_le_one (by norm_num)
            linarith
      exact ⟨tback _ key.1, tback _ key.2⟩
    · rintro ⟨rfl, rfl⟩
      apply (AgriLA6.eq_iff_G pe po c K U A h H L1 L2 _ _ hK hH hpo').2
      refine ⟨⟨⟨by positivity, hKL1⟩, ⟨by positivity, hKL2⟩⟩, ?_, ?_⟩
      · intro x hx0 _
        rw [tK]
        rcases eq_or_ne (x * H / K) 1 with he | hne
        · rw [he]
        · exact (AgriLA6.A3 hh0 hh1 h0 hpo' hu hum ha3 hb3 (by positivity) le_rfl hne).le
      · intro x hx0 _
        rw [tK]
        rcases eq_or_ne (x * H / K) 1 with he | hne
        · rw [he]
        · exact (AgriLA6.B3 hh0 hh1 h0 hpo' hu hum ha3 hb3 le_rfl (by positivity) hne).le
  · -- part 4
    intro H4
    have h4 : u < h * (1 - h) * (2 * po - m) := by
      rw [eK] at H4
      have key : h * (1 - h) * (m + u / (h * (1 - h))) = h * (1 - h) * m + u := by
        have hne1 : (1 : ℝ) - h ≠ 0 := by linarith
        have hne2 : h * (1 - h) ≠ 0 := ne_of_gt hk
        field_simp <;> ring
      have := mul_lt_mul_of_pos_left H4 hk
      nlinarith
    intro x1 x2
    constructor
    · intro hE
      obtain ⟨a1, a2, d1, d2⟩ := unpack x1 x2 hE
      have k1 : x1 * H / K = 2 := by
        by_contra hne
        have := AgriLA6.D4 hh0 hh1 h0 hpo' hu h4 a1 a2 hne
        have := d1 2 (by norm_num) le_rfl
        linarith
      have k2 : x2 * H / K = 2 := by
        by_contra hne
        have := AgriLA6.E4 hh0 hh1 h0 hpo' hu h4 a1 a2 hne
        have := d2 2 (by norm_num) le_rfl
        linarith
      exact ⟨tback2 _ k1, tback2 _ k2⟩
    · rintro ⟨rfl, rfl⟩
      apply (AgriLA6.eq_iff_G pe po c K U A h H L1 L2 _ _ hK hH hpo').2
      refine ⟨⟨⟨by positivity, hL1⟩, ⟨by positivity, hL2⟩⟩, ?_, ?_⟩
      · intro x hx0 _
        rw [t2K]
        rcases eq_or_ne (x * H / K) 2 with he | hne
        · rw [he]
        · exact (AgriLA6.D4 hh0 hh1 h0 hpo' hu h4 (by positivity) (by norm_num) hne).le
      · intro x hx0 _
        rw [t2K]
        rcases eq_or_ne (x * H / K) 2 with he | hne
        · rw [he]
        · exact (AgriLA6.E4 hh0 hh1 h0 hpo' hu h4 (by norm_num) (by positivity) hne).le
