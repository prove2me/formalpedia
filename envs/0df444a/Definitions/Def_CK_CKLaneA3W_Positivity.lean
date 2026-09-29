-- Prove2me | Definitions.Def_CK_CKLaneA3W_Positivity
-- name    : CK_CKLaneA3W_Positivity
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:34:44.043027+00:00
-- url     : https://prove2.me/theorems/85f12231-be13-4a1b-bda5-c736139ea884
-- title:
--   Courtade–Kumar proof module `CKLaneA3W.Positivity` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3W.Positivity` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3W.Positivity` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3W.Positivity (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3W/Positivity.lean)

import Definitions.Def_CK_CKLaneA3W_ExactPoly

/-!
# CKLaneA3W.Positivity — interval box bounds (Horner in t) and the final positivity lemmas
-/

namespace CKLaneA3W

/-- interval for `x^k`, `x ∈ [a, b]`, boxes not straddling 0 handled exactly; straddling handled
crudely but soundly. -/
noncomputable def powI (a b : ℚ) (k : ℕ) : ℚ × ℚ :=
  if 0 ≤ a then (qpow a k, qpow b k)
  else if b ≤ 0 then
    (if k % 2 = 0 then (qpow (-b) k, qpow (-a) k) else (-qpow (-a) k, -qpow (-b) k))
  else (-(qpow (max (-a) b) k), qpow (max (-a) b) k)

theorem powI_spec {a b : ℚ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) (k : ℕ) :
    ((powI a b k).1 : ℝ) ≤ x ^ k ∧ x ^ k ≤ ((powI a b k).2 : ℝ) := by
  unfold powI
  split_ifs with h1 h2 h3
  · have h1' : (0 : ℝ) ≤ a := by exact_mod_cast h1
    simp only [qpow_eq]; push_cast
    exact ⟨pow_le_pow_left₀ h1' ha k, pow_le_pow_left₀ (h1'.trans ha) hb k⟩
  · have h2' : (b : ℝ) ≤ 0 := by exact_mod_cast h2
    have hx0 : 0 ≤ -x := by linarith
    have e : x ^ k = (-x) ^ k := by
      rw [neg_pow]; have : Even k := Nat.even_iff.mpr h3; rw [this.neg_one_pow, one_mul]
    simp only [qpow_eq]; push_cast
    rw [e]
    exact ⟨pow_le_pow_left₀ (by linarith) (by linarith) k, pow_le_pow_left₀ hx0 (by linarith) k⟩
  · have h2' : (b : ℝ) ≤ 0 := by exact_mod_cast h2
    have hx0 : 0 ≤ -x := by linarith
    have hodd : Odd k := Nat.odd_iff.mpr (by omega)
    have e : x ^ k = -((-x) ^ k) := by rw [hodd.neg_pow]; ring
    simp only [qpow_eq]; push_cast
    rw [e]
    constructor
    · exact neg_le_neg (pow_le_pow_left₀ hx0 (by linarith) k)
    · exact neg_le_neg (pow_le_pow_left₀ (by linarith) (by linarith) k)
  · have hm : |x| ≤ ((max (-a) b : ℚ) : ℝ) := by
      rw [abs_le]; push_cast
      constructor
      · have := le_max_left (-(a : ℝ)) (b : ℝ); linarith
      · have := le_max_right (-(a : ℝ)) (b : ℝ); linarith
    have hp : |x ^ k| ≤ ((max (-a) b : ℚ) : ℝ) ^ k := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hm k
    simp only [qpow_eq]; push_cast at hp ⊢
    exact ⟨by have := neg_abs_le (x ^ k); linarith, (le_abs_self _).trans hp⟩

noncomputable def mulI (x y : ℚ × ℚ) : ℚ × ℚ :=
  (min (min (x.1 * y.1) (x.1 * y.2)) (min (x.2 * y.1) (x.2 * y.2)),
   max (max (x.1 * y.1) (x.1 * y.2)) (max (x.2 * y.1) (x.2 * y.2)))

theorem mulI_spec {x y : ℚ × ℚ} {u v : ℝ} (hu1 : (x.1 : ℝ) ≤ u) (hu2 : u ≤ (x.2 : ℝ))
    (hv1 : (y.1 : ℝ) ≤ v) (hv2 : v ≤ (y.2 : ℝ)) :
    ((mulI x y).1 : ℝ) ≤ u * v ∧ u * v ≤ ((mulI x y).2 : ℝ) := by
  unfold mulI
  push_cast
  constructor
  · rcases le_total 0 v with hv | hv
    · have h1 : (x.1 : ℝ) * v ≤ u * v := mul_le_mul_of_nonneg_right hu1 hv
      rcases le_total 0 (x.1 : ℝ) with hx | hx
      · have : (x.1 : ℝ) * y.1 ≤ x.1 * v := mul_le_mul_of_nonneg_left hv1 hx
        have := min_le_left ((x.1 : ℝ) * y.1) (x.1 * y.2)
        have := min_le_left (min ((x.1 : ℝ) * y.1) (x.1 * y.2)) (min ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith
      · have : (x.1 : ℝ) * y.2 ≤ x.1 * v := mul_le_mul_of_nonpos_left hv2 hx
        have := min_le_right ((x.1 : ℝ) * y.1) (x.1 * y.2)
        have := min_le_left (min ((x.1 : ℝ) * y.1) (x.1 * y.2)) (min ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith
    · have h1 : (x.2 : ℝ) * v ≤ u * v := mul_le_mul_of_nonpos_right hu2 hv
      rcases le_total 0 (x.2 : ℝ) with hx | hx
      · have : (x.2 : ℝ) * y.1 ≤ x.2 * v := mul_le_mul_of_nonneg_left hv1 hx
        have := min_le_left ((x.2 : ℝ) * y.1) (x.2 * y.2)
        have := min_le_right (min ((x.1 : ℝ) * y.1) (x.1 * y.2)) (min ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith
      · have : (x.2 : ℝ) * y.2 ≤ x.2 * v := mul_le_mul_of_nonpos_left hv2 hx
        have := min_le_right ((x.2 : ℝ) * y.1) (x.2 * y.2)
        have := min_le_right (min ((x.1 : ℝ) * y.1) (x.1 * y.2)) (min ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith
  · rcases le_total 0 v with hv | hv
    · have h1 : u * v ≤ (x.2 : ℝ) * v := mul_le_mul_of_nonneg_right hu2 hv
      rcases le_total 0 (x.2 : ℝ) with hx | hx
      · have : (x.2 : ℝ) * v ≤ x.2 * y.2 := mul_le_mul_of_nonneg_left hv2 hx
        have := le_max_right ((x.2 : ℝ) * y.1) (x.2 * y.2)
        have := le_max_right (max ((x.1 : ℝ) * y.1) (x.1 * y.2)) (max ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith
      · have : (x.2 : ℝ) * v ≤ x.2 * y.1 := mul_le_mul_of_nonpos_left hv1 hx
        have := le_max_left ((x.2 : ℝ) * y.1) (x.2 * y.2)
        have := le_max_right (max ((x.1 : ℝ) * y.1) (x.1 * y.2)) (max ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith
    · have h1 : u * v ≤ (x.1 : ℝ) * v := mul_le_mul_of_nonpos_right hu1 hv
      rcases le_total 0 (x.1 : ℝ) with hx | hx
      · have : (x.1 : ℝ) * v ≤ x.1 * y.2 := mul_le_mul_of_nonneg_left hv2 hx
        have := le_max_right ((x.1 : ℝ) * y.1) (x.1 * y.2)
        have := le_max_left (max ((x.1 : ℝ) * y.1) (x.1 * y.2)) (max ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith
      · have : (x.1 : ℝ) * v ≤ x.1 * y.1 := mul_le_mul_of_nonpos_left hv1 hx
        have := le_max_left ((x.1 : ℝ) * y.1) (x.1 * y.2)
        have := le_max_left (max ((x.1 : ℝ) * y.1) (x.1 * y.2)) (max ((x.2 : ℝ) * y.1) (x.2 * y.2))
        linarith

noncomputable def sBox (a b : ℚ) (s : SPoly) : ℚ × ℚ :=
  @List.rec (ℕ × LPoly) (fun _ => ℚ × ℚ) (0, 0)
    (fun m _ ih => ((mulI (LPoly.intv m.2) (powI a b m.1)).1 + ih.1,
                    (mulI (LPoly.intv m.2) (powI a b m.1)).2 + ih.2)) s

theorem sBox_spec {a b : ℚ} {σ : ℝ} (ha : (a : ℝ) ≤ σ) (hb : σ ≤ (b : ℝ)) (s : SPoly) :
    ((sBox a b s).1 : ℝ) ≤ SPoly.eval σ (Real.log 2) s ∧
      SPoly.eval σ (Real.log 2) s ≤ ((sBox a b s).2 : ℝ) := by
  induction s with
  | nil => simp [sBox, SPoly.eval_nil]
  | cons m s ih =>
    obtain ⟨l1, l2⟩ := LPoly.intv_spec log2_lo log2_hi m.2
    obtain ⟨p1, p2⟩ := powI_spec ha hb m.1
    obtain ⟨q1, q2⟩ := mulI_spec p1 p2 l1 l2
    show (((mulI (LPoly.intv m.2) (powI a b m.1)).1 + (sBox a b s).1 : ℚ) : ℝ) ≤ _ ∧
      _ ≤ (((mulI (LPoly.intv m.2) (powI a b m.1)).2 + (sBox a b s).2 : ℚ) : ℝ)
    rw [SPoly.eval_cons]
    have hm1 : ((mulI (LPoly.intv m.2) (powI a b m.1)).1 : ℝ) ≤ σ ^ m.1 * LPoly.eval (Real.log 2) m.2 := by
      obtain ⟨r1, _⟩ := mulI_spec (x := LPoly.intv m.2) (y := powI a b m.1) l1 l2 p1 p2
      linarith [mul_comm (σ ^ m.1) (LPoly.eval (Real.log 2) m.2)]
    have hm2 : σ ^ m.1 * LPoly.eval (Real.log 2) m.2 ≤ ((mulI (LPoly.intv m.2) (powI a b m.1)).2 : ℝ) := by
      obtain ⟨_, r2⟩ := mulI_spec (x := LPoly.intv m.2) (y := powI a b m.1) l1 l2 p1 p2
      linarith [mul_comm (σ ^ m.1) (LPoly.eval (Real.log 2) m.2)]
    push_cast
    exact ⟨add_le_add hm1 ih.1, add_le_add hm2 ih.2⟩

noncomputable def tBox (t0 t1 a b : ℚ) (P : TPoly) : ℚ × ℚ :=
  @List.rec SPoly (fun _ => ℚ × ℚ) (0, 0)
    (fun s _ ih => ((sBox a b s).1 + (mulI (t0, t1) ih).1, (sBox a b s).2 + (mulI (t0, t1) ih).2)) P

theorem tBox_spec {t0 t1 a b : ℚ} {t σ : ℝ} (ht0 : (t0 : ℝ) ≤ t) (ht1 : t ≤ (t1 : ℝ))
    (ha : (a : ℝ) ≤ σ) (hb : σ ≤ (b : ℝ)) (P : TPoly) :
    ((tBox t0 t1 a b P).1 : ℝ) ≤ TPoly.eval t σ (Real.log 2) P ∧
      TPoly.eval t σ (Real.log 2) P ≤ ((tBox t0 t1 a b P).2 : ℝ) := by
  induction P with
  | nil => simp [tBox, TPoly.eval_nil]
  | cons s P ih =>
    obtain ⟨s1, s2⟩ := sBox_spec ha hb s
    obtain ⟨m1, m2⟩ := mulI_spec (x := (t0, t1)) (y := tBox t0 t1 a b P) ht0 ht1 ih.1 ih.2
    show (((sBox a b s).1 + (mulI (t0, t1) (tBox t0 t1 a b P)).1 : ℚ) : ℝ) ≤ _ ∧
      _ ≤ (((sBox a b s).2 + (mulI (t0, t1) (tBox t0 t1 a b P)).2 : ℚ) : ℝ)
    rw [TPoly.eval_cons]
    push_cast
    exact ⟨add_le_add s1 m1, add_le_add s2 m2⟩

/-! ## uniform box covers of σ ∈ [-1/2, 1/2] -/

noncomputable def allBoxes (f : ℚ → ℚ → Bool) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => ih && f (-1 / 2 + (j : ℚ) / m) (-1 / 2 + ((j : ℚ) + 1) / m)) m

theorem allBoxes_aux (f : ℚ → ℚ → Bool) (m k : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true
      (fun j ih => ih && f (-1 / 2 + (j : ℚ) / m) (-1 / 2 + ((j : ℚ) + 1) / m)) k = true) :
    ∀ j < k, f (-1 / 2 + (j : ℚ) / m) (-1 / 2 + ((j : ℚ) + 1) / m) = true := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    have h' : Nat.rec (motive := fun _ => Bool) true
        (fun j ih => ih && f (-1 / 2 + (j : ℚ) / m) (-1 / 2 + ((j : ℚ) + 1) / m)) k = true ∧
        f (-1 / 2 + (k : ℚ) / m) (-1 / 2 + ((k : ℚ) + 1) / m) = true := by
      simpa using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact ih h'.1 j hj'
    · rw [hj']; exact h'.2

theorem allBoxes_cover (f : ℚ → ℚ → Bool) (m : ℕ) (hm : 0 < m) (h : allBoxes f m = true)
    {σ : ℝ} (hσ : |σ| ≤ 1 / 2) :
    ∃ a b : ℚ, f a b = true ∧ (a : ℝ) ≤ σ ∧ σ ≤ (b : ℝ) := by
  have hall := allBoxes_aux f m m h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hlo, hhi⟩ := abs_le.mp hσ
  set y : ℝ := (σ + 1 / 2) * m with hy
  have hy0 : 0 ≤ y := by rw [hy]; exact mul_nonneg (by linarith) hm'.le
  let j : ℕ := min (⌊y⌋₊) (m - 1)
  have hj : j < m := by omega
  refine ⟨-1 / 2 + (j : ℚ) / m, -1 / 2 + ((j : ℚ) + 1) / m, hall j hj, ?_, ?_⟩
  · push_cast
    have h1 : (j : ℝ) ≤ (σ + 1 / 2) * m := by
      have : (j : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      exact this.trans (Nat.floor_le hy0)
    have h1' : (j : ℝ) / m ≤ σ + 1 / 2 := by rw [div_le_iff₀ hm']; linarith
    linarith
  · push_cast
    have h2 : (σ + 1 / 2) * m ≤ (j : ℝ) + 1 := by
      by_cases hc : ⌊y⌋₊ ≤ m - 1
      · have : j = ⌊y⌋₊ := min_eq_left hc
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · push Not at hc
        have hj' : j = m - 1 := min_eq_right hc.le
        rw [hj']
        have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; nlinarith
    have h2' : σ + 1 / 2 ≤ ((j : ℝ) + 1) / m := by rw [le_div_iff₀ hm']; linarith
    linarith

end CKLaneA3W


