-- Prove2me | solution 1 for Arxiv0812_1178.canonical_closures_generate
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:50:06.005076+00:00
-- url     : https://prove2.me/submissions/2ae3e047-3436-491d-ad7f-c231cb05a16a

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
namespace Arxiv0812_1178

lemma cc_single {α : Type*} [DecidableEq α] {P : α → Prop} [DecidablePred P] [Fintype {p // P p}]
    (f : {p // P p} → ℝ) (x : α) :
    ∑ c : {p // P p}, (if c.1 = x then (1:ℝ) else 0) * f c = if h : P x then f ⟨x, h⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨x, h⟩]
    · simp
    · intro c _ hc
      have : c.1 ≠ x := fun e => hc (Subtype.ext e)
      simp [this]
    · simp
  · apply Finset.sum_eq_zero
    intro c _
    have : c.1 ≠ x := fun e => h (e ▸ c.2)
    simp [this]

lemma cc_part1 {n : ℕ} (t1 : Fin n) (φ : Fin n → Fin n → ℝ) (hφ : ∀ k l, φ l k = -φ k l)
    (k l m : Fin n) : closurePhase φ k l m =
      closurePhase φ t1 k l + closurePhase φ t1 l m - closurePhase φ t1 k m := by
  unfold closurePhase
  have h1 := hφ t1 l; have h2 := hφ t1 m; have h3 := hφ k m; have h4 := hφ t1 k
  linarith

/-- weight vector for β_{0ab} -/
def ccW {n : ℕ} (a b : Fin n) (c : ClosureIdx n) : ℤ :=
  (if c.1 = (a, b) then 1 else 0) - (if c.1 = (b, a) then 1 else 0)

lemma cc_single' {α : Type*} [DecidableEq α] {P : α → Prop} [DecidablePred P]
    [Fintype {p // P p}] (f : {p // P p} → ℝ) (x : α) (Q : {p // P p} → Prop) [DecidablePred Q]
    (hQ : ∀ c, Q c ↔ c.1 = x) :
    ∑ c : {p // P p}, (if Q c then (1:ℝ) else 0) * f c = if h : P x then f ⟨x, h⟩ else 0 := by
  rw [← cc_single f x]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : Q c
  · rw [if_pos h, if_pos ((hQ c).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((hQ c).2 h'))]

lemma cc_w {n : ℕ} (hn : 3 ≤ n) (φ : Fin n → Fin n → ℝ) (hφ : ∀ k l, φ l k = -φ k l)
    (a b : Fin n) :
    closurePhase φ ⟨0, by omega⟩ a b = ∑ c, (ccW a b c : ℝ) * canonicalClosure φ c := by
  have e : ∀ c : ClosureIdx n, (ccW a b c : ℝ) * canonicalClosure φ c =
      (if c.1 = (a, b) then (1:ℝ) else 0) * canonicalClosure φ c -
      (if c.1 = (b, a) then (1:ℝ) else 0) * canonicalClosure φ c := by
    intro c; unfold ccW; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun c _ => e c), Finset.sum_sub_distrib, cc_single, cc_single]
  have h00 : ∀ x : Fin n, φ x x = 0 := fun x => by have := hφ x x; linarith
  simp only [canonicalClosure, closurePhase]
  by_cases ha : (0 : ℕ) < a.1
  · by_cases hb : (0 : ℕ) < b.1
    · rcases lt_trichotomy a b with hab | hab | hab
      · rw [dif_pos ⟨ha, hab⟩, dif_neg (fun h => absurd h.2 (not_lt.2 hab.le))]
        simp
      · subst hab; simp [h00]; have := hφ ⟨0, by omega⟩ a; linarith
      · rw [dif_neg (fun h => absurd h.2 (not_lt.2 hab.le)), dif_pos ⟨hb, hab⟩]
        have := hφ ⟨0, by omega⟩ a; have := hφ ⟨0, by omega⟩ b; have := hφ a b
        simp; linarith
    · have hb0 : b = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
      rw [hb0]
      rw [dif_neg (fun h => absurd h.2 (by simp [Fin.lt_def])), dif_neg (fun h => by simp at h)]
      simp [h00]; have := hφ ⟨0, by omega⟩ a; linarith
  · have ha0 : a = ⟨0, by omega⟩ := Fin.ext (by simp; omega)
    rw [ha0]
    rw [dif_neg (fun h => by simp at h), dif_neg (fun h => absurd h.2 (by simp [Fin.lt_def]))]
    simp [h00]; have := hφ ⟨0, by omega⟩ b; linarith

theorem canonical_closures_generate {n : ℕ} (hn : 3 ≤ n) (t1 : Fin n) (ht1 : t1.1 = 0) :
    (∀ φ : Fin n → Fin n → ℝ, (∀ k l, φ l k = -φ k l) →
      ∀ k l m : Fin n, closurePhase φ k l m =
        closurePhase φ t1 k l + closurePhase φ t1 l m - closurePhase φ t1 k m) ∧
    (∀ k l m : Fin n, k ≠ l → l ≠ m → k ≠ m →
      ∃ w : ClosureIdx n → ℤ, ∀ φ : Fin n → Fin n → ℝ, (∀ k' l', φ l' k' = -φ k' l') →
        closurePhase φ k l m = ∑ c, (w c : ℝ) * canonicalClosure φ c) ∧
    (∀ φ : Fin n → Fin n → ℝ, (∀ k l, φ l k = -φ k l) →
      closureOp n *ᵥ baselineVec φ = canonicalClosure φ) := by
  have ht : t1 = ⟨0, by omega⟩ := Fin.ext ht1
  refine ⟨fun φ hφ k l m => cc_part1 t1 φ hφ k l m, ?_, ?_⟩
  · intro k l m _ _ _
    refine ⟨fun c => ccW k l c + ccW l m c - ccW k m c, fun φ hφ => ?_⟩
    rw [cc_part1 ⟨0, by omega⟩ φ hφ k l m, cc_w hn φ hφ, cc_w hn φ hφ, cc_w hn φ hφ,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    push_cast; ring
  · intro φ hφ
    funext c
    simp only [Matrix.mulVec, dotProduct, closureOp, baselineVec, add_mul, sub_mul,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have e1 : ∀ b : Baseline n, (b.1.1.1 = 0 ∧ b.1.2 = c.1.1) ↔ b.1 = (⟨0, by omega⟩, c.1.1) := by
      intro b; constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext (Fin.ext h1) h2
      · intro h; rw [h]; exact ⟨rfl, rfl⟩
    have e2 : ∀ b : Baseline n, (b.1.1.1 = 0 ∧ b.1.2 = c.1.2) ↔ b.1 = (⟨0, by omega⟩, c.1.2) := by
      intro b; constructor
      · rintro ⟨h1, h2⟩; exact Prod.ext (Fin.ext h1) h2
      · intro h; rw [h]; exact ⟨rfl, rfl⟩
    rw [cc_single' (P := fun p : Fin n × Fin n => p.1 < p.2) (fun b => φ b.1.1 b.1.2) (⟨0, by omega⟩, c.1.1) _ e1,
      cc_single' (P := fun p : Fin n × Fin n => p.1 < p.2) (fun b => φ b.1.1 b.1.2) (⟨0, by omega⟩, c.1.2) _ e2,
      cc_single' (P := fun p : Fin n × Fin n => p.1 < p.2) (fun b => φ b.1.1 b.1.2) c.1 _
        (fun b => Iff.rfl)]
    have hk : (⟨0, by omega⟩ : Fin n) < c.1.1 := by rw [Fin.lt_def]; exact c.2.1
    have hl : (⟨0, by omega⟩ : Fin n) < c.1.2 := lt_trans hk c.2.2
    rw [dif_pos hk, dif_pos hl, dif_pos c.2.2]
    simp only [canonicalClosure, closurePhase]
    have := hφ ⟨0, by omega⟩ c.1.2
    linarith

end Arxiv0812_1178

open Arxiv0812_1178 in
theorem solution {n : ℕ} (hn : 3 ≤ n) (t1 : Fin n) (ht1 : t1.1 = 0) :
    (∀ φ : Fin n → Fin n → ℝ, (∀ k l, φ l k = -φ k l) →
      ∀ k l m : Fin n, closurePhase φ k l m =
        closurePhase φ t1 k l + closurePhase φ t1 l m - closurePhase φ t1 k m) ∧
    (∀ k l m : Fin n, k ≠ l → l ≠ m → k ≠ m →
      ∃ w : ClosureIdx n → ℤ, ∀ φ : Fin n → Fin n → ℝ, (∀ k' l', φ l' k' = -φ k' l') →
        closurePhase φ k l m = ∑ c, (w c : ℝ) * canonicalClosure φ c) ∧
    (∀ φ : Fin n → Fin n → ℝ, (∀ k l, φ l k = -φ k l) →
      closureOp n *ᵥ baselineVec φ = canonicalClosure φ) :=
  Arxiv0812_1178.canonical_closures_generate hn t1 ht1
