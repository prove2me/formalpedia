-- Prove2me | solution 1 for AssumptionsOfPhysics.eq_of_mix_eq_right
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-02T20:23:18.286435+00:00
-- url     : https://prove2.me/submissions/990e4863-ba70-492b-9670-31071459485e

import Mathlib
import Definitions.Def_AoP_EnsembleSpaces

open AssumptionsOfPhysics Filter Topology

namespace AoPCancel

variable {I : ℝ → ℝ → ℝ} {E : Type*} [TopologicalSpace E] (X : EnsembleSpace I E)

lemma clampI_coe_val (x : ℝ) : ((clampI x : unitInterval) : ℝ) = max 0 (min 1 x) := by
  simp [clampI, Set.coe_projIcc]

lemma clampI_val {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : ((clampI x : unitInterval) : ℝ) = x := by
  rw [clampI_coe_val, min_eq_right h1, max_eq_right h0]

lemma clampI_coe (q : unitInterval) : clampI (q : ℝ) = q :=
  Subtype.ext (clampI_val q.2.1 q.2.2)

lemma clampI_one_sub (p : ℝ) : clampI (1 - p) = unitInterval.symm (clampI p) := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq, clampI_coe_val, clampI_coe_val]
  rcases le_total p 0 with h | h
  · rw [min_eq_right (by linarith : p ≤ 1), max_eq_left h, min_eq_left (by linarith),
      max_eq_right (by linarith)]; ring
  rcases le_total p 1 with h' | h'
  · rw [min_eq_right h', max_eq_right h, min_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [min_eq_left h', max_eq_right zero_le_one, min_eq_right (by linarith),
      max_eq_left (by linarith)]; ring

lemma continuous_clampI : Continuous clampI := continuous_projIcc (h := zero_le_one)

/-- Mixing with a real coefficient (clamped to `[0,1]`). -/
noncomputable def mixR (p : ℝ) (a b : E) : E := X.mix (clampI p) a b

lemma mixR_coe (q : unitInterval) (a b : E) : mixR X q a b = X.mix q a b := by
  simp [mixR, clampI_coe]

lemma mixR_one (a b : E) : mixR X 1 a b = a := by
  have : clampI 1 = 1 := Subtype.ext (by rw [clampI_val zero_le_one le_rfl]; rfl)
  simp [mixR, this, X.mix_one]

lemma mixR_comm (p : ℝ) (a b : E) : mixR X p a b = mixR X (1 - p) b a := by
  simp only [mixR, clampI_one_sub]; exact X.mix_comm _ a b

lemma mixR_zero (a b : E) : mixR X 0 a b = b := by
  rw [mixR_comm, sub_zero, mixR_one]

lemma mixR_self (p : ℝ) (a : E) : mixR X p a a = a := X.mix_self _ a

/-- Associativity in a convenient form. -/
lemma mixR_assoc {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (x y z : E) :
    mixR X α x (mixR X β y z) =
      mixR X (α + (1 - α) * β) (mixR X (α / (α + (1 - α) * β)) x y) z := by
  rcases eq_or_lt_of_le hα1 with h1 | h1
  · subst h1; simp [mixR_one]
  by_cases h00 : α = 0 ∧ β = 0
  · obtain ⟨rfl, rfl⟩ := h00; simp [mixR_zero]
  have hp3 : (1 - α) * (1 - β) < 1 := by
    rcases not_and_or.mp h00 with h | h
    · have : 0 < α := lt_of_le_of_ne hα0 (Ne.symm h)
      nlinarith
    · have : 0 < β := lt_of_le_of_ne hβ0 (Ne.symm h)
      nlinarith
  have key := X.mix_assoc α ((1 - α) * (1 - β)) x y z hα0 h1
    (mul_nonneg (by linarith) (by linarith)) hp3 (by nlinarith)
  have e1 : (1 - α - (1 - α) * (1 - β)) / (1 - α) = β := by
    field_simp [show (1 - α) ≠ 0 by linarith]; ring
  have e2 : 1 - (1 - α) * (1 - β) = α + (1 - α) * β := by ring
  rw [e1, e2] at key
  exact key

/-- Mixing an ensemble into a mixture containing it. -/
lemma mixR_mixR_left {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (x z : E) : mixR X α x (mixR X β x z) = mixR X (α + (1 - α) * β) x z := by
  rw [mixR_assoc X hα0 hα1 hβ0 hβ1, mixR_self]

lemma continuous_S_mixR (x e : E) : Continuous fun q : ℝ => X.S (mixR X q x e) := by
  unfold mixR
  exact X.continuous_S.comp (X.continuous_mix.comp
    (continuous_clampI.prodMk (continuous_const.prodMk continuous_const)))

lemma eq_at_one_of_seq {φ : ℝ → ℝ} (hφ : Continuous φ) {q : ℕ → ℝ}
    (hq : Tendsto q atTop (𝓝 1)) (h : ∀ n, φ (q n) = 0) : φ 1 = 0 := by
  have h1 : Tendsto (fun n => φ (q n)) atTop (𝓝 (φ 1)) := (hφ.tendsto 1).comp hq
  simp only [h] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds


lemma clampI_half_val : ((clampI (1 / 2) : unitInterval) : ℝ) = 1 / 2 :=
  clampI_val (by norm_num) (by norm_num)

/-! ### Corollary 4.102 -/

theorem eq_of_mix_eq_right' (a b : E) (p : unitInterval) (hp : 0 < (p : ℝ))
    (h : X.mix p a b = b) : a = b := by
  rcases eq_or_lt_of_le p.2.2 with h1 | h1
  · have : p = 1 := Subtype.ext h1
    rw [this, X.mix_one] at h; exact h
  have hR : mixR X p a b = b := by rw [mixR_coe]; exact h
  have hn : ∀ n : ℕ, mixR X (1 - (1 - (p : ℝ)) ^ n) a b = b := by
    intro n
    induction n with
    | zero => simp [mixR_zero]
    | succ n ih =>
      have h0 : 0 ≤ (1 - (p : ℝ)) ^ n := pow_nonneg (by linarith) n
      have h1' : (1 - (p : ℝ)) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have := mixR_mixR_left X hp.le h1.le (by linarith : 0 ≤ 1 - (1 - (p : ℝ)) ^ n)
        (by linarith) a b
      rw [ih, hR] at this
      have e : 1 - (1 - (p : ℝ)) ^ (n + 1) = p + (1 - p) * (1 - (1 - p) ^ n) := by ring
      rw [e]; exact this.symm
  have hlim : Tendsto (fun n : ℕ => 1 - (1 - (p : ℝ)) ^ n) atTop (𝓝 1) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - (p : ℝ))
      (by linarith)).const_sub 1
    simpa using this
  have hS : X.S a - X.S b = 0 := by
    have := eq_at_one_of_seq (φ := fun q => X.S (mixR X q a b) - X.S b)
      ((continuous_S_mixR X a b).sub continuous_const) hlim
      (fun n => by show X.S (mixR X (1 - (1 - (p : ℝ)) ^ n) a b) - X.S b = 0
                   rw [hn n, sub_self])
    simpa [mixR_one] using this
  have hc := X.concave_S p a b hp h1
  apply hc.2.mp
  rw [h]; linear_combination (p : ℝ) * hS

/-! ### Theorem 4.73 -/

/-- One step of the propagation `p ↦ 2p/(1+p)`. -/
lemma step (a b e : E) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (h : mixR X p a e = mixR X p b e) :
    mixR X (2 * p / (1 + p)) (mixR X (1 / 2) a b) e = mixR X (2 * p / (1 + p)) a e := by
  have hs0 : 0 ≤ p / (1 + p) := by positivity
  have hs1 : p / (1 + p) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h1 := mixR_assoc X hs0 hs1 hp0.le hp1 a b e
  have h2 := mixR_mixR_left X hs0 hs1 hp0.le hp1 a e
  have eγ : p / (1 + p) + (1 - p / (1 + p)) * p = 2 * p / (1 + p) := by
    field_simp; ring
  have ehalf : p / (1 + p) / (2 * p / (1 + p)) = 1 / 2 := by
    field_simp
  rw [eγ, ehalf] at h1
  rw [eγ] at h2
  rw [← h1, ← h, h2]

lemma two_mul_div_bounds {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    0 < 2 * p / (1 + p) ∧ 2 * p / (1 + p) ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by linarith)]; linarith

theorem cancellative' (a b e : E) (p : unitInterval) (hp₀ : 0 < (p : ℝ))
    (hp₁ : (p : ℝ) < 1) (h : X.mix p a e = X.mix p b e) : a = b := by
  set c := mixR X (1 / 2) a b with hc
  have hcomm : mixR X (1 / 2) b a = c := by rw [mixR_comm, hc]; norm_num
  let q : ℕ → ℝ := fun n => Nat.rec (p : ℝ) (fun _ x => 2 * x / (1 + x)) n
  have hq0 : q 0 = p := rfl
  have hqs : ∀ n, q (n + 1) = 2 * q n / (1 + q n) := fun n => rfl
  have inv : ∀ n, (p : ℝ) ≤ q n ∧ q n ≤ 1 ∧ mixR X (q n) a e = mixR X (q n) b e ∧
      1 - q n ≤ (1 - p) * (1 / (1 + p)) ^ n := by
    intro n
    induction n with
    | zero => rw [hq0]; exact ⟨le_rfl, hp₁.le, by simpa [mixR_coe] using h, by simp⟩
    | succ n ih =>
      obtain ⟨hpq, hq1, hqe, hqb⟩ := ih
      have hq0' : 0 < q n := lt_of_lt_of_le hp₀ hpq
      have hA := step X a b e hq0' hq1 hqe
      have hB := step X b a e hq0' hq1 hqe.symm
      rw [hcomm] at hB
      rw [hqs]
      obtain ⟨_, hb1⟩ := two_mul_div_bounds hq0' hq1
      refine ⟨?_, hb1, hA.symm.trans hB, ?_⟩
      · rw [le_div_iff₀ (by linarith)]; nlinarith
      · have e1 : 1 - 2 * q n / (1 + q n) = (1 - q n) / (1 + q n) := by
          field_simp; ring
        rw [e1, pow_succ, ← mul_assoc]
        have : (1 - q n) / (1 + q n) ≤ (1 - q n) * (1 / (1 + p)) := by
          rw [div_eq_mul_one_div]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          apply one_div_le_one_div_of_le (by linarith) (by linarith)
        calc (1 - q n) / (1 + q n) ≤ (1 - q n) * (1 / (1 + p)) := this
          _ ≤ _ := mul_le_mul_of_nonneg_right hqb (by positivity)
  have hlim : Tendsto q atTop (𝓝 1) := by
    have hr : Tendsto (fun n : ℕ => (1 - (p : ℝ)) * (1 / (1 + p)) ^ n) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : (0 : ℝ) ≤ 1 / (1 + p))
        (by rw [div_lt_one (by linarith)]; linarith)).const_mul (1 - (p : ℝ))
      simpa using this
    have h0 : Tendsto (fun n => 1 - q n) atTop (𝓝 0) :=
      squeeze_zero (fun n => by linarith [(inv n).2.1]) (fun n => (inv n).2.2.2) hr
    have := h0.const_sub 1
    simpa using this
  have hlim' : Tendsto (fun n => q (n + 1)) atTop (𝓝 1) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hca : ∀ n, mixR X (q (n + 1)) c e = mixR X (q (n + 1)) a e := by
    intro n
    have ⟨hpq, hq1, hqe, _⟩ := inv n
    rw [hqs]; exact step X a b e (lt_of_lt_of_le hp₀ hpq) hq1 hqe
  have hcb : ∀ n, mixR X (q (n + 1)) c e = mixR X (q (n + 1)) b e := fun n =>
    (hca n).trans (inv (n + 1)).2.2.1
  have hSa : X.S c - X.S a = 0 := by
    have := eq_at_one_of_seq (φ := fun r => X.S (mixR X r c e) - X.S (mixR X r a e))
      ((continuous_S_mixR X c e).sub (continuous_S_mixR X a e)) hlim'
      (fun n => by show X.S (mixR X (q (n + 1)) c e) - X.S (mixR X (q (n + 1)) a e) = 0
                   rw [hca n, sub_self])
    simpa [mixR_one] using this
  have hSb : X.S c - X.S b = 0 := by
    have := eq_at_one_of_seq (φ := fun r => X.S (mixR X r c e) - X.S (mixR X r b e))
      ((continuous_S_mixR X c e).sub (continuous_S_mixR X b e)) hlim'
      (fun n => by show X.S (mixR X (q (n + 1)) c e) - X.S (mixR X (q (n + 1)) b e) = 0
                   rw [hcb n, sub_self])
    simpa [mixR_one] using this
  have hc2 := X.concave_S (clampI (1 / 2)) a b (by rw [clampI_half_val]; norm_num)
    (by rw [clampI_half_val]; norm_num)
  apply hc2.2.mp
  have : X.S (X.mix (clampI (1 / 2)) a b) = X.S c := rfl
  rw [this, clampI_half_val]
  linear_combination (-1 / 2 : ℝ) * hSa - (1 / 2 : ℝ) * hSb

/-! ### Proposition 4.116 (items 1, 2, 3, 5) -/

theorem mixingEntropy_properties' :
    (∀ a b : E, 0 ≤ X.mixingEntropy a b) ∧ (∀ a b : E, X.mixingEntropy a b = 0 ↔ a = b) ∧
      (∀ a b : E, X.mixingEntropy a b ≤ I (1 / 2) (1 / 2)) ∧
      (∀ a b : E, X.mixingEntropy a b = X.mixingEntropy b a) := by
  have hh0 : 0 < ((clampI (1 / 2) : unitInterval) : ℝ) := by rw [clampI_half_val]; norm_num
  have hh1 : ((clampI (1 / 2) : unitInterval) : ℝ) < 1 := by rw [clampI_half_val]; norm_num
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a b => ?_⟩
  · have := (X.concave_S _ a b hh0 hh1).1
    rw [clampI_half_val] at this
    unfold EnsembleSpace.mixingEntropy; linarith
  · have := (X.concave_S _ a b hh0 hh1).2
    rw [clampI_half_val] at this
    unfold EnsembleSpace.mixingEntropy
    constructor
    · intro h0; apply this.mp; linarith
    · rintro rfl; rw [X.mix_self]; ring
  · have := X.upper_bound_S (clampI (1 / 2)) a b
    rw [clampI_half_val, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at this
    unfold EnsembleSpace.mixingEntropy; linarith
  · have hs : unitInterval.symm (clampI (1 / 2)) = clampI (1 / 2) := by
      apply Subtype.ext; rw [unitInterval.coe_symm_eq, clampI_half_val]; norm_num
    unfold EnsembleSpace.mixingEntropy
    rw [X.mix_comm (clampI (1 / 2)) a b, hs]; ring

/-! ### Proposition 4.67 -/

lemma I_le_of_orth {a b : E} (h : X.Orth a b) (q : unitInterval) (hq0 : 0 < (q : ℝ))
    (hq1 : (q : ℝ) < 1) : I q (1 - q) ≤ I (1 - q) q := by
  have h1 := h q hq0 hq1
  have h2 := X.upper_bound_S (unitInterval.symm q) b a
  rw [X.mix_comm (unitInterval.symm q) b a, unitInterval.symm_symm, unitInterval.coe_symm_eq,
    sub_sub_cancel] at h2
  linarith

lemma I_symm_of_orth {a b : E} (h : X.Orth a b) (q : unitInterval) (hq0 : 0 < (q : ℝ))
    (hq1 : (q : ℝ) < 1) : I q (1 - q) = I (1 - q) q := by
  have h1 := I_le_of_orth X h q hq0 hq1
  have h2 := I_le_of_orth X h (unitInterval.symm q)
    (by rw [unitInterval.coe_symm_eq]; linarith) (by rw [unitInterval.coe_symm_eq]; linarith)
  rw [unitInterval.coe_symm_eq, sub_sub_cancel] at h2
  linarith

lemma orth_symm {a b : E} (h : X.Orth a b) : X.Orth b a := by
  intro q hq0 hq1
  have hs0 : 0 < ((unitInterval.symm q : unitInterval) : ℝ) := by
    rw [unitInterval.coe_symm_eq]; linarith
  have hs1 : ((unitInterval.symm q : unitInterval) : ℝ) < 1 := by
    rw [unitInterval.coe_symm_eq]; linarith
  have h1 := h _ hs0 hs1
  rw [unitInterval.coe_symm_eq, sub_sub_cancel] at h1
  rw [X.mix_comm q b a, h1, ← I_symm_of_orth X h q hq0 hq1]; ring

lemma orth_irrefl (hI : ∀ p : ℝ, 0 < p → p < 1 → 0 < I p (1 - p)) (a : E) : ¬ X.Orth a a := by
  intro h
  have h1 := h (clampI (1 / 2)) (by rw [clampI_half_val]; norm_num)
    (by rw [clampI_half_val]; norm_num)
  rw [X.mix_self, clampI_half_val] at h1
  have := hI (1 / 2) (by norm_num) (by norm_num)
  linarith

lemma orth_of_component {x y z : E} (h : X.Orth x y) (hz : X.IsComponent z y) :
    X.Orth x z := by
  obtain ⟨p, d, hp, rfl⟩ := hz
  rcases eq_or_lt_of_le p.2.2 with h1 | h1
  · have : p = 1 := Subtype.ext h1
    rw [this, X.mix_one] at h; exact h
  exact ((X.orth_mix_iff p x z d).mpr h hp h1).1

theorem orth_properties' (hI : ∀ p : ℝ, 0 < p → p < 1 → 0 < I p (1 - p)) :
    (∀ a : E, ¬ X.Orth a a) ∧ (∀ a b : E, X.Orth a b ↔ X.Orth b a) ∧
      (∀ a b : E, X.IsComponent b a → ¬ X.Orth a b) ∧
      (∀ a b : E, X.Orth a b → X.Separate a b) := by
  refine ⟨orth_irrefl X hI, fun a b => ⟨orth_symm X, orth_symm X⟩, ?_, ?_⟩
  · intro a b hb hab
    exact orth_irrefl X hI b (orth_of_component X (orth_symm X hab) hb)
  · rintro a b hab ⟨c, hca, hcb⟩
    exact orth_irrefl X hI c (orth_of_component X (orth_symm X (orth_of_component X hab hcb)) hca)

end AoPCancel

theorem solution {I : ℝ → ℝ → ℝ} {E : Type*} [TopologicalSpace E]
    (X : EnsembleSpace I E) (a b : E) (p : unitInterval) (hp : 0 < (p : ℝ))
    (h : X.mix p a b = b) : a = b :=
  AoPCancel.eq_of_mix_eq_right' X a b p hp h
