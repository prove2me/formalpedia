-- Prove2me | solution 1 for AffinePolicies.TwoGap.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:36:46.582087+00:00
-- url     : https://prove2.me/submissions/6baab954-655f-4834-a5bf-17717130ec82

import Mathlib
import Definitions.Def_AffinePolicies_TwoGap_Setting



namespace AffinePolicies.TwoGap

open Matrix

def VS (m : ℕ) : Set (Fin m → ℝ) :=
  {0} ∪ Set.range (fun j : Fin m => (Pi.single j (1 : ℝ) : Fin m → ℝ)) ∪ {bLow m, bHigh m}

lemma U6_eq (m : ℕ) : U6 m = convexHull ℝ (VS m) := rfl

def Good (m : ℕ) (σ : Equiv.Perm (Fin m)) : Prop := ∀ b : Fin m → ℝ, b ∈ U6 m ↔ b ∘ σ ∈ U6 m

lemma mem_pre {m : ℕ} (σ : Equiv.Perm (Fin m)) (h1 : ∀ s ∈ VS m, s ∘ σ ∈ VS m)
    {b : Fin m → ℝ} (hb : b ∈ U6 m) : b ∘ σ ∈ U6 m := by
  have hc : Convex ℝ ((LinearMap.funLeft ℝ ℝ (σ : Fin m → Fin m)) ⁻¹' (U6 m)) := by
    rw [U6_eq]; exact (convex_convexHull ℝ _).linear_preimage _
  have hsub : VS m ⊆ (LinearMap.funLeft ℝ ℝ (σ : Fin m → Fin m)) ⁻¹' (U6 m) := by
    intro s hs
    rw [U6_eq]
    exact subset_convexHull ℝ _ (h1 s hs)
  have := convexHull_min hsub hc
  rw [← U6_eq] at this
  exact this hb

lemma good_of_vert {m : ℕ} (σ : Equiv.Perm (Fin m)) (h1 : ∀ s ∈ VS m, s ∘ σ ∈ VS m)
    (h2 : ∀ s ∈ VS m, s ∘ (⇑σ⁻¹) ∈ VS m) : Good m σ := by
  intro b
  constructor
  · exact mem_pre σ h1
  · intro h
    have := mem_pre σ⁻¹ h2 h
    have e : (b ∘ σ) ∘ (⇑σ⁻¹) = b := by
      funext k; simp
    rwa [e] at this

lemma Good_mul {m : ℕ} {σ τ : Equiv.Perm (Fin m)} (h1 : Good m σ) (h2 : Good m τ) :
    Good m (σ * τ) := by
  intro b
  rw [h1 b, h2 (b ∘ σ)]
  rfl

lemma Good_inv {m : ℕ} {σ : Equiv.Perm (Fin m)} (h1 : Good m σ) : Good m σ⁻¹ := by
  intro b
  rw [h1 (b ∘ (⇑σ⁻¹))]
  have e : (b ∘ (⇑σ⁻¹)) ∘ σ = b := by
    funext k; simp
  rw [e]

lemma Good_one {m : ℕ} : Good m (1 : Equiv.Perm (Fin m)) := by
  intro b; rfl

lemma single_comp {m : ℕ} (σ : Equiv.Perm (Fin m)) (k : Fin m) :
    (Pi.single k (1:ℝ) : Fin m → ℝ) ∘ σ = Pi.single (σ⁻¹ k) 1 := by
  funext l
  simp only [Function.comp, Pi.single_apply]
  have : σ l = k ↔ l = σ⁻¹ k := by
    rw [Equiv.Perm.inv_def]; exact (Equiv.eq_symm_apply σ).symm
  simp only [this]

lemma good_block {m : ℕ} (σ : Equiv.Perm (Fin m)) (hinv : σ⁻¹ = σ)
    (hblk : ∀ l : Fin m, ((σ l : Fin m) : ℕ) < m / 2 ↔ (l : ℕ) < m / 2) : Good m σ := by
  have h1 : ∀ s ∈ VS m, s ∘ σ ∈ VS m := by
    intro s hs
    rcases hs with (hs | hs) | hs
    · left; left
      have : s = 0 := hs
      subst this; rfl
    · left; right
      obtain ⟨k, rfl⟩ := hs
      refine ⟨σ⁻¹ k, ?_⟩
      exact (single_comp σ k).symm
    · right
      rcases hs with hs | hs
      · have : s = bLow m := hs
        subst this
        have : bLow m ∘ σ = bLow m := by
          funext l; simp only [Function.comp, bLow, hblk]
        rw [this]; exact Or.inl rfl
      · have : s = bHigh m := hs
        subst this
        have : bHigh m ∘ σ = bHigh m := by
          funext l; simp only [Function.comp, bHigh]
          have := hblk l
          simp only [← not_lt, this]
        rw [this]; exact Or.inr rfl
  refine good_of_vert σ h1 ?_
  rw [hinv]; exact h1

lemma good_flip {m : ℕ} (σ : Equiv.Perm (Fin m)) (hinv : σ⁻¹ = σ)
    (hblk : ∀ l : Fin m, ((σ l : Fin m) : ℕ) < m / 2 ↔ ¬ (l : ℕ) < m / 2) : Good m σ := by
  have h1 : ∀ s ∈ VS m, s ∘ σ ∈ VS m := by
    intro s hs
    rcases hs with (hs | hs) | hs
    · left; left
      have : s = 0 := hs
      subst this; rfl
    · left; right
      obtain ⟨k, rfl⟩ := hs
      refine ⟨σ⁻¹ k, ?_⟩
      exact (single_comp σ k).symm
    · right
      rcases hs with hs | hs
      · have : s = bLow m := hs
        subst this
        have : bLow m ∘ σ = bHigh m := by
          funext l; simp only [Function.comp, bLow, bHigh, hblk, not_lt]
        rw [this]; exact Or.inr rfl
      · have : s = bHigh m := hs
        subst this
        have : bHigh m ∘ σ = bLow m := by
          funext l; simp only [Function.comp, bLow, bHigh]
          have := hblk l
          simp only [← not_lt, this]
          simp
        rw [this]; exact Or.inl rfl
  refine good_of_vert σ h1 ?_
  rw [hinv]; exact h1

lemma good_swap {m : ℕ} (i j : Fin m) (h : (i : ℕ) < m / 2 ↔ (j : ℕ) < m / 2) :
    Good m (Equiv.swap i j) := by
  refine good_block _ (Equiv.swap_inv i j) ?_
  intro l
  by_cases hl : l = i
  · subst hl; simp [h]
  · by_cases hl2 : l = j
    · subst hl2; simp [h]
    · rw [Equiv.swap_apply_of_ne_of_ne hl hl2]

def rotE (n : ℕ) : Equiv.Perm (Fin (n + n)) where
  toFun k := ⟨if (k : ℕ) < n then k + n else k - n, by
    have := k.2; split_ifs <;> omega⟩
  invFun k := ⟨if (k : ℕ) < n then k + n else k - n, by
    have := k.2; split_ifs <;> omega⟩
  left_inv k := by
    have := k.2
    apply Fin.ext; simp only; split_ifs <;> omega
  right_inv k := by
    have := k.2
    apply Fin.ext; simp only; split_ifs <;> omega

lemma good_rot (n : ℕ) : Good (n + n) (rotE n) := by
  have hinv : (rotE n)⁻¹ = rotE n := by
    ext k
    have := k.2
    simp only [Equiv.Perm.inv_def, rotE, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  refine good_flip _ hinv ?_
  intro l
  have := l.2
  simp only [rotE, Equiv.coe_fn_mk]
  split_ifs <;> simp <;> omega

lemma good_trans (n : ℕ) (i j : Fin (n + n)) : ∃ τ : Equiv.Perm (Fin (n + n)), Good (n + n) τ ∧ τ i = j := by
  by_cases h : (i : ℕ) < (n + n) / 2 ↔ (j : ℕ) < (n + n) / 2
  · exact ⟨Equiv.swap i j, good_swap i j h, Equiv.swap_apply_left i j⟩
  · refine ⟨Equiv.swap (rotE n i) j * rotE n, Good_mul (good_swap _ _ ?_) (good_rot n), ?_⟩
    · have := i.2; have := j.2
      simp only [rotE, Equiv.coe_fn_mk]
      split_ifs <;> omega
    · simp


def FeasA (m : ℕ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) : Prop :=
  ∀ b ∈ U6 m, 0 ≤ P *ᵥ b + q ∧ b ≤ B6 m *ᵥ (P *ᵥ b + q)

def CostA (m : ℕ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (t : ℝ) : Prop :=
  ∀ b ∈ U6 m, d6 m ⬝ᵥ (P *ᵥ b + q) ≤ t

lemma d6_dot (m : ℕ) (v : Fin m → ℝ) : d6 m ⬝ᵥ v = ∑ i, v i := by
  simp [d6, dotProduct]

open Classical in
noncomputable def Gs (m : ℕ) : Finset (Equiv.Perm (Fin m)) := Finset.univ.filter (fun σ => Good m σ)

lemma mem_Gs {m : ℕ} {σ : Equiv.Perm (Fin m)} : σ ∈ Gs m ↔ Good m σ := by
  simp [Gs]

def pσ {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (σ : Equiv.Perm (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i k => P (σ⁻¹ i) (σ⁻¹ k)

def qσ {m : ℕ} (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) : Fin m → ℝ := fun i => q (σ⁻¹ i)

lemma pσ_eq {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (b : Fin m → ℝ) :
    pσ P σ *ᵥ b + qσ q σ = fun i => (P *ᵥ (b ∘ σ) + q) (σ⁻¹ i) := by
  funext i
  simp only [pσ, qσ, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp]
  congr 1
  rw [← Equiv.sum_comp σ (fun k => P (σ⁻¹ i) (σ⁻¹ k) * b k)]
  simp

lemma B6_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (a c : Fin m) : B6 m (σ a) (σ c) = B6 m a c := by
  simp [B6, σ.injective.eq_iff]

lemma B6_mulVec_perm {m : ℕ} (σ : Equiv.Perm (Fin m)) (w : Fin m → ℝ) :
    B6 m *ᵥ (fun i => w (σ⁻¹ i)) = fun i => (B6 m *ᵥ w) (σ⁻¹ i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h2 : B6 m i (σ k) = B6 m (σ⁻¹ i) k := by
    simpa using B6_perm σ (σ⁻¹ i) k
  rw [h2]
  simp

lemma trans_feas {m : ℕ} {P : Matrix (Fin m) (Fin m) ℝ} {q : Fin m → ℝ} (hF : FeasA m P q)
    {σ : Equiv.Perm (Fin m)} (hσ : Good m σ) {b : Fin m → ℝ} (hb : b ∈ U6 m) :
    0 ≤ pσ P σ *ᵥ b + qσ q σ ∧ b ≤ B6 m *ᵥ (pσ P σ *ᵥ b + qσ q σ) := by
  have hbσ : b ∘ σ ∈ U6 m := (hσ b).1 hb
  obtain ⟨h0, h1⟩ := hF _ hbσ
  rw [pσ_eq, B6_mulVec_perm]
  refine ⟨fun i => h0 (σ⁻¹ i), fun i => ?_⟩
  have := h1 (σ⁻¹ i)
  simpa using this

lemma sym_avg {m : ℕ} (htr : ∀ i j : Fin m, ∃ τ : Equiv.Perm (Fin m), Good m τ ∧ τ i = j)
    (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (hF : FeasA m P q) :
    ∃ (P1 : Matrix (Fin m) (Fin m) ℝ) (q1 : Fin m → ℝ), FeasA m P1 q1 ∧
      (∀ t, CostA m P q t → CostA m P1 q1 t) ∧ ∀ i j, q1 i = q1 j := by
  have hid : (1 : Equiv.Perm (Fin m)) ∈ Gs m := mem_Gs.2 Good_one
  have hcpos : (0 : ℝ) < ((Gs m).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨_, hid⟩
  set c : ℝ := ((Gs m).card : ℝ) with hc
  refine ⟨c⁻¹ • ∑ σ ∈ Gs m, pσ P σ, c⁻¹ • ∑ σ ∈ Gs m, qσ q σ, ?_, ?_, ?_⟩
  · have hval : ∀ b : Fin m → ℝ, (c⁻¹ • ∑ σ ∈ Gs m, pσ P σ) *ᵥ b + c⁻¹ • ∑ σ ∈ Gs m, qσ q σ
        = c⁻¹ • ∑ σ ∈ Gs m, (pσ P σ *ᵥ b + qσ q σ) := by
      intro b
      rw [Matrix.smul_mulVec, Matrix.sum_mulVec, Finset.sum_add_distrib, smul_add]
    intro b hb
    simp only [hval]
    refine ⟨?_, ?_⟩
    · refine smul_nonneg (inv_nonneg.2 hcpos.le) (Finset.sum_nonneg fun σ hσ => ?_)
      exact (trans_feas hF (mem_Gs.1 hσ) hb).1
    · rw [Matrix.mulVec_smul, Matrix.mulVec_sum]
      have hb' : b = c⁻¹ • ∑ σ ∈ Gs m, b := by
        rw [Finset.sum_const, hc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcpos.ne', one_smul]
      conv_lhs => rw [hb']
      exact smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun σ hσ =>
        (trans_feas hF (mem_Gs.1 hσ) hb).2) (inv_nonneg.2 hcpos.le)
  · intro t ht b hb
    have hval : (c⁻¹ • ∑ σ ∈ Gs m, pσ P σ) *ᵥ b + c⁻¹ • ∑ σ ∈ Gs m, qσ q σ
        = c⁻¹ • ∑ σ ∈ Gs m, (pσ P σ *ᵥ b + qσ q σ) := by
      rw [Matrix.smul_mulVec, Matrix.sum_mulVec, Finset.sum_add_distrib, smul_add]
    rw [hval, d6_dot]
    have hs : ∀ σ ∈ Gs m, ∑ i, (pσ P σ *ᵥ b + qσ q σ) i ≤ t := by
      intro σ hσ
      rw [pσ_eq]
      have := ht (b ∘ σ) ((mem_Gs.1 hσ b).1 hb)
      rw [d6_dot] at this
      calc ∑ i, (P *ᵥ (b ∘ σ) + q) (σ⁻¹ i) = ∑ i, (P *ᵥ (b ∘ σ) + q) i :=
            Equiv.sum_comp σ⁻¹ (fun i => (P *ᵥ (b ∘ σ) + q) i)
        _ ≤ t := this
    have e : ∑ i, (c⁻¹ • ∑ σ ∈ Gs m, (pσ P σ *ᵥ b + qσ q σ)) i
        = c⁻¹ * ∑ σ ∈ Gs m, ∑ i, (pσ P σ *ᵥ b + qσ q σ) i := by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ← Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [e]
    calc c⁻¹ * ∑ σ ∈ Gs m, ∑ i, (pσ P σ *ᵥ b + qσ q σ) i
        ≤ c⁻¹ * ∑ σ ∈ Gs m, t := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum hs) (inv_nonneg.2 hcpos.le)
      _ = t := by
          rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcpos.ne', one_mul]
  · intro i j
    obtain ⟨τ, hτ, hτi⟩ := htr i j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, qσ]
    congr 1
    refine Finset.sum_equiv (Equiv.mulLeft τ) ?_ ?_
    · intro ρ
      rw [mem_Gs, mem_Gs]
      constructor
      · intro h; exact Good_mul hτ h
      · intro h
        have := Good_mul (Good_inv hτ) h
        simpa using this
    · intro ρ _
      simp only [Equiv.coe_mulLeft]
      have h3 : τ⁻¹ j = i := by rw [← hτi]; simp
      have h4 : ((τ * ρ)⁻¹) j = ρ⁻¹ i := by
        rw [_root_.mul_inv_rev, Equiv.Perm.mul_apply, h3]
      rw [h4]


abbrev EE (m : ℕ) := (Fin m → Fin m → ℝ) × (Fin m → ℝ)

def yv {m : ℕ} (e : EE m) (b : Fin m → ℝ) : Fin m → ℝ := Matrix.of e.1 *ᵥ b + e.2

lemma yv_apply {m : ℕ} (e : EE m) (b : Fin m → ℝ) (i : Fin m) :
    yv e b i = ∑ j, e.1 i j * b j + e.2 i := by
  simp [yv, Matrix.mulVec, dotProduct]

lemma yv_comb {m : ℕ} (e : EE m) (x y : Fin m → ℝ) (a c : ℝ) (hac : a + c = 1) :
    yv e (a • x + c • y) = a • yv e x + c • yv e y := by
  funext i
  simp only [yv_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ j, e.1 i j * (a * x j) = a * ∑ j, e.1 i j * x j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∑ j, e.1 i j * (c * y j) = c * ∑ j, e.1 i j * y j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  have : e.2 i = a * e.2 i + c * e.2 i := by rw [← add_mul, hac, one_mul]
  nlinarith [this]

lemma b_le_one {m : ℕ} (hm : 0 < m) {b : Fin m → ℝ} (hb : b ∈ U6 m) (i : Fin m) : b i ≤ 1 := by
  have hs : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm)
  have hc : Convex ℝ {b : Fin m → ℝ | ∀ i, b i ≤ 1} := by
    intro x hx y hy a c ha hc hac i
    have h1 := hx i
    have h2 := hy i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hc]
  have hsub : VS m ⊆ {b : Fin m → ℝ | ∀ i, b i ≤ 1} := by
    intro s hs' i
    rcases hs' with (hs' | hs') | hs'
    · have : s = 0 := hs'
      subst this; simp
    · obtain ⟨k, rfl⟩ := hs'
      simp only [Pi.single_apply]; split_ifs <;> norm_num
    · rcases hs' with hs' | hs'
      · have : s = bLow m := hs'
        subst this
        simp only [bLow]
        split_ifs
        · rw [div_le_one (by linarith)]; exact hs
        · norm_num
      · have : s = bHigh m := hs'
        subst this
        simp only [bHigh]
        split_ifs
        · rw [div_le_one (by linarith)]; exact hs
        · norm_num
  have := convexHull_min hsub hc
  exact this hb i

open Classical in
noncomputable def Vf (m : ℕ) : Finset (Fin m → ℝ) :=
  insert 0 (insert (bLow m) (insert (bHigh m)
    (Finset.univ.image (fun j : Fin m => (Pi.single j (1:ℝ) : Fin m → ℝ)))))

lemma mem_Vf {m : ℕ} {v : Fin m → ℝ} : v ∈ Vf m ↔ v ∈ VS m := by
  classical
  simp only [Vf, VS, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_union, Set.mem_singleton_iff, Set.mem_range, Set.mem_insert_iff]
  tauto

lemma cost_hull {m : ℕ} (e : EE m) (t : ℝ) (h : ∀ v ∈ VS m, ∑ i, yv e v i ≤ t) :
    ∀ b ∈ U6 m, ∑ i, yv e b i ≤ t := by
  have hc : Convex ℝ {b : Fin m → ℝ | ∑ i, yv e b i ≤ t} := by
    intro x hx y hy a c ha hc hac
    simp only [Set.mem_setOf_eq] at *
    rw [yv_comb e x y a c hac]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : a * t + c * t = t := by rw [← add_mul, hac, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hc]
  intro b hb
  have := convexHull_min (s := VS m) (fun v hv => h v hv) hc
  exact this hb

def KK (m : ℕ) : Set (EE m) :=
  {e | ∀ b ∈ U6 m, 0 ≤ yv e b ∧ b ≤ B6 m *ᵥ yv e b ∧ ∑ i, yv e b i ≤ m}

lemma mem_KK {m : ℕ} {e : EE m} :
    e ∈ KK m ↔ FeasA m (Matrix.of e.1) e.2 ∧ CostA m (Matrix.of e.1) e.2 m := by
  simp only [KK, FeasA, CostA, Set.mem_setOf_eq, d6_dot]
  constructor
  · intro h
    exact ⟨fun b hb => ⟨(h b hb).1, (h b hb).2.1⟩, fun b hb => (h b hb).2.2⟩
  · rintro ⟨h1, h2⟩ b hb
    exact ⟨(h1 b hb).1, (h1 b hb).2, h2 b hb⟩

lemma yv_cont {m : ℕ} (b : Fin m → ℝ) (i : Fin m) : Continuous fun e : EE m => yv e b i := by
  simp only [yv_apply]
  fun_prop

lemma KK_closed {m : ℕ} : IsClosed (KK m) := by
  have h : KK m = ⋂ b ∈ U6 m, ({e : EE m | 0 ≤ yv e b} ∩ {e | b ≤ B6 m *ᵥ yv e b} ∩
      {e | ∑ i, yv e b i ≤ m}) := by
    ext e; simp only [KK, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff, and_assoc]
  rw [h]
  refine isClosed_biInter fun b hb => ?_
  have hc1 : Continuous fun e : EE m => yv e b := continuous_pi fun i => yv_cont b i
  have hc2 : Continuous fun e : EE m => B6 m *ᵥ yv e b := by
    refine continuous_pi fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact continuous_finset_sum _ fun k _ => continuous_const.mul (yv_cont b k)
  refine ((isClosed_le continuous_const hc1).inter (isClosed_le continuous_const hc2)).inter ?_
  exact isClosed_le (continuous_finset_sum _ fun i _ => yv_cont b i) continuous_const

lemma KK_sub_box {m : ℕ} {e : EE m} (he : e ∈ KK m) :
    e ∈ (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin m => Set.Icc (-(m:ℝ)) m) ×ˢ
      (Set.univ.pi fun _ : Fin m => Set.Icc (0:ℝ) m) := by
  have h0 : (0 : Fin m → ℝ) ∈ U6 m := subset_convexHull ℝ _ (Or.inl (Or.inl rfl))
  have hq0 : ∀ i, 0 ≤ e.2 i := by
    intro i
    have := (he 0 h0).1 i
    simpa [yv_apply] using this
  have hq1 : ∀ i, e.2 i ≤ m := by
    intro i
    have h := (he 0 h0).2.2
    have h' : ∑ i, e.2 i ≤ m := by simpa [yv_apply] using h
    exact le_trans (Finset.single_le_sum (f := fun i => e.2 i) (fun i _ => hq0 i) (Finset.mem_univ i)) h'
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro i j
    have hj : (Pi.single j (1:ℝ) : Fin m → ℝ) ∈ U6 m :=
      subset_convexHull ℝ _ (Or.inl (Or.inr ⟨j, rfl⟩))
    have hy : ∀ k, yv e (Pi.single j 1) k = e.1 k j + e.2 k := by
      intro k; simp [yv_apply, Pi.single_apply]
    have hnn : ∀ k, 0 ≤ e.1 k j + e.2 k := fun k => by
      rw [← hy]; exact (he _ hj).1 k
    have hs : ∑ k, (e.1 k j + e.2 k) ≤ m := by
      have := (he _ hj).2.2
      simpa [hy] using this
    have : e.1 i j + e.2 i ≤ ∑ k, (e.1 k j + e.2 k) :=
      Finset.single_le_sum (f := fun k => e.1 k j + e.2 k) (fun k _ => hnn k) (Finset.mem_univ i)
    have h1 := hq0 i; have h2 := hq1 i; have h3 := hnn i
    constructor <;> linarith
  · simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    exact fun i => ⟨hq0 i, hq1 i⟩

lemma KK_nonempty {m : ℕ} (hm : 0 < m) : (KK m).Nonempty := by
  refine ⟨((fun _ _ => 0), (fun _ => 1)), ?_⟩
  intro b hb
  have hy : ∀ k, yv ((fun _ _ => 0), (fun _ => (1:ℝ))) b k = 1 := by
    intro k; simp [yv_apply]
  have hy' : yv ((fun _ _ => 0), (fun _ => (1:ℝ))) b = fun _ => 1 := funext hy
  rw [hy']
  refine ⟨fun i => zero_le_one, fun i => ?_, by simp⟩
  have hb1 := b_le_one hm hb i
  simp only [Matrix.mulVec, dotProduct, mul_one]
  have : B6 m i i ≤ ∑ k, B6 m i k := by
    refine Finset.single_le_sum (f := fun k => B6 m i k) (fun k _ => ?_) (Finset.mem_univ i)
    simp only [B6]; split_ifs
    · exact zero_le_one
    · positivity
  have h2 : B6 m i i = 1 := by simp [B6]
  linarith

open Classical in
lemma exists_opt {m : ℕ} (hm : 0 < m) :
    ∃ (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ), FeasA m P q ∧
      ∀ (P' : Matrix (Fin m) (Fin m) ℝ) (q' : Fin m → ℝ) (t : ℝ),
        FeasA m P' q' → CostA m P' q' t → CostA m P q t := by
  have hbox : IsCompact ((Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin m =>
      Set.Icc (-(m:ℝ)) m) ×ˢ (Set.univ.pi fun _ : Fin m => Set.Icc (0:ℝ) m)) :=
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc).prod
      (isCompact_univ_pi fun _ => isCompact_Icc)
  have hKc : IsCompact (KK m) := hbox.of_isClosed_subset KK_closed (fun e he => KK_sub_box he)
  have hne : (Vf m).Nonempty := ⟨0, by simp [Vf]⟩
  let g : EE m → ℝ := fun e => (Vf m).sup' hne (fun v => ∑ i, yv e v i)
  have hg : Continuous g :=
    Continuous.finset_sup'_apply hne fun v _ => continuous_finset_sum _ fun i _ => yv_cont v i
  obtain ⟨e0, he0, hmin⟩ := hKc.exists_isMinOn (KK_nonempty hm) hg.continuousOn
  obtain ⟨hF0, hC0⟩ := mem_KK.1 he0
  refine ⟨Matrix.of e0.1, e0.2, hF0, ?_⟩
  intro P' q' t hF' hC'
  by_cases ht : (m : ℝ) ≤ t
  · intro b hb
    exact le_trans (hC0 b hb) ht
  · push_neg at ht
    have he' : ((P' : Fin m → Fin m → ℝ), q') ∈ KK m :=
      mem_KK.2 ⟨hF', fun b hb => le_trans (hC' b hb) ht.le⟩
    have h1 : g e0 ≤ g ((P' : Fin m → Fin m → ℝ), q') := hmin he'
    have h2 : g ((P' : Fin m → Fin m → ℝ), q') ≤ t := by
      refine Finset.sup'_le _ _ fun v hv => ?_
      have := hC' v (subset_convexHull ℝ _ (mem_Vf.1 hv))
      rw [d6_dot] at this
      exact this
    have h3 : ∀ v ∈ VS m, ∑ i, yv e0 v i ≤ t := by
      intro v hv
      exact le_trans (Finset.le_sup' (fun v => ∑ i, yv e0 v i) (mem_Vf.2 hv)) (h1.trans h2)
    intro b hb
    have := cost_hull e0 t h3 b hb
    rw [d6_dot]
    exact this


theorem lemma3_core (m : ℕ) (hm_even : Even m) (hm0 : 0 < m) :
    ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ),
      AffinePolicies.Simplex.IsOptimalAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) x P q ∧
        ∀ i j, q i = q j := by
  obtain ⟨n, rfl⟩ := hm_even
  obtain ⟨P0, q0, hF0, hopt⟩ := exists_opt hm0
  obtain ⟨P1, q1, hF1, hC1, hq⟩ := sym_avg (good_trans n) P0 q0 hF0
  refine ⟨0, P1, q1, ⟨?_, ?_⟩, hq⟩
  · refine ⟨le_refl _, fun b hb => ?_⟩
    have := hF1 b hb
    simpa [A6, AffinePolicies.Simplex.affinePolicy] using this
  · intro x' P' q' t hF' hC'
    have hF'' : FeasA (n + n) P' q' := by
      intro b hb
      have := hF'.2 b hb
      simpa [A6, AffinePolicies.Simplex.affinePolicy] using this
    have hC'' : CostA (n + n) P' q' t := by
      intro b hb
      have := hC' b hb
      simpa [c6, AffinePolicies.Simplex.affinePolicy] using this
    have h0 := hopt P' q' t hF'' hC''
    have h1 := hC1 t h0
    intro b hb
    have := h1 b hb
    simpa [c6, AffinePolicies.Simplex.affinePolicy] using this

end AffinePolicies.TwoGap

open AffinePolicies.TwoGap


theorem solution (m : ℕ) (hm_even : Even m) (hm0 : 0 < m) :
    ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ),
      AffinePolicies.Simplex.IsOptimalAff (A6 m) (B6 m) (c6 m) (d6 m) (U6 m) x P q ∧ ∀ i j, q i = q j := by
  exact lemma3_core m hm_even hm0
