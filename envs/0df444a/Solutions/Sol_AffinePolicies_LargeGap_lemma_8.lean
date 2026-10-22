-- Prove2me | solution 1 for AffinePolicies.LargeGap.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T02:09:25.777057+00:00
-- url     : https://prove2.me/submissions/e60e80f0-8b98-4805-822b-fa2250d5c5e0

import Mathlib
import Definitions.Def_AffinePolicies_LargeGap_Setting



namespace AffinePolicies.LargeGap

open AffinePolicies.Simplex Matrix

lemma g35_sym_apply {m : ℕ} (θ μ lam : ℝ) (b : Fin m → ℝ) (i : Fin m) :
    affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam) b i
      = (θ - μ) * b i + μ * ∑ k, b k + lam := by
  simp only [affinePolicy, Matrix.mulVec, dotProduct, Pi.add_apply]
  have : ∀ k, (if i = k then θ else μ) * b k
      = (θ - μ) * (if i = k then b k else 0) + μ * b k := by
    intro k; split_ifs <;> ring
  simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq]
  simp

lemma g35_B_apply {m : ℕ} (δ : ℝ) (y : Fin m → ℝ) (i : Fin m) :
    (B19 m δ *ᵥ y) i = y i + theta0 m δ * (∑ k, y k - y i) := by
  rw [show ∑ k, y k - y i = ∑ k ∈ Finset.univ.erase i, y k by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring]
  simp only [B19, Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, one_mul]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hk))]

lemma g35_cost {m : ℕ} (x y : Fin m → ℝ) :
    c19 m ⬝ᵥ x + d19 m ⬝ᵥ y = ∑ i, y i := by
  simp [c19, d19, dotProduct]

lemma g35_mem_zero (m : ℕ) (δ : ℝ) : (0 : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inl (Or.inl (Or.inl rfl)))

lemma g35_mem_single (m : ℕ) (δ : ℝ) (j : Fin m) :
    (Pi.single j (1:ℝ) : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))

lemma g35_mem_const (m : ℕ) (δ : ℝ) :
    (fun _ => 1 / Real.sqrt m : Fin m → ℝ) ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inl (Or.inr rfl))

lemma g35_mem_block (m : ℕ) (δ : ℝ) (S : Finset (Fin m)) (hS : S.card = rr m δ) :
    blockPt m δ S ∈ U19 m δ :=
  subset_convexHull ℝ _ (Or.inr ⟨S, hS, rfl⟩)

/-- Good: feasible with x = 0 and worst-case cost ≤ t, for the symmetric policy. -/
def G35Good (m : ℕ) (δ θ μ lam t : ℝ) : Prop :=
  Feasible (A19 m) (B19 m δ) (U19 m δ) 0
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)) ∧
    CostLE (c19 m) (d19 m) (U19 m δ) 0
      (affinePolicy (fun i j => if i = j then θ else μ) (fun _ => lam)) t

lemma g35_good_iff (m : ℕ) (δ θ μ lam t : ℝ) :
    G35Good m δ θ μ lam t ↔ ∀ b ∈ U19 m δ,
      (∀ i, 0 ≤ (θ - μ) * b i + μ * ∑ k, b k + lam ∧
        b i ≤ ((θ - μ) * b i + μ * ∑ k, b k + lam) + theta0 m δ *
          (∑ k, ((θ - μ) * b k + μ * ∑ k, b k + lam) - ((θ - μ) * b i + μ * ∑ k, b k + lam))) ∧
      ∑ k, ((θ - μ) * b k + μ * ∑ k, b k + lam) ≤ t := by
  unfold G35Good Feasible CostLE
  simp only [A19, Matrix.zero_mulVec, zero_add, g35_cost, Pi.le_def, g35_B_apply,
    g35_sym_apply, Pi.zero_apply, le_refl, implies_true, true_and]
  constructor
  · rintro ⟨h1, h2⟩ b hb
    exact ⟨fun i => ⟨(h1 b hb).1 i, (h1 b hb).2 i⟩, h2 b hb⟩
  · intro h
    exact ⟨fun b hb => ⟨fun i => ((h b hb).1 i).1, fun i => ((h b hb).1 i).2⟩,
      fun b hb => (h b hb).2⟩

lemma g35_closed (m : ℕ) (δ : ℝ) :
    IsClosed {p : ℝ × ℝ × ℝ × ℝ | G35Good m δ p.1 p.2.1 p.2.2.1 p.2.2.2} := by
  simp only [g35_good_iff, Set.setOf_forall, Set.setOf_and]
  refine isClosed_iInter fun b => isClosed_iInter fun _ =>
    IsClosed.inter (isClosed_iInter fun i => IsClosed.inter ?_ ?_) ?_ <;>
    exact isClosed_le (by fun_prop) (by fun_prop)

lemma g35_sum_single {m : ℕ} (j : Fin m) : ∑ k, (Pi.single j (1:ℝ) : Fin m → ℝ) k = 1 := by
  simp

/-- bounds on a good symmetric triple -/
lemma g35_bounds (m : ℕ) (hm0 : 0 < m) (δ θ μ lam t C : ℝ) (h : G35Good m δ θ μ lam t)
    (htC : t ≤ C) :
    0 ≤ t ∧ 0 ≤ lam ∧ lam ≤ C ∧ -C ≤ θ ∧ θ ≤ m * C ∧ (2 ≤ m → -C ≤ μ ∧ μ ≤ 2 * C) := by
  rw [g35_good_iff] at h
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm0
  let j0 : Fin m := ⟨0, hm0⟩
  obtain ⟨h0a, h0c⟩ := h 0 (g35_mem_zero m δ)
  have f0 := (h0a j0).1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at f0 h0c
  obtain ⟨hja, hjc⟩ := h _ (g35_mem_single m δ j0)
  rw [g35_sum_single] at hja hjc
  have fj0 := (hja j0).1
  simp only [Pi.single_eq_same] at fj0
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, g35_sum_single] at hjc
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hjc
  -- hjc : (θ - μ) * 1 + m * (μ * 1) + m * lam ≤ t
  have ht0 : 0 ≤ t := by nlinarith
  have hlC : lam ≤ C := by nlinarith
  have hθ1 : -C ≤ θ := by nlinarith
  have hμ' : 2 ≤ m → -lam ≤ μ := by
    intro h2
    let j1 : Fin m := ⟨1, by omega⟩
    have := (hja j1).1
    have hne : j1 ≠ j0 := by simp [j0, j1, Fin.ext_iff]
    simp only [Pi.single_eq_of_ne hne] at this
    linarith
  have hμm : (m - 1 : ℝ) * μ ≥ -((m - 1 : ℝ) * lam) := by
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have : m = 1 := by omega
      subst this; simp
    · have := hμ' h2
      have : (0:ℝ) ≤ m - 1 := by linarith
      nlinarith
  refine ⟨ht0, f0, hlC, hθ1, ?_, ?_⟩
  · nlinarith
  · intro h2
    have := hμ' h2
    have hm2 : (2:ℝ) ≤ m := by exact_mod_cast h2
    refine ⟨by linarith, ?_⟩
    have : (m - 1 : ℝ) * μ ≤ 2 * C := by nlinarith
    by_contra hc
    push_neg at hc
    nlinarith

/-- U is bounded componentwise -/
lemma g35_U_bound (m : ℕ) (hm0 : 0 < m) (δ : ℝ) (b : Fin m → ℝ) (hb : b ∈ U19 m δ) :
    b ∈ Set.Icc (0 : Fin m → ℝ) (fun _ => 1 + theta0 m δ) := by
  have hθ : 0 < theta0 m δ := by
    unfold theta0; have : (0:ℝ) < m := by exact_mod_cast hm0
    exact one_div_pos.mpr (Real.rpow_pos_of_pos this _)
  refine convexHull_min ?_ (convex_Icc _ _) hb
  rintro g (((rfl | ⟨j, rfl⟩) | rfl) | ⟨S, -, rfl⟩)
  · exact ⟨le_refl _, fun i => by simp; linarith⟩
  · refine ⟨fun i => ?_, fun i => ?_⟩
    · by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    · by_cases h : i = j
      · subst h; simp; linarith
      · simp [Pi.single_eq_of_ne h]; linarith
  · have hs : (1:ℝ) ≤ Real.sqrt m := by
      rw [Real.one_le_sqrt]; exact_mod_cast hm0
    refine ⟨fun i => by simp, fun i => ?_⟩
    simp only
    have : 1 / Real.sqrt m ≤ 1 := by rw [div_le_one (by linarith)]; exact hs
    linarith
  · refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [blockPt, Pi.zero_apply]; split_ifs <;> linarith
    · simp only [blockPt]; split_ifs <;> linarith

lemma g35_identity_good (m : ℕ) (hm0 : 0 < m) (δ : ℝ) :
    G35Good m δ 1 0 0 (m * (1 + theta0 m δ)) := by
  have hθ : 0 < theta0 m δ := by
    unfold theta0; have : (0:ℝ) < m := by exact_mod_cast hm0
    exact one_div_pos.mpr (Real.rpow_pos_of_pos this _)
  rw [g35_good_iff]
  intro b hb
  have hB := g35_U_bound m hm0 δ b hb
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  refine ⟨fun i => ⟨hB.1 i, ?_⟩, ?_⟩
  · have : 0 ≤ ∑ k, b k - b i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_sub_cancel_left]
      exact Finset.sum_nonneg fun k _ => hB.1 k
    nlinarith
  · calc ∑ k, b k ≤ ∑ _k : Fin m, (1 + theta0 m δ) := Finset.sum_le_sum fun k _ => hB.2 k
      _ = m * (1 + theta0 m δ) := by simp; ring

/-- permutation invariance of U -/
lemma g35_U_perm (m : ℕ) (δ : ℝ) (τ : Equiv.Perm (Fin m)) (b : Fin m → ℝ)
    (hb : b ∈ U19 m δ) : b ∘ τ ∈ U19 m δ := by
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) := LinearMap.funLeft ℝ ℝ τ
  have hL : ∀ v, L v = v ∘ τ := fun v => rfl
  have : U19 m δ ⊆ L ⁻¹' U19 m δ := by
    refine convexHull_min ?_ ((convex_convexHull ℝ _).linear_preimage L) 
    rintro g (((rfl | ⟨j, rfl⟩) | rfl) | ⟨S, hS, rfl⟩)
    · show L 0 ∈ U19 m δ
      rw [map_zero]; exact g35_mem_zero m δ
    · show L _ ∈ U19 m δ
      have : L (Pi.single j 1) = Pi.single (τ.symm j) 1 := by
        rw [hL]; ext i
        simp only [Function.comp_apply, Pi.single_apply, Equiv.eq_symm_apply]
      rw [this]; exact g35_mem_single m δ _
    · show L _ ∈ U19 m δ
      rw [hL]; exact g35_mem_const m δ
    · show L _ ∈ U19 m δ
      have : L (blockPt m δ S) = blockPt m δ (S.map τ.symm.toEmbedding) := by
        rw [hL]; ext i
        simp only [Function.comp_apply, blockPt, Finset.mem_map_equiv, Equiv.symm_symm]
      rw [this]
      exact g35_mem_block m δ _ (by rw [Finset.card_map, hS])
  exact this hb

lemma g35_B_perm (m : ℕ) (δ : ℝ) (σ : Equiv.Perm (Fin m)) (v : Fin m → ℝ) (i : Fin m) :
    (B19 m δ *ᵥ (v ∘ σ)) i = (B19 m δ *ᵥ v) (σ i) := by
  rw [g35_B_apply, g35_B_apply]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp σ v]

lemma g35_perm_two {m : ℕ} (j0 j1 i k : Fin m) (h01 : j0 ≠ j1) (hik : i ≠ k) :
    ∃ τ : Equiv.Perm (Fin m), τ j0 = i ∧ τ j1 = k := by
  let τ1 := Equiv.swap j0 i
  have h1 : τ1 j0 = i := Equiv.swap_apply_left _ _
  have hu : τ1 j1 ≠ i := by
    intro h; apply h01; apply τ1.injective; rw [h, h1]
  refine ⟨Equiv.swap (τ1 j1) k * τ1, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, h1, Equiv.swap_apply_of_ne_of_ne hu.symm hik]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

lemma g35_reindex {m : ℕ} (f : Equiv.Perm (Fin m) → ℝ) (τ : Equiv.Perm (Fin m)) :
    ∑ σ, f (σ * τ) = ∑ σ, f σ :=
  Equiv.sum_comp (Equiv.mulRight τ) f

/-- symmetrization -/
lemma g35_symm (m : ℕ) (hm0 : 0 < m) (δ : ℝ) (x' : Fin m → ℝ) (P' : Matrix (Fin m) (Fin m) ℝ)
    (q' : Fin m → ℝ) (t : ℝ)
    (hf : Feasible (A19 m) (B19 m δ) (U19 m δ) x' (affinePolicy P' q'))
    (hc : CostLE (c19 m) (d19 m) (U19 m δ) x' (affinePolicy P' q') t) :
    ∃ θ μ lam, G35Good m δ θ μ lam t ∧ (m < 2 → μ = 0) := by
  classical
  set N : ℝ := ((Finset.univ : Finset (Equiv.Perm (Fin m))).card : ℝ) with hN
  have hNpos : 0 < N := by
    rw [hN]; exact_mod_cast Finset.card_pos.mpr Finset.univ_nonempty
  let j0 : Fin m := ⟨0, hm0⟩
  let θb : ℝ := (1 / N) * ∑ σ : Equiv.Perm (Fin m), P' (σ j0) (σ j0)
  let μb : ℝ := if h : 2 ≤ m then (1 / N) * ∑ σ : Equiv.Perm (Fin m), P' (σ j0) (σ ⟨1, h⟩) else 0
  let lb : ℝ := (1 / N) * ∑ σ : Equiv.Perm (Fin m), q' (σ j0)
  let Y' := affinePolicy P' q'
  let Ys : Equiv.Perm (Fin m) → (Fin m → ℝ) → Fin m → ℝ := fun σ b => Y' (b ∘ σ.symm) ∘ σ
  -- per-σ facts
  have hs1 : ∀ σ, ∀ b ∈ U19 m δ, ∀ i, 0 ≤ Ys σ b i := by
    intro σ b hb i
    exact (hf.2 _ (g35_U_perm m δ σ.symm b hb)).1 (σ i)
  have hs2 : ∀ σ, ∀ b ∈ U19 m δ, ∀ i, b i ≤ (B19 m δ *ᵥ Ys σ b) i := by
    intro σ b hb i
    have := (hf.2 _ (g35_U_perm m δ σ.symm b hb)).2 (σ i)
    simp only [A19, Matrix.zero_mulVec, zero_add, Function.comp_apply,
      Equiv.symm_apply_apply] at this
    rw [g35_B_perm]; exact this
  have hs3 : ∀ σ, ∀ b ∈ U19 m δ, ∑ i, Ys σ b i ≤ t := by
    intro σ b hb
    have := hc _ (g35_U_perm m δ σ.symm b hb)
    rw [g35_cost] at this
    simp only [Ys, Function.comp_apply]
    rw [Equiv.sum_comp σ (fun i => Y' (b ∘ σ.symm) i)]
    exact this
  -- the averaged policy
  let Yb : (Fin m → ℝ) → Fin m → ℝ := fun b => (1 / N) • ∑ σ, Ys σ b
  have hYb : ∀ b i, Yb b i = (1 / N) * ∑ σ, Ys σ b i := by
    intro b i; simp [Yb, Finset.sum_apply]
  -- entrywise averages
  have hq : ∀ i, (1 / N) * ∑ σ : Equiv.Perm (Fin m), q' (σ i) = lb := by
    intro i
    simp only [lb]
    congr 1
    rw [← g35_reindex (fun σ => q' (σ j0)) (Equiv.swap j0 i)]
    simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  have hP : ∀ i k, (1 / N) * ∑ σ : Equiv.Perm (Fin m), P' (σ i) (σ k)
      = if i = k then θb else μb := by
    intro i k
    split_ifs with hik
    · subst hik
      simp only [θb]
      congr 1
      rw [← g35_reindex (fun σ => P' (σ j0) (σ j0)) (Equiv.swap j0 i)]
      simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    · have h2 : 2 ≤ m := by
        by_contra h2
        apply hik; ext; omega
      simp only [μb, dif_pos h2]
      congr 1
      have h01 : j0 ≠ ⟨1, h2⟩ := by simp [j0, Fin.ext_iff]
      obtain ⟨τ, hτ0, hτ1⟩ := g35_perm_two j0 ⟨1, h2⟩ i k h01 hik
      rw [← g35_reindex (fun σ => P' (σ j0) (σ ⟨1, h2⟩)) τ]
      simp only [Equiv.Perm.mul_apply, hτ0, hτ1]
  have heq : affinePolicy (fun i j => if i = j then θb else μb) (fun _ => lb) = Yb := by
    funext b i
    rw [hYb]
    simp only [Ys, Y', affinePolicy, Function.comp_apply, Pi.add_apply, Matrix.mulVec,
      dotProduct]
    have inner : ∀ σ : Equiv.Perm (Fin m),
        ∑ k, P' (σ i) k * (b ∘ σ.symm) k = ∑ k, P' (σ i) (σ k) * b k := by
      intro σ
      rw [← Equiv.sum_comp σ (fun k => P' (σ i) k * (b ∘ σ.symm) k)]
      simp
    simp only [Function.comp_apply] at inner
    simp_rw [inner]
    rw [Finset.sum_add_distrib, Finset.sum_comm, mul_add, Finset.mul_sum, hq]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← hP i k, ← Finset.sum_mul]; ring
  refine ⟨θb, μb, lb, ?_, ?_⟩
  · unfold G35Good
    rw [heq]
    refine ⟨⟨le_refl _, fun b hb => ⟨fun i => ?_, fun i => ?_⟩⟩, fun b hb => ?_⟩
    · rw [Pi.zero_apply, hYb]
      exact mul_nonneg (one_div_pos.mpr hNpos).le (Finset.sum_nonneg fun σ _ => hs1 σ b hb i)
    · simp only [A19, Matrix.zero_mulVec, zero_add, Yb, Matrix.mulVec_smul, Matrix.mulVec_sum,
        Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have : ∑ σ : Equiv.Perm (Fin m), b i ≤ ∑ σ, (B19 m δ *ᵥ Ys σ b) i :=
        Finset.sum_le_sum fun σ _ => hs2 σ b hb i
      rw [Finset.sum_const, nsmul_eq_mul, ← hN] at this
      have h' := mul_le_mul_of_nonneg_left this (one_div_pos.mpr hNpos).le
      rw [← mul_assoc, one_div_mul_cancel hNpos.ne', one_mul] at h'
      exact h'
    · rw [g35_cost]
      simp only [hYb]
      rw [← Finset.mul_sum, Finset.sum_comm]
      have : ∑ σ : Equiv.Perm (Fin m), ∑ i, Ys σ b i ≤ ∑ σ : Equiv.Perm (Fin m), t :=
        Finset.sum_le_sum fun σ _ => hs3 σ b hb
      rw [Finset.sum_const, nsmul_eq_mul, ← hN] at this
      have h' := mul_le_mul_of_nonneg_left this (one_div_pos.mpr hNpos).le
      rw [← mul_assoc, one_div_mul_cancel hNpos.ne', one_mul] at h'
      exact h'
  · intro h2
    simp only [μb, dif_neg (by omega : ¬ 2 ≤ m)]

theorem g35_lemma8_core (δ : ℝ) (m : ℕ) (hm0 : 0 < m) :
    ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (μ θ lam : ℝ),
      IsOptimalAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) x P q ∧
        (∀ i j, i ≠ j → P i j = μ) ∧ (∀ j, P j j = θ) ∧ (∀ j, q j = lam) := by
  set C : ℝ := m * (1 + theta0 m δ) with hC
  have hgood0 := g35_identity_good m hm0 δ
  rw [← hC] at hgood0
  have hb0 := g35_bounds m hm0 δ 1 0 0 C C hgood0 le_rfl
  have hC0 : 0 ≤ C := hb0.1
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm0
  set M : ℝ := (m + 2) * C with hM
  have hMC : C ≤ M := by nlinarith
  have hmC : (m:ℝ) * C ≤ M := by nlinarith
  have h2C : 2 * C ≤ M := by nlinarith
  let K : Set (ℝ × ℝ × ℝ × ℝ) :=
    {p | G35Good m δ p.1 p.2.1 p.2.2.1 p.2.2.2} ∩ Set.Icc (-M, -M, -M, -M) (M, M, M, C)
  have hK : IsCompact K := isCompact_Icc.inter_left (g35_closed m δ)
  -- membership criterion
  have hmem : ∀ θ μ lam t, G35Good m δ θ μ lam t → t ≤ C → (m < 2 → μ = 0) →
      ((θ, μ, lam, t) : ℝ × ℝ × ℝ × ℝ) ∈ K := by
    intro θ μ lam t hg htC hμ0
    obtain ⟨ht0, hl0, hlC, hθ1, hθ2, hμ⟩ := g35_bounds m hm0 δ θ μ lam t C hg htC
    refine ⟨hg, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, htC⟩
    · show -M ≤ θ; linarith
    · show -M ≤ μ
      rcases Nat.lt_or_ge m 2 with h | h
      · rw [hμ0 h]; linarith
      · linarith [(hμ h).1]
    · show -M ≤ lam; linarith
    · show -M ≤ t; linarith
    · show θ ≤ M; linarith
    · show μ ≤ M
      rcases Nat.lt_or_ge m 2 with h | h
      · rw [hμ0 h]; linarith
      · linarith [(hμ h).2]
    · show lam ≤ M; linarith
  have hne : K.Nonempty := ⟨_, hmem 1 0 0 C hgood0 le_rfl (fun _ => rfl)⟩
  obtain ⟨p, hpK, hpmin⟩ := hK.exists_isMinOn hne
    (by fun_prop : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2)).continuousOn
  refine ⟨0, fun i j => if i = j then p.1 else p.2.1, fun _ => p.2.2.1, p.2.1, p.1, p.2.2.1,
    ⟨hpK.1.1, ?_⟩, ?_, ?_, ?_⟩
  · intro x' P' q' t hf hc
    obtain ⟨θ', μ', l', hg, hμ0⟩ := g35_symm m hm0 δ x' P' q' t hf hc
    have hpc := hpK.1.2
    have hle : p.2.2.2 ≤ t := by
      rcases le_or_gt C t with h | h
      · exact hpK.2.2.2.2.2.trans h
      · exact hpmin (hmem θ' μ' l' t hg h.le hμ0)
    intro b hb
    exact (hpc b hb).trans hle
  · intro i j hij; simp [hij]
  · intro j; simp
  · intro j; rfl

end AffinePolicies.LargeGap

open AffinePolicies.LargeGap


theorem solution (δ : ℝ) (m : ℕ) (hm0 : 0 < m) :
    ∃ (x : Fin m → ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (q : Fin m → ℝ) (μ θ lam : ℝ),
      AffinePolicies.Simplex.IsOptimalAff (A19 m) (B19 m δ) (c19 m) (d19 m) (U19 m δ) x P q ∧
        (∀ i j, i ≠ j → P i j = μ) ∧ (∀ j, P j j = θ) ∧ (∀ j, q j = lam) := by
  exact g35_lemma8_core δ m hm0
