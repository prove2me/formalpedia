-- Prove2me | solution 1 for AugLagLLC.KKT.cpld_limit_kkt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T16:40:18.379877+00:00
-- url     : https://prove2.me/submissions/ead4077f-7bd5-4dcb-ba92-bcbac00d2aa8

import Mathlib
import Definitions.Def_AugLagLLC_KKT_ConstraintQualifications

open Filter Topology
open scoped InnerProductSpace

namespace AugLagFJ

lemma continuous_gradient_of_C1 {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiff ℝ 1 F) : Continuous (gradient F) := by
  have h := hF.continuous_fderiv one_ne_zero
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp h

/-- Fritz–John type limit extraction: normalizing by `1 + max ‖aₖ‖ ‖bₖ‖`. -/
lemma fj_limit {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {H : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : κ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : Continuous (gradient F)) (hH : ∀ i, Continuous (gradient (H i)))
    (hG : ∀ j, Continuous (gradient (G j)))
    {xs : EuclideanSpace ℝ (Fin n)}
    {y : ℕ → EuclideanSpace ℝ (Fin n)} (hy : Tendsto y atTop (𝓝 xs))
    (a : ℕ → ι → ℝ) (b : ℕ → κ → ℝ)
    (hres : Tendsto (fun k => gradient F (y k) + ∑ i, a k i • gradient (H i) (y k)
        + ∑ j, b k j • gradient (G j) (y k)) atTop (𝓝 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ (t : ℝ) (ah : ι → ℝ) (bh : κ → ℝ),
      Tendsto (fun j => (1 + max ‖a (ψ j)‖ ‖b (ψ j)‖)⁻¹) atTop (𝓝 t) ∧
      Tendsto (fun j => (1 + max ‖a (ψ j)‖ ‖b (ψ j)‖)⁻¹ • a (ψ j)) atTop (𝓝 ah) ∧
      Tendsto (fun j => (1 + max ‖a (ψ j)‖ ‖b (ψ j)‖)⁻¹ • b (ψ j)) atTop (𝓝 bh) ∧
      t + max ‖ah‖ ‖bh‖ = 1 ∧
      t • gradient F xs + ∑ i, ah i • gradient (H i) xs + ∑ j, bh j • gradient (G j) xs = 0 := by
  set M : ℕ → ℝ := fun k => max ‖a k‖ ‖b k‖ with hM
  set s : ℕ → ℝ := fun k => (1 + M k)⁻¹ with hs
  have hM0 : ∀ k, 0 ≤ M k := fun k => le_trans (norm_nonneg _) (le_max_left _ _)
  have hs0 : ∀ k, 0 < s k := fun k => inv_pos.2 (by linarith [hM0 k])
  have hsM : ∀ k, s k + s k * M k = 1 := fun k => by
    have : (1 + M k) ≠ 0 := by linarith [hM0 k]
    simp only [hs]; field_simp
  have hs1 : ∀ k, s k ≤ 1 := fun k => by nlinarith [hsM k, hs0 k, hM0 k]
  have hsM1 : ∀ k, s k * M k ≤ 1 := fun k => by nlinarith [hsM k, hs0 k, hM0 k]
  have hna : ∀ k, ‖s k • a k‖ = s k * ‖a k‖ := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 k)]
  have hnb : ∀ k, ‖s k • b k‖ = s k * ‖b k‖ := fun k => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hs0 k)]
  have hmax : ∀ k, max ‖s k • a k‖ ‖s k • b k‖ = s k * M k := fun k => by
    rw [hna, hnb, mul_max_of_nonneg _ _ (hs0 k).le]
  set z : ℕ → ℝ × (ι → ℝ) × (κ → ℝ) := fun k => (s k, s k • a k, s k • b k) with hz
  have hzb : ∀ k, z k ∈ Metric.closedBall (0 : ℝ × (ι → ℝ) × (κ → ℝ)) 1 := by
    intro k
    rw [mem_closedBall_zero_iff, Prod.norm_def, Prod.norm_def]
    simp only [hz, Real.norm_eq_abs, abs_of_pos (hs0 k)]
    refine max_le (hs1 k) (max_le ?_ ?_)
    · rw [hna]; exact le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (hs0 k).le) (hsM1 k)
    · rw [hnb]; exact le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (hs0 k).le) (hsM1 k)
  obtain ⟨⟨t, ah, bh⟩, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hzb
  have ht : Tendsto (fun j => s (ψ j)) atTop (𝓝 t) := (continuous_fst.tendsto _).comp hlim
  have ha : Tendsto (fun j => s (ψ j) • a (ψ j)) atTop (𝓝 ah) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have hb : Tendsto (fun j => s (ψ j) • b (ψ j)) atTop (𝓝 bh) :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  refine ⟨ψ, hψ, t, ah, bh, ht, ha, hb, ?_, ?_⟩
  · have h1 : Tendsto (fun j => s (ψ j) + max ‖s (ψ j) • a (ψ j)‖ ‖s (ψ j) • b (ψ j)‖) atTop
        (𝓝 (t + max ‖ah‖ ‖bh‖)) :=
      ht.add ((continuous_norm.tendsto _).comp ha |>.max ((continuous_norm.tendsto _).comp hb))
    have h2 : (fun j => s (ψ j) + max ‖s (ψ j) • a (ψ j)‖ ‖s (ψ j) • b (ψ j)‖) = fun _ => 1 := by
      funext j; rw [hmax]; exact hsM _
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  · have hyψ : Tendsto (fun j => y (ψ j)) atTop (𝓝 xs) := hy.comp hψ.tendsto_atTop
    have h1 : Tendsto (fun j => s (ψ j) • (gradient F (y (ψ j))
        + ∑ i, a (ψ j) i • gradient (H i) (y (ψ j))
        + ∑ j', b (ψ j) j' • gradient (G j') (y (ψ j)))) atTop (𝓝 (t • (0 : EuclideanSpace ℝ (Fin n)))) :=
      ht.smul (hres.comp hψ.tendsto_atTop)
    rw [smul_zero] at h1
    have h2 : Tendsto (fun j => s (ψ j) • (gradient F (y (ψ j))
        + ∑ i, a (ψ j) i • gradient (H i) (y (ψ j))
        + ∑ j', b (ψ j) j' • gradient (G j') (y (ψ j)))) atTop
        (𝓝 (t • gradient F xs + ∑ i, ah i • gradient (H i) xs + ∑ j, bh j • gradient (G j) xs)) := by
      have e : (fun j => s (ψ j) • (gradient F (y (ψ j))
          + ∑ i, a (ψ j) i • gradient (H i) (y (ψ j))
          + ∑ j', b (ψ j) j' • gradient (G j') (y (ψ j)))) = fun j =>
          s (ψ j) • gradient F (y (ψ j)) + ∑ i, (s (ψ j) • a (ψ j)) i • gradient (H i) (y (ψ j))
          + ∑ j', (s (ψ j) • b (ψ j)) j' • gradient (G j') (y (ψ j)) := by
        funext j
        simp only [smul_add, Finset.smul_sum, Pi.smul_apply, smul_smul, smul_eq_mul]
      rw [e]
      refine (ht.smul ((hF.tendsto _).comp hyψ)).add ?_ |>.add ?_
      · refine tendsto_finsetSum _ fun i _ => ?_
        exact ((tendsto_pi_nhds.1 ha) i).smul (((hH i).tendsto _).comp hyψ)
      · refine tendsto_finsetSum _ fun i _ => ?_
        exact ((tendsto_pi_nhds.1 hb) i).smul (((hG i).tendsto _).comp hyψ)
    exact tendsto_nhds_unique h2 h1


end AugLagFJ

namespace AugLagCara

open Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- One reduction step: subtracting a multiple of a linear relation. -/
lemma step (v : ι → E) (w : κ → E) (a : ι → ℝ) (b : κ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (c : ι → ℝ) (d : κ → ℝ) (hrel : ∑ i, c i • v i + ∑ j, d j • w j = 0)
    (hc : ∀ i, a i = 0 → c i = 0) (hd : ∀ j, b j = 0 → d j = 0)
    (hne : (∃ i, c i ≠ 0) ∨ (∃ j, d j ≠ 0)) :
    ∃ (a2 : ι → ℝ) (b2 : κ → ℝ), (∀ j, 0 ≤ b2 j) ∧
      ∑ i, a2 i • v i + ∑ j, b2 j • w j = ∑ i, a i • v i + ∑ j, b j • w j ∧
      (univ.filter fun i => a2 i ≠ 0).card + (univ.filter fun j => b2 j ≠ 0).card <
        (univ.filter fun i => a i ≠ 0).card + (univ.filter fun j => b j ≠ 0).card ∧
      (∀ j, b2 j ≠ 0 → b j ≠ 0) := by
  -- generic facts for `a - λ c`, `b - λ d`
  have gen : ∀ (c d : ι → ℝ) (d' : κ → ℝ) (_ : True), True := fun _ _ _ _ => trivial
  clear gen
  have hsum : ∀ (c : ι → ℝ) (d : κ → ℝ), ∑ i, c i • v i + ∑ j, d j • w j = 0 → ∀ l : ℝ,
      ∑ i, (a i - l * c i) • v i + ∑ j, (b j - l * d j) • w j =
        ∑ i, a i • v i + ∑ j, b j • w j := by
    intro c d h l
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum]
    have h' : l • (∑ i, c i • v i + ∑ j, d j • w j) = 0 := by rw [h, smul_zero]
    rw [smul_add] at h'
    calc ∑ i, a i • v i - l • ∑ i, c i • v i + (∑ j, b j • w j - l • ∑ j, d j • w j)
        = ∑ i, a i • v i + ∑ j, b j • w j - (l • ∑ i, c i • v i + l • ∑ j, d j • w j) := by
          abel
      _ = _ := by rw [h', sub_zero]
  have hcard : ∀ (a2 : ι → ℝ) (b2 : κ → ℝ), (∀ i, a i = 0 → a2 i = 0) →
      (∀ j, b j = 0 → b2 j = 0) →
      ((∃ i, a i ≠ 0 ∧ a2 i = 0) ∨ (∃ j, b j ≠ 0 ∧ b2 j = 0)) →
      (univ.filter fun i => a2 i ≠ 0).card + (univ.filter fun j => b2 j ≠ 0).card <
        (univ.filter fun i => a i ≠ 0).card + (univ.filter fun j => b j ≠ 0).card := by
    intro a2 b2 ha hb2 hx
    have s1 : (univ.filter fun i => a2 i ≠ 0) ⊆ (univ.filter fun i => a i ≠ 0) := by
      intro i; simp only [mem_filter, mem_univ, true_and]; exact fun h h' => h (ha i h')
    have s2 : (univ.filter fun j => b2 j ≠ 0) ⊆ (univ.filter fun j => b j ≠ 0) := by
      intro j; simp only [mem_filter, mem_univ, true_and]; exact fun h h' => h (hb2 j h')
    rcases hx with ⟨i, hi, hi2⟩ | ⟨j, hj, hj2⟩
    · have : (univ.filter fun i => a2 i ≠ 0) ⊂ (univ.filter fun i => a i ≠ 0) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨s1, fun heq => ?_⟩
        have : i ∈ (univ.filter fun i => a i ≠ 0) := by simp [hi]
        rw [← heq] at this; simp [hi2] at this
      have := Finset.card_lt_card this
      have := Finset.card_le_card s2
      omega
    · have : (univ.filter fun j => b2 j ≠ 0) ⊂ (univ.filter fun j => b j ≠ 0) := by
        refine Finset.ssubset_iff_subset_ne.2 ⟨s2, fun heq => ?_⟩
        have : j ∈ (univ.filter fun j => b j ≠ 0) := by simp [hj]
        rw [← heq] at this; simp [hj2] at this
      have := Finset.card_lt_card this
      have := Finset.card_le_card s1
      omega
  -- case with a positive `d`
  have pos : ∀ (c : ι → ℝ) (d : κ → ℝ), ∑ i, c i • v i + ∑ j, d j • w j = 0 →
      (∀ i, a i = 0 → c i = 0) → (∀ j, b j = 0 → d j = 0) → (∃ j, 0 < d j) →
      ∃ (a2 : ι → ℝ) (b2 : κ → ℝ), (∀ j, 0 ≤ b2 j) ∧
      ∑ i, a2 i • v i + ∑ j, b2 j • w j = ∑ i, a i • v i + ∑ j, b j • w j ∧
      (univ.filter fun i => a2 i ≠ 0).card + (univ.filter fun j => b2 j ≠ 0).card <
        (univ.filter fun i => a i ≠ 0).card + (univ.filter fun j => b j ≠ 0).card ∧
      (∀ j, b2 j ≠ 0 → b j ≠ 0) := by
    intro c d h hc hd ⟨j1, hj1⟩
    have hnon : (univ.filter fun j => 0 < d j).Nonempty := ⟨j1, by simp [hj1]⟩
    obtain ⟨j0, hj0m, hj0⟩ := Finset.exists_min_image _ (fun j => b j / d j) hnon
    simp only [mem_filter, mem_univ, true_and] at hj0m hj0
    set l := b j0 / d j0 with hl
    have hl0 : 0 ≤ l := div_nonneg (hb j0) hj0m.le
    refine ⟨fun i => a i - l * c i, fun j => b j - l * d j, ?_, hsum c d h l, ?_, ?_⟩
    · intro j
      rcases lt_or_ge 0 (d j) with hdj | hdj
      · have := hj0 j hdj
        rw [le_div_iff₀ hdj] at this
        linarith
      · nlinarith [hb j]
    · refine hcard _ _ (fun i hi => by simp [hi, hc i hi]) (fun j hj => by simp [hj, hd j hj])
        (Or.inr ⟨j0, fun h0 => ?_, ?_⟩)
      · exact hj0m.ne' (hd j0 h0)
      · simp only [hl]; field_simp; ring
    · intro j hj hbj
      exact hj (by simp [hbj, hd j hbj])
  by_cases hp : ∃ j, 0 < d j
  · exact pos c d hrel hc hd hp
  by_cases hn : ∃ j, d j < 0
  · refine pos (-c) (-d) ?_ (fun i hi => by simp [hc i hi]) (fun j hj => by simp [hd j hj]) ?_
    · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
      rw [← neg_add, hrel, neg_zero]
    · obtain ⟨j, hj⟩ := hn; exact ⟨j, by simp [hj]⟩
  push Not at hp hn
  have hd0 : ∀ j, d j = 0 := fun j => le_antisymm (hp j) (hn j)
  obtain ⟨i0, hi0⟩ : ∃ i, c i ≠ 0 := by
    rcases hne with h | ⟨j, hj⟩
    · exact h
    · exact absurd (hd0 j) hj
  set l := a i0 / c i0 with hl
  refine ⟨fun i => a i - l * c i, fun j => b j - l * d j, fun j => by simp [hd0 j, hb j],
    hsum c d hrel l, ?_, fun j hj hbj => hj (by simp [hbj, hd0 j])⟩
  refine hcard _ _ (fun i hi => by simp [hi, hc i hi]) (fun j hj => by simp [hj, hd0 j])
    (Or.inl ⟨i0, fun h0 => hi0 (hc i0 h0), ?_⟩)
  simp only [hl]; field_simp; ring

/-- Conic Carathéodory lemma with free and nonnegative coefficients. -/
theorem conic_caratheodory (v : ι → E) (w : κ → E) (a : ι → ℝ) (b : κ → ℝ)
    (hb : ∀ j, 0 ≤ b j) :
    ∃ (I : Finset ι) (J : Finset κ) (a' : ι → ℝ) (b' : κ → ℝ),
      (∀ i ∉ I, a' i = 0) ∧ (∀ j ∉ J, b' j = 0) ∧ (∀ j, 0 ≤ b' j) ∧ (∀ j ∈ J, b j ≠ 0) ∧
      ∑ i, a' i • v i + ∑ j, b' j • w j = ∑ i, a i • v i + ∑ j, b j • w j ∧
      LinearIndependent ℝ (Sum.elim (fun i : I => v i) (fun j : J => w j)) := by
  suffices H : ∀ N : ℕ, ∀ (a : ι → ℝ) (b : κ → ℝ), (∀ j, 0 ≤ b j) →
      (univ.filter fun i => a i ≠ 0).card + (univ.filter fun j => b j ≠ 0).card ≤ N →
      ∃ (I : Finset ι) (J : Finset κ) (a' : ι → ℝ) (b' : κ → ℝ),
      (∀ i ∉ I, a' i = 0) ∧ (∀ j ∉ J, b' j = 0) ∧ (∀ j, 0 ≤ b' j) ∧ (∀ j ∈ J, b j ≠ 0) ∧
      ∑ i, a' i • v i + ∑ j, b' j • w j = ∑ i, a i • v i + ∑ j, b j • w j ∧
      LinearIndependent ℝ (Sum.elim (fun i : I => v i) (fun j : J => w j)) from
    H _ a b hb le_rfl
  intro N
  induction N with
  | zero =>
    intro a b hb hN
    refine ⟨∅, ∅, a, b, fun i _ => ?_, fun j _ => ?_, hb, by simp, rfl, ?_⟩
    · by_contra h
      have : (univ.filter fun i => a i ≠ 0).card ≠ 0 :=
        Finset.card_ne_zero.2 ⟨i, by simp [h]⟩
      omega
    · by_contra h
      have : (univ.filter fun j => b j ≠ 0).card ≠ 0 :=
        Finset.card_ne_zero.2 ⟨j, by simp [h]⟩
      omega
    · exact linearIndependent_empty_type
  | succ N ih =>
    intro a b hb hN
    set I := univ.filter fun i => a i ≠ 0 with hI
    set J := univ.filter fun j => b j ≠ 0 with hJ
    by_cases hli : LinearIndependent ℝ (Sum.elim (fun i : I => v i) (fun j : J => w j))
    · refine ⟨I, J, a, b, fun i hi => ?_, fun j hj => ?_, hb, fun j hj => ?_, rfl, hli⟩
      · simpa [hI] using hi
      · simpa [hJ] using hj
      · simpa [hJ] using hj
    obtain ⟨g, hg, x0, hx0⟩ := Fintype.not_linearIndependent_iff.1 hli
    set c : ι → ℝ := fun i => if h : i ∈ I then g (Sum.inl ⟨i, h⟩) else 0 with hcdef
    set d : κ → ℝ := fun j => if h : j ∈ J then g (Sum.inr ⟨j, h⟩) else 0 with hddef
    have hc : ∀ i, a i = 0 → c i = 0 := fun i hi => by
      have : i ∉ I := by simp [hI, hi]
      simp [hcdef, this]
    have hd : ∀ j, b j = 0 → d j = 0 := fun j hj => by
      have : j ∉ J := by simp [hJ, hj]
      simp [hddef, this]
    have hrel : ∑ i, c i • v i + ∑ j, d j • w j = 0 := by
      rw [Fintype.sum_sum_type] at hg
      have e1 : ∑ i, c i • v i = ∑ i : I, g (Sum.inl i) • v i := by
        rw [← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by simp [hcdef, hi])]
        rw [← Finset.sum_coe_sort I]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [hcdef, i.2]
      have e2 : ∑ j, d j • w j = ∑ j : J, g (Sum.inr j) • w j := by
        rw [← Finset.sum_subset (Finset.subset_univ J) (fun j _ hj => by simp [hddef, hj])]
        rw [← Finset.sum_coe_sort J]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [hddef, j.2]
      rw [e1, e2]
      simpa using hg
    have hne : (∃ i, c i ≠ 0) ∨ (∃ j, d j ≠ 0) := by
      rcases x0 with i | j
      · exact Or.inl ⟨i, by simpa [hcdef, i.2] using hx0⟩
      · exact Or.inr ⟨j, by simpa [hddef, j.2] using hx0⟩
    obtain ⟨a2, b2, hb2, hs2, hlt, hsupp⟩ := step v w a b hb c d hrel hc hd hne
    rw [← hI, ← hJ] at hlt
    obtain ⟨I', J', a', b', h1, h2, h3, h4, h5, h6⟩ := ih a2 b2 hb2 (by omega)
    exact ⟨I', J', a', b', h1, h2, h3, fun j hj => hsupp j (h4 j hj), h5.trans hs2, h6⟩

end AugLagCara

open AugLagFJ AugLagCara AugLagLLC.KKT

theorem solution {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {F : EuclideanSpace ℝ (Fin n) → ℝ} {H : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {G : κ → EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiff ℝ 1 F) (hH : ∀ i, ContDiff ℝ 1 (H i)) (hG : ∀ j, ContDiff ℝ 1 (G j))
    {xs : EuclideanSpace ℝ (Fin n)} (hHx : ∀ i, H i xs = 0) (hGx : ∀ j, G j xs ≤ 0)
    (hcpld : CPLDAt H G xs)
    {y : ℕ → EuclideanSpace ℝ (Fin n)} (hy : Tendsto y atTop (𝓝 xs))
    (a : ℕ → ι → ℝ) (b : ℕ → κ → ℝ) (hb : ∀ k j, 0 ≤ b k j)
    (hbG : ∀ k j, G j xs < 0 → b k j = 0)
    (hres : Tendsto (fun k => gradient F (y k) + ∑ i, a k i • gradient (H i) (y k)
        + ∑ j, b k j • gradient (G j) (y k)) atTop (𝓝 0)) :
    IsKKT F H G xs := by
  classical
  -- Carathéodory at every iterate
  choose I J a' b' h1 h2 h3 h4 h5 h6 using fun k =>
    conic_caratheodory (fun i => gradient (H i) (y k)) (fun j => gradient (G j) (y k))
      (a k) (b k) (hb k)
  -- pigeonhole on the supports
  obtain ⟨c, hc⟩ := Finite.exists_infinite_fiber (fun k => (I k, J k))
  have hfreq : ∃ᶠ k in atTop, (I k, J k) = c := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact Set.infinite_coe_iff.1 hc
  obtain ⟨φ0, hφ0, hφ0c⟩ := extraction_of_frequently_atTop hfreq
  have hφ0t := hφ0.tendsto_atTop
  have hIc : ∀ m, I (φ0 m) = c.1 := fun m => by rw [← hφ0c m]
  have hJc : ∀ m, J (φ0 m) = c.2 := fun m => by rw [← hφ0c m]
  have hres' : Tendsto (fun m => gradient F (y (φ0 m)) + ∑ i, a' (φ0 m) i • gradient (H i) (y (φ0 m))
      + ∑ j, b' (φ0 m) j • gradient (G j) (y (φ0 m))) atTop (𝓝 0) := by
    have := hres.comp hφ0t
    refine this.congr fun m => ?_
    simp only [Function.comp, add_assoc, h5]
  have cF := continuous_gradient_of_C1 hF
  have cH := fun i => continuous_gradient_of_C1 (hH i)
  have cG := fun j => continuous_gradient_of_C1 (hG j)
  obtain ⟨ψ, hψ, t, ah, bh, ht, ha, hbt, hnorm, heq⟩ :=
    fj_limit cF cH cG (hy.comp hφ0t) (fun m => a' (φ0 m)) (fun m => b' (φ0 m)) hres'
  set s : ℕ → ℝ := fun m => (1 + max ‖a' (φ0 (ψ m))‖ ‖b' (φ0 (ψ m))‖)⁻¹ with hs
  have hs0 : ∀ m, 0 < s m := fun m =>
    inv_pos.2 (by linarith [le_trans (norm_nonneg (a' (φ0 (ψ m)))) (le_max_left _ ‖b' (φ0 (ψ m))‖)])
  -- properties of the limit coefficients
  have hah0 : ∀ i ∉ c.1, ah i = 0 := fun i hi => by
    have := (tendsto_pi_nhds.1 ha) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    refine tendsto_nhds_unique this (tendsto_const_nhds.congr fun m => ?_)
    rw [h1 _ i (by rw [hIc]; exact hi), mul_zero]
  have hbh0 : ∀ j ∉ c.2, bh j = 0 := fun j hj => by
    have := (tendsto_pi_nhds.1 hbt) j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    refine tendsto_nhds_unique this (tendsto_const_nhds.congr fun m => ?_)
    rw [h2 _ j (by rw [hJc]; exact hj), mul_zero]
  have hbhnn : ∀ j, 0 ≤ bh j := fun j =>
    ge_of_tendsto' ((tendsto_pi_nhds.1 hbt) j) fun m => by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg (hs0 m).le (h3 _ _)
  have hJact : ∀ j ∈ c.2, G j xs = 0 := fun j hj => by
    have hj' : j ∈ J (φ0 0) := by rw [hJc]; exact hj
    rcases lt_or_eq_of_le (hGx j) with hlt | heq'
    · exact absurd (hbG _ j hlt) (h4 _ j hj')
    · exact heq'
  have ht0 : 0 ≤ t := ge_of_tendsto' ht fun m => (hs0 m).le
  rcases lt_or_eq_of_le ht0 with htpos | htz
  · -- KKT multipliers
    refine ⟨hHx, hGx, fun i => t⁻¹ * ah i, fun j => t⁻¹ * bh j,
      fun j => mul_nonneg (inv_nonneg.2 ht0) (hbhnn j), fun j hj => ?_, ?_⟩
    · have : j ∉ c.2 := fun hjc => by linarith [hJact j hjc]
      show t⁻¹ * bh j = 0
      rw [hbh0 j this, mul_zero]
    · have := congrArg (fun w => t⁻¹ • w) heq
      simp only [smul_add, smul_zero, Finset.smul_sum, smul_smul, inv_mul_cancel₀ htpos.ne',
        one_smul, smul_eq_mul] at this
      exact this
  · -- t = 0 contradicts CPLD
    exfalso
    subst htz
    simp only [zero_smul, zero_add] at heq hnorm
    have hnt : (∃ i ∈ c.1, ah i ≠ 0) ∨ (∃ j ∈ c.2, bh j ≠ 0) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hA, hB⟩ := hcon
      have eA : ah = 0 := funext fun i => by
        by_cases hi : i ∈ c.1
        · exact hA i hi
        · exact hah0 i hi
      have eB : bh = 0 := funext fun j => by
        by_cases hj : j ∈ c.2
        · exact hB j hj
        · exact hbh0 j hj
      rw [eA, eB] at hnorm
      simp at hnorm
    have hsumI : ∑ i ∈ c.1, ah i • gradient (H i) xs + ∑ j ∈ c.2, bh j • gradient (G j) xs = 0 := by
      rw [Finset.sum_subset (Finset.subset_univ c.1) (fun i _ hi => by simp [hah0 i hi]),
        Finset.sum_subset (Finset.subset_univ c.2) (fun j _ hj => by simp [hbh0 j hj])]
      exact heq
    have hdep := hcpld c.1 c.2 hJact ⟨ah, bh, fun j _ => hbhnn j, hnt, hsumI⟩
    have hyl : Tendsto (fun m => y (φ0 (ψ m))) atTop (𝓝 xs) :=
      (hy.comp hφ0t).comp hψ.tendsto_atTop
    obtain ⟨m, hm⟩ := (hyl.eventually hdep).exists
    have hli := h6 (φ0 (ψ m))
    rw [hIc, hJc] at hli
    exact hm hli
