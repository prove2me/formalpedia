-- Prove2me | solution 1 for AlgMechDesign.Local.no_local_mechanism_below_n
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:35:37.109177+00:00
-- url     : https://prove2.me/submissions/b4e0d73e-1ad7-4fd2-8af7-5e17211e0f8d

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices



namespace AlgMechDesign.Local

open Finset

lemma nl_util_eq {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (d : Fin n → Fin k → ℝ) (i : Fin n)
    (ti : Fin k → ℝ) :
    utility alloc pay d i ti = pay d i - setTime ti (agentSet alloc d i) := rfl

lemma nl_pay_eq_price {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htr : IsTruthful alloc pay)
    {t : Fin n → Fin k → ℝ} (ht : IsType t) (i : Fin n) :
    pay t i = price alloc pay i (agentSet alloc t i) t := by
  have hA : IsAttainable alloc i (agentSet alloc t i) t :=
    ⟨t i, fun j => ht i j, by rw [Function.update_eq_self]⟩
  have hp : price alloc pay i (agentSet alloc t i) t
      = pay (Function.update t i (Classical.choose hA)) i := by
    unfold price; rw [dif_pos hA]
  obtain ⟨hw, hwY⟩ := Classical.choose_spec hA
  have h1 := htr t ht i (t i) (Classical.choose hA) (fun j => ht i j) hw
  have h2 := htr t ht i (Classical.choose hA) (t i) hw (fun j => ht i j)
  rw [nl_util_eq, nl_util_eq, hwY, Function.update_eq_self] at h1 h2
  linarith

lemma nl_menu {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htr : IsTruthful alloc pay)
    {t : Fin n → Fin k → ℝ} (ht : IsType t) (i : Fin n) {Y : Finset (Fin k)}
    (hY : IsAttainable alloc i Y t) :
    price alloc pay i Y t - setTime (t i) Y ≤
      price alloc pay i (agentSet alloc t i) t - setTime (t i) (agentSet alloc t i) := by
  have hp : price alloc pay i Y t = pay (Function.update t i (Classical.choose hY)) i := by
    unfold price; rw [dif_pos hY]
  obtain ⟨hw, hwY⟩ := Classical.choose_spec hY
  have h1 := htr t ht i (t i) (Classical.choose hY) (fun j => ht i j) hw
  rw [nl_util_eq, nl_util_eq, hwY, Function.update_eq_self] at h1
  rw [hp, ← nl_pay_eq_price htr ht i]
  exact h1

lemma nl_load_le_makespan {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n)
    (m : Fin n) : load t x m ≤ makespan t x := le_sup' _ (mem_univ m)

lemma nl_makespan_le {n k : ℕ} [NeZero n] (t : Fin n → Fin k → ℝ) (x : Fin k → Fin n) (B : ℝ)
    (h : ∀ m, load t x m ≤ B) : makespan t x ≤ B := sup'_le _ _ (fun m _ => h m)

lemma nl_term_le_load {n k : ℕ} (t : Fin n → Fin k → ℝ) (ht : IsType t) (x : Fin k → Fin n)
    (j : Fin k) : t (x j) j ≤ load t x (x j) := by
  unfold load
  exact single_le_sum (f := fun j' => t (x j) j') (fun j' _ => (ht _ _).le) (by simp)

lemma nl_force_off {n k : ℕ} [NeZero n] {c : ℝ} (hc : 0 ≤ c)
    {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)} (hap : IsApprox c alloc)
    {t : Fin n → Fin k → ℝ} (ht : IsType t) {i l0 : Fin n} (hl0 : l0 ≠ i)
    {S : Finset (Fin k)} {lam M : ℝ} (hlam : 0 ≤ lam) (hl : ∀ j, t l0 j ≤ lam)
    (hM : ∀ j, j ∉ S → M ≤ t i j) (hMl : c * (k * lam) < M) :
    agentSet alloc t i ⊆ S := by
  intro j hj
  by_contra hjS
  have hj' : alloc t j = i := by simpa [agentSet] using hj
  have h1 := nl_term_le_load t ht (alloc t) j
  rw [hj'] at h1
  have h2 := nl_load_le_makespan t (alloc t) i
  have h3 := hap t ht (fun _ => l0)
  have h4 : makespan t (fun _ => l0) ≤ k * lam := by
    apply nl_makespan_le; intro m
    unfold load
    by_cases hm : m = l0
    · subst hm
      have := Finset.sum_le_card_nsmul univ (fun j => t m j) lam (fun j _ => hl j)
      simpa using this
    · have : univ.filter (fun _ : Fin k => l0 = m) = ∅ := by
        ext x; simp [Ne.symm hm]
      rw [this, sum_empty]; positivity
  have h5 := mul_le_mul_of_nonneg_left h4 hc
  have := hM j hjS
  linarith

lemma nl_params (n k : ℕ) (c B : ℝ) (hc1 : 1 ≤ c) (hcn : c < n) (hk : 1 ≤ k) (hB : 0 ≤ B) :
    ∃ lam a ε M : ℝ, 0 < ε ∧ B < ε ∧ ε ≤ a ∧ a < lam ∧ ε < lam ∧ c * (k * ε) < lam ∧
      c * (k * lam) < M ∧ c * (lam + k * ε) < a * n := by
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hn : (0:ℝ) < n := by linarith
  set ε : ℝ := B + 1 with hε
  have hε0 : 0 < ε := by linarith
  set d : ℝ := (n:ℝ) - c with hd
  have hd0 : 0 < d := by linarith
  set q : ℝ := 2 * c * k * ε / d with hq
  have hqd : q * d = 2 * c * k * ε := by rw [hq]; field_simp
  have hq0 : 0 ≤ q := by positivity
  have hck : 0 < c * k * ε := by positivity
  set lam : ℝ := 2 * ε + q + c * k * ε + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  refine ⟨lam, lam * (c + n) / (2 * n), ε, c * (k * lam) + 1, hε0, by linarith, ?_, ?_, ?_, ?_,
    by linarith, ?_⟩
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · linarith
  · have : c * (k * ε) = c * k * ε := by ring
    linarith
  · have hrw : lam * (c + n) / (2 * n) * n = lam * (c + n) / 2 := by field_simp
    rw [hrw]
    have h1 : lam * d = (2 * ε + c * k * ε + 1) * d + q * d := by rw [hlam]; ring
    have h2 : 0 < (2 * ε + c * k * ε + 1) * d := by positivity
    nlinarith

theorem nl_core (n k : ℕ) [NeZero n] (hk : n ^ 2 ≤ k) (c : ℝ)
    (hc : c < n) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hloc : IsLocal alloc pay) : ¬ IsApprox c alloc := by
  intro hap
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hk1 : 1 ≤ k := le_trans (Nat.one_le_pow _ _ hn1) hk
  have hc1 : 1 ≤ c := by
    by_contra h; push_neg at h
    let t1 : Fin n → Fin k → ℝ := fun _ _ => 1
    have ht1 : IsType t1 := fun _ _ => one_pos
    have h3 := hap t1 ht1 (alloc t1)
    have h4 := nl_term_le_load t1 ht1 (alloc t1) ⟨0, hk1⟩
    have h5 := nl_load_le_makespan t1 (alloc t1) (alloc t1 ⟨0, hk1⟩)
    have h6 : t1 (alloc t1 ⟨0, hk1⟩) ⟨0, hk1⟩ = 1 := rfl
    nlinarith
  have hn2 : 2 ≤ n := by
    have : (1:ℝ) < n := by linarith
    exact_mod_cast this
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
  have hc0 : (0:ℝ) ≤ c := by linarith
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
  let C : Fin n → ℝ := fun i => price alloc pay i ∅ (fun _ _ => 1)
  have hC : ∀ i (t : Fin n → Fin k → ℝ), IsType t → price alloc pay i ∅ t = C i :=
    fun i t ht => hloc i ∅ t _ ht (fun _ _ => one_pos) (fun l _ j hj => by simp at hj)
  obtain ⟨lam, a, ε, M, hε0, hBε, hεa, halam, hεlam, hP3, hP4, hP5⟩ :=
    nl_params n k c (∑ i, |C i|) hc1 hc hk1 (by positivity)
  have hCε : ∀ i, 0 < C i + ε := by
    intro i
    have h1 : |C i| ≤ ∑ i, |C i| :=
      single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (mem_univ i)
    have := neg_abs_le (C i)
    linarith
  have hlam0 : 0 < lam := by linarith
  have hMl : lam < M := by
    have h1 : (1:ℝ) ≤ c * k := by nlinarith
    nlinarith
  let T0 : Fin n → Fin k → ℝ := fun _ _ => lam
  have hT0 : IsType T0 := fun _ _ => hlam0
  obtain ⟨i, hi⟩ : ∃ i, n ≤ (agentSet alloc T0 i).card := by
    by_contra h; push_neg at h
    have hsum : k = ∑ i, (agentSet alloc T0 i).card := by
      have := Finset.card_eq_sum_card_fiberwise (f := alloc T0) (s := univ) (t := univ)
        (fun _ _ => mem_univ _)
      simpa [agentSet] using this
    have h2 : ∑ i : Fin n, (agentSet alloc T0 i).card < ∑ i : Fin n, n :=
      sum_lt_sum_of_nonempty univ_nonempty (fun i _ => h i)
    simp at h2
    nlinarith
  set X := agentSet alloc T0 i with hXdef
  obtain ⟨X0, hX0X, hX0c⟩ := exists_subset_card_eq hi
  obtain ⟨l0, hl0⟩ := exists_ne i
  let S : Fin n → Fin k → ℝ := fun _ j => if j ∈ X then lam else ε
  let τ : Fin k → ℝ := fun j => if j ∈ X0 then a else if j ∈ X then ε else M
  have hτpos : ∀ j, 0 < τ j := by
    intro j; simp only [τ]; split_ifs <;> linarith
  let F := Function.update S i τ
  have hFi : F i = τ := by simp [F]
  have hFl : ∀ l, l ≠ i → F l = S l := fun l hl => by simp [F, hl]
  have hF : IsType F := by
    intro l j
    by_cases hl : l = i
    · rw [hl, hFi]; exact hτpos j
    · rw [hFl l hl]; simp only [S]; split_ifs <;> linarith
  have hlocX : ∀ Y, Y ⊆ X → price alloc pay i Y F = price alloc pay i Y T0 :=
    fun Y hY => hloc i Y F T0 hF hT0 (fun l hl j hj => by rw [hFl l hl]; simp [S, T0, hY hj])
  set Z := agentSet alloc F i with hZdef
  have hZX : Z ⊆ X := by
    apply nl_force_off hc0 hap hF hl0 (S := X) (lam := lam) (M := M) hlam0.le
    · intro j; rw [hFl l0 hl0]; simp only [S]; split_ifs <;> linarith
    · intro j hj; rw [hFi]; simp only [τ]
      rw [if_neg (fun h => hj (hX0X h)), if_neg hj]
    · exact hP4
  have hempty_att : ∀ t : Fin n → Fin k → ℝ, IsType t → (∀ j, t l0 j ≤ lam) →
      IsAttainable alloc i ∅ t := by
    intro t ht hl
    refine ⟨fun _ => M, fun _ => by linarith, ?_⟩
    apply Finset.subset_empty.mp
    apply nl_force_off hc0 hap (t := Function.update t i (fun _ => M)) ?_ hl0 (S := ∅)
      hlam0.le ?_ ?_ hP4
    · intro l j
      by_cases hl' : l = i
      · rw [hl']; simp; linarith
      · simp [hl']; exact ht l j
    · intro j; simp [hl0]; exact hl j
    · intro j _; simp
  have hmenu0 := nl_menu htr hF i (hempty_att F hF (fun j => by
    rw [hFl l0 hl0]; simp only [S]; split_ifs <;> linarith))
  rw [hC i F hF] at hmenu0
  have hset0 : setTime (F i) ∅ = 0 := by simp [setTime]
  rw [hset0, hFi, ← hZdef] at hmenu0
  have hZatt : IsAttainable alloc i Z T0 := by
    by_cases hZe : Z = ∅
    · rw [hZe]; exact hempty_att T0 hT0 (fun _ => le_rfl)
    · obtain ⟨j0, hj0⟩ := nonempty_iff_ne_empty.mpr hZe
      have hst : ε ≤ setTime τ Z := by
        have h1 : τ j0 ≤ setTime τ Z :=
          single_le_sum (f := τ) (fun j _ => (hτpos j).le) hj0
        have h2 : ε ≤ τ j0 := by
          have := hZX hj0
          simp only [τ]; split_ifs <;> linarith
        linarith
      have hpos : 0 < price alloc pay i Z T0 := by
        rw [← hlocX Z hZX]; have := hCε i; linarith
      by_contra hna
      have : price alloc pay i Z T0 = 0 := by unfold price; rw [dif_neg hna]
      linarith
  have hXatt : IsAttainable alloc i X F := by
    let w : Fin k → ℝ := fun j => if j ∈ X then ε else M
    refine ⟨w, fun j => by simp only [w]; split_ifs <;> linarith, ?_⟩
    have hGi : Function.update F i w i = w := by simp
    have hGl : ∀ l, l ≠ i → Function.update F i w l = S l := fun l hl => by
      rw [Function.update_of_ne hl, hFl l hl]
    have hG : IsType (Function.update F i w) := by
      intro l j
      by_cases hl : l = i
      · rw [hl, hGi]; simp only [w]; split_ifs <;> linarith
      · rw [hGl l hl]; simp only [S]; split_ifs <;> linarith
    apply Subset.antisymm
    · apply nl_force_off hc0 hap hG hl0 (S := X) (lam := lam) (M := M) hlam0.le
      · intro j; rw [hGl l0 hl0]; simp only [S]; split_ifs <;> linarith
      · intro j hj; rw [hGi]; simp only [w]; rw [if_neg hj]
      · exact hP4
    · intro j hj
      by_contra hnot
      have hj' : alloc (Function.update F i w) j ≠ i := by
        intro h; apply hnot; simp [agentSet, h]
      have h1 := nl_term_le_load _ hG (alloc (Function.update F i w)) j
      have h2 := nl_load_le_makespan (Function.update F i w) (alloc (Function.update F i w))
        (alloc (Function.update F i w) j)
      have hval : Function.update F i w (alloc (Function.update F i w) j) j = lam := by
        rw [hGl _ hj']; simp [S, hj]
      let y : Fin k → Fin n := fun j => if j ∈ X then i else l0
      have h3 := hap _ hG y
      have h4 : makespan (Function.update F i w) y ≤ k * ε := by
        apply nl_makespan_le; intro m; unfold load
        calc ∑ j ∈ univ.filter (fun j => y j = m), Function.update F i w m j
            ≤ ∑ j ∈ univ.filter (fun j => y j = m), ε := by
              apply sum_le_sum; intro j hj
              simp only [mem_filter, mem_univ, true_and] at hj
              by_cases hjX : j ∈ X
              · have : m = i := by rw [← hj]; simp [y, hjX]
                rw [this, hGi]; simp [w, hjX]
              · have : m = l0 := by rw [← hj]; simp [y, hjX]
                rw [this, hGl l0 hl0]; simp [S, hjX]
          _ = (univ.filter (fun j => y j = m)).card * ε := by rw [sum_const, nsmul_eq_mul]
          _ ≤ k * ε := by
              apply mul_le_mul_of_nonneg_right _ hε0.le
              have := card_filter_le (univ : Finset (Fin k)) (fun j => y j = m)
              simp at this; exact_mod_cast this
      have h5 := mul_le_mul_of_nonneg_left h4 hc0
      linarith
  have hpayF := nl_menu htr hF i hXatt
  have hpayT := nl_menu htr hT0 i hZatt
  rw [hFi, hlocX X subset_rfl, ← hZdef, hlocX Z hZX] at hpayF
  have hZeq : Z = X := by
    by_contra hne
    have hsd : (X \ Z).Nonempty := by
      rw [sdiff_nonempty]; intro h; exact hne (Subset.antisymm hZX h)
    have e1 : setTime τ X = setTime τ (X \ Z) + setTime τ Z := by
      unfold setTime; rw [sum_sdiff hZX]
    have e2 : setTime (T0 i) X = setTime (T0 i) (X \ Z) + setTime (T0 i) Z := by
      unfold setTime; rw [sum_sdiff hZX]
    have e3 : setTime τ (X \ Z) < setTime (T0 i) (X \ Z) := by
      unfold setTime; apply sum_lt_sum_of_nonempty hsd; intro j hj
      have hjX := (mem_sdiff.mp hj).1
      simp only [τ, T0]; split_ifs <;> linarith
    linarith
  have hload : a * n ≤ makespan F (alloc F) := by
    have h1 := nl_load_le_makespan F (alloc F) i
    have h2 : load F (alloc F) i = setTime τ X := by
      rw [← hZeq, hZdef, ← hFi]; rfl
    have h3 : ∑ j ∈ X0, τ j ≤ setTime τ X :=
      sum_le_sum_of_subset_of_nonneg hX0X (fun j _ _ => (hτpos j).le)
    have h4 : ∑ j ∈ X0, τ j = a * n := by
      rw [sum_congr rfl (fun j hj => by simp [τ, hj] : ∀ j ∈ X0, τ j = a)]
      simp [hX0c]; ring
    linarith
  let e : X0 ≃ Fin n := X0.equivFin.trans (finCongr hX0c)
  let y2 : Fin k → Fin n := fun j => if h : j ∈ X0 then e ⟨j, h⟩ else if j ∈ X then i else l0
  have hopt : makespan F y2 ≤ lam + k * ε := by
    apply nl_makespan_le; intro m; unfold load
    have hb : ∀ j ∈ univ.filter (fun j => y2 j = m),
        F m j ≤ (if j ∈ X0 then lam else 0) + ε := by
      intro j hj; simp only [mem_filter, mem_univ, true_and] at hj
      by_cases h0 : j ∈ X0
      · rw [if_pos h0]
        have : F m j ≤ lam := by
          by_cases hm : m = i
          · rw [hm, hFi]; simp only [τ, if_pos h0]; linarith
          · rw [hFl m hm]; simp [S, hX0X h0]
        linarith
      · rw [if_neg h0]
        by_cases hjX : j ∈ X
        · have : m = i := by rw [← hj]; simp [y2, h0, hjX]
          rw [this, hFi]; simp [τ, h0, hjX]
        · have : m = l0 := by rw [← hj]; simp [y2, h0, hjX]
          rw [this, hFl l0 hl0]; simp [S, hjX]
    calc _ ≤ ∑ j ∈ univ.filter (fun j => y2 j = m), ((if j ∈ X0 then lam else 0) + ε) :=
          sum_le_sum hb
      _ = ∑ j ∈ univ.filter (fun j => y2 j = m), (if j ∈ X0 then lam else 0)
            + (univ.filter (fun j => y2 j = m)).card * ε := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ lam + k * ε := by
          have hA : ∑ j ∈ univ.filter (fun j => y2 j = m), (if j ∈ X0 then lam else 0) ≤ lam := by
            rw [← sum_filter, sum_const, nsmul_eq_mul]
            have hc1' : ((univ.filter (fun j => y2 j = m)).filter (fun j => j ∈ X0)).card ≤ 1 := by
              apply card_le_one.mpr
              intro a1 ha1 b1 hb1
              simp only [mem_filter, mem_univ, true_and] at ha1 hb1
              have ea : y2 a1 = e ⟨a1, ha1.2⟩ := by simp [y2, ha1.2]
              have eb : y2 b1 = e ⟨b1, hb1.2⟩ := by simp [y2, hb1.2]
              have hee : e ⟨a1, ha1.2⟩ = e ⟨b1, hb1.2⟩ := by rw [← ea, ← eb, ha1.1, hb1.1]
              exact congrArg Subtype.val (e.injective hee)
            have : (((univ.filter (fun j => y2 j = m)).filter (fun j => j ∈ X0)).card : ℝ) ≤ 1 := by
              exact_mod_cast hc1'
            nlinarith
          have hB : ((univ.filter (fun j => y2 j = m)).card : ℝ) * ε ≤ k * ε := by
            apply mul_le_mul_of_nonneg_right _ hε0.le
            have := card_filter_le (univ : Finset (Fin k)) (fun j => y2 j = m)
            simp at this; exact_mod_cast this
          linarith
  have h1 := hap F hF y2
  have h2 := mul_le_mul_of_nonneg_left hopt hc0
  linarith

end AlgMechDesign.Local

open AlgMechDesign.Local


theorem solution (n k : ℕ) [NeZero n] (hk : n ^ 2 ≤ k) (c : ℝ)
    (hc : c < n) (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hloc : IsLocal alloc pay) : ¬ IsApprox c alloc := by
  exact nl_core n k hk c hc alloc pay htr hloc
