-- Prove2me | solution 1 for AKSSorting.Core.expander_exists
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:50:38.530433+00:00
-- url     : https://prove2.me/submissions/6816c67b-1dab-45ef-8531-8b7e0ad08912

import Mathlib
import Definitions.Def_AKSSorting_Core_IsExpander



namespace AKSSorting.Core
open Classical



noncomputable def nbf {V : Type} (G : SimpleGraph V) (S X : Finset V) : Finset V :=
  S.filter (fun v => ∃ x ∈ X, G.Adj x v)

lemma neighbours_ncard {V : Type} (G : SimpleGraph V) (S X : Finset V)
    (h : neighbours G X ⊆ ↑S) :
    (neighbours G X).ncard = (nbf G S X).card := by
  have : neighbours G X = ↑(nbf G S X) := by
    ext v
    simp only [nbf, neighbours, Set.mem_setOf_eq, Finset.coe_filter]
    constructor
    · intro hv; exact ⟨h hv, hv⟩
    · intro hv; exact hv.2
  rw [this, Set.ncard_coe_finset]

lemma mk_expander {V : Type} (G : SimpleGraph V) (A B : Finset V) (k : ℕ) (ε : ℝ)
    (hd : Disjoint A B) (he : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (hk : ∀ v, (G.neighborSet v).encard ≤ (k : ℕ∞))
    (hX : ∀ X ⊆ A, X.Nonempty →
      (1 - ε) * (1 / ε) * min (X.card : ℝ) (ε * B.card) < ((nbf G B X).card : ℝ))
    (hY : ∀ Y ⊆ B, Y.Nonempty →
      (1 - ε) * (1 / ε) * min (Y.card : ℝ) (ε * A.card) < ((nbf G A Y).card : ℝ)) :
    IsExpander G A B k ε := by
  refine ⟨hd, he, hk, ?_, ?_⟩
  · intro X hXA hne
    rw [neighbours_ncard G B X ?_]
    · exact hX X hXA hne
    · intro v hv
      obtain ⟨x, hx, hadj⟩ := hv
      rcases he x v hadj with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd h (Finset.disjoint_left.mp hd (hXA hx))
  · intro Y hYB hne
    rw [neighbours_ncard G A Y ?_]
    · exact hY Y hYB hne
    · intro v hv
      obtain ⟨x, hx, hadj⟩ := hv
      rcases he x v hadj with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd (hYB hx) (Finset.disjoint_left.mp hd h)
      · exact h

lemma expander_X {V : Type} {G : SimpleGraph V} {A B : Finset V} {k : ℕ} {ε : ℝ}
    (h : IsExpander G A B k ε) {X : Finset V} (hXA : X ⊆ A) (hne : X.Nonempty) :
    (1 - ε) * (1 / ε) * min (X.card : ℝ) (ε * B.card) < ((nbf G B X).card : ℝ) := by
  obtain ⟨hd, he, _, h4, _⟩ := h
  have := h4 X hXA hne
  rwa [neighbours_ncard G B X] at this
  intro v hv
  obtain ⟨x, hx, hadj⟩ := hv
  rcases he x v hadj with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h (Finset.disjoint_left.mp hd (hXA hx))

lemma expander_Y {V : Type} {G : SimpleGraph V} {A B : Finset V} {k : ℕ} {ε : ℝ}
    (h : IsExpander G A B k ε) {Y : Finset V} (hYB : Y ⊆ B) (hne : Y.Nonempty) :
    (1 - ε) * (1 / ε) * min (Y.card : ℝ) (ε * A.card) < ((nbf G A Y).card : ℝ) := by
  obtain ⟨hd, he, _, _, h5⟩ := h
  have := h5 Y hYB hne
  rwa [neighbours_ncard G A Y] at this
  intro v hv
  obtain ⟨x, hx, hadj⟩ := hv
  rcases he x v hadj with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd (hYB hx) (Finset.disjoint_left.mp hd h)
  · exact h

lemma expander_symm {V : Type} {G : SimpleGraph V} {A B : Finset V} {k : ℕ} {ε : ℝ}
    (h : IsExpander G A B k ε) : IsExpander G B A k ε := by
  obtain ⟨hd, he, hk, h4, h5⟩ := h
  exact ⟨hd.symm, fun u v huv => (he u v huv).symm, hk, h5, h4⟩




section Counting
variable {α β : Type} [Fintype α] [Fintype β]

lemma card_preimage_equiv (π : α ≃ β) (T : Finset β) :
    (Finset.univ.filter (fun w : α => π w ∈ T)).card = T.card := by
  have : (Finset.univ.filter (fun w : α => π w ∈ T)).map π.toEmbedding = T := by
    ext b
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ha
    · intro hb; exact ⟨π.symm b, by simpa using hb, by simp⟩
  calc _ = ((Finset.univ.filter (fun w : α => π w ∈ T)).map π.toEmbedding).card :=
        (Finset.card_map _).symm
    _ = T.card := by rw [this]

lemma step_count (hcard : Fintype.card α = Fintype.card β) (X : Finset α) (a : α)
    (ha : a ∉ X) (T : Finset β) :
    Fintype.card β * (Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ insert a X, φ z ∈ T)).card ≤
      T.card * (Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ X, φ z ∈ T)).card := by
  set P := Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ X, φ z ∈ T) with hP
  set Q := Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ insert a X, φ z ∈ T) with hQ
  have hQP : Q ⊆ P := by
    intro φ hφ
    simp only [hQ, hP, Finset.mem_filter, Finset.mem_univ, true_and] at hφ ⊢
    intro z hz; exact hφ z (Finset.mem_insert_of_mem hz)
  have hxn : X.card ≤ Fintype.card β := by
    rw [← hcard]; exact Finset.card_le_univ X
  by_cases hxt : X.card ≤ T.card
  · -- main double counting
    have h1 : (Q.sigma (fun _ => (Finset.univ.filter (fun w : α => w ∉ X)))).card ≤
        (P.sigma (fun π => (Finset.univ.filter (fun w : α => w ∉ X ∧ π w ∈ T)))).card := by
      apply Finset.card_le_card_of_injOn
        (fun p => (⟨(Equiv.swap a p.2).trans p.1, p.2⟩ : (_ : α ≃ β) × α))
      · intro p hp
        simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.coe_filter,
          Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
        obtain ⟨hpQ, hpw⟩ := hp
        simp only [hQ, hP, Finset.mem_filter, Finset.mem_univ, true_and] at hpQ ⊢
        refine ⟨?_, hpw, ?_⟩
        · intro z hz
          have hza : z ≠ a := fun h => ha (h ▸ hz)
          have hzw : z ≠ p.2 := fun h => hpw (h ▸ hz)
          simp [Equiv.swap_apply_of_ne_of_ne hza hzw]
          exact hpQ z (Finset.mem_insert_of_mem hz)
        · simp
          exact hpQ a (Finset.mem_insert_self a X)
      · intro p hp q hq hpq
        simp only [Sigma.mk.injEq] at hpq
        obtain ⟨h1, h2⟩ := hpq
        have h2' : p.2 = q.2 := by simpa using h2
        obtain ⟨p1, p2⟩ := p
        obtain ⟨q1, q2⟩ := q
        simp only at h2'
        subst h2'
        have : p1 = q1 := by
          ext z
          have := congrArg (fun e : α ≃ β => e ((Equiv.swap a p2) z)) h1
          simpa using this
        subst this
        rfl
    rw [Finset.card_sigma, Finset.card_sigma] at h1
    simp only [Finset.sum_const, smul_eq_mul] at h1
    have h3 : (Finset.univ.filter (fun w : α => w ∉ X)).card = Fintype.card β - X.card := by
      rw [← hcard, Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp
    have h4 : ∀ π ∈ P, (Finset.univ.filter (fun w : α => w ∉ X ∧ π w ∈ T)).card =
        T.card - X.card := by
      intro π hπ
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      have : (Finset.univ.filter (fun w : α => w ∉ X ∧ π w ∈ T)) =
          (Finset.univ.filter (fun w : α => π w ∈ T)) \ X := by
        ext w; simp [and_comm]
      rw [this, Finset.card_sdiff_of_subset, card_preimage_equiv]
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hπ z hz
    rw [Finset.sum_congr rfl h4] at h1
    simp only [Finset.sum_const, smul_eq_mul, h3] at h1
    -- h1 : Q.card * (n - x) ≤ P.card * (t - x)
    have hQP' := Finset.card_le_card hQP
    obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hxn
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hxt
    rw [hu, hv] at h1
    rw [hu, hv]
    simp only [Nat.add_sub_cancel_left] at h1
    nlinarith
  · -- P is empty
    push_neg at hxt
    have hPe : P = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro φ hφ
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hφ
      have : X.card ≤ T.card := by
        apply Finset.card_le_card_of_injOn φ
        · intro z hz; exact hφ z hz
        · intro z _ z' _ h; exact φ.injective h
      omega
    have hQe : Q = ∅ := Finset.subset_empty.mp (hPe ▸ hQP)
    rw [hQe]; simp

lemma count_bound (hcard : Fintype.card α = Fintype.card β) (X : Finset α) (T : Finset β) :
    (Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ X, φ z ∈ T)).card * Fintype.card β ^ X.card ≤
      Fintype.card (α ≃ β) * T.card ^ X.card := by
  induction X using Finset.induction_on with
  | empty => simp
  | insert a X ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ, pow_succ]
    have := step_count hcard X a ha T
    calc _ = (Fintype.card β * (Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ insert a X, φ z ∈ T)).card)
          * Fintype.card β ^ X.card := by ring
      _ ≤ (T.card * (Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ X, φ z ∈ T)).card)
          * Fintype.card β ^ X.card := Nat.mul_le_mul_right _ this
      _ = T.card * ((Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ X, φ z ∈ T)).card
          * Fintype.card β ^ X.card) := by ring
      _ ≤ T.card * (Fintype.card (α ≃ β) * T.card ^ X.card) := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

lemma tuple_count (hcard : Fintype.card α = Fintype.card β) (d : ℕ) (X : Finset α)
    (T : Finset β) :
    (Finset.univ.filter (fun φ : Fin d → (α ≃ β) => ∀ j, ∀ z ∈ X, φ j z ∈ T)).card *
        (Fintype.card β ^ X.card) ^ d ≤
      Fintype.card (α ≃ β) ^ d * (T.card ^ X.card) ^ d := by
  have h1 : (Finset.univ.filter (fun φ : Fin d → (α ≃ β) => ∀ j, ∀ z ∈ X, φ j z ∈ T)) =
      Fintype.piFinset (fun _ : Fin d =>
        Finset.univ.filter (fun φ : α ≃ β => ∀ z ∈ X, φ z ∈ T)) := by
    ext φ; simp [Fintype.mem_piFinset]
  rw [h1, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_pow, ← mul_pow]
  exact Nat.pow_le_pow_left (count_bound hcard X T) d

end Counting



lemma binom_le (n x : ℕ) (hx : 1 ≤ x) :
    (n.choose x : ℝ) ≤ (Real.exp 1 * n / x) ^ x := by
  have h1 := Nat.choose_le_pow_div (α := ℝ) x n
  have h2 := Real.pow_div_factorial_le_exp (x : ℝ) (Nat.cast_nonneg x) x
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hf : (0 : ℝ) < (x.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos x
  calc (n.choose x : ℝ) ≤ (n : ℝ) ^ x / x.factorial := h1
    _ = ((n : ℝ) / x) ^ x * ((x : ℝ) ^ x / x.factorial) := by
        rw [div_pow]; field_simp
    _ ≤ ((n : ℝ) / x) ^ x * Real.exp x := by
        apply mul_le_mul_of_nonneg_left h2
        positivity
    _ = (Real.exp 1 * n / x) ^ x := by
        rw [show Real.exp (x : ℝ) = (Real.exp 1) ^ x by
          rw [← Real.exp_nat_mul]; simp, ← mul_pow]
        congr 1; ring

lemma term_bound (M k n x : ℕ) (θ : ℝ) (hM : 1 ≤ M) (hx : 1 ≤ x) (hn : 0 < n)
    (hθ : 0 ≤ θ) (hq : ((M * x : ℕ) : ℝ) / n ≤ θ) :
    (n.choose x : ℝ) * (n.choose (M * x) : ℝ) * (((M * x : ℕ) : ℝ) / n) ^ (x * (M + 1 + k)) ≤
      (Real.exp 1 ^ (M + 1) * M * θ ^ k) ^ x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have htpos : 1 ≤ M * x := Nat.one_le_iff_ne_zero.mpr (by positivity)
  set q : ℝ := ((M * x : ℕ) : ℝ) / n with hqdef
  have hqpos : 0 < q := by
    rw [hqdef]; have : (0:ℝ) < ((M * x : ℕ) : ℝ) := by exact_mod_cast htpos
    positivity
  set r : ℝ := Real.exp 1 * n / x with hr
  have hrq : r = Real.exp 1 * M / q := by
    rw [hr, hqdef]; push_cast; field_simp
  have hC1 := binom_le n x hx
  have hC2 := binom_le n (M * x) htpos
  have hr2 : Real.exp 1 * n / ((M * x : ℕ) : ℝ) = r / M := by
    rw [hr]; push_cast; field_simp
  rw [hr2] at hC2
  have hexp : (r / M) ^ (M * x) = ((r / M) ^ M) ^ x := by rw [← pow_mul]
  have hq' : q ^ (x * (M + 1 + k)) = (q ^ (M + 1 + k)) ^ x := by rw [← pow_mul, mul_comm]
  have hprod : (n.choose x : ℝ) * (n.choose (M * x) : ℝ) * q ^ (x * (M + 1 + k)) ≤
      (r * (r / M) ^ M * q ^ (M + 1 + k)) ^ x := by
    rw [hq', mul_pow, mul_pow, ← hexp]
    apply mul_le_mul (mul_le_mul hC1 hC2 (by positivity) (by positivity)) le_rfl (by positivity)
      (by positivity)
  have hval : r * (r / M) ^ M * q ^ (M + 1 + k) = Real.exp 1 ^ (M + 1) * M * q ^ k := by
    have h1 : Real.exp 1 * M / q / M = Real.exp 1 / q := by field_simp
    rw [hrq, h1, div_pow, pow_add, pow_add, pow_succ]
    field_simp
    ring
  rw [hval] at hprod
  refine hprod.trans ?_
  apply pow_le_pow_left₀ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ hqpos.le hq k


section Prob
variable {α β : Type} [Fintype α] [Fintype β]

noncomputable def UU {d : ℕ} (φ : Fin d → (α ≃ β)) (X : Finset α) : Finset β :=
  Finset.univ.biUnion (fun j => X.image (φ j))

def Good {d : ℕ} (M m : ℕ) (φ : Fin d → (α ≃ β)) : Prop :=
  ∀ X : Finset α, X.Nonempty → X.card ≤ m → M * X.card < (UU φ X).card

lemma mem_UU {d : ℕ} (φ : Fin d → (α ≃ β)) (X : Finset α) (j : Fin d) (z : α) (hz : z ∈ X) :
    φ j z ∈ UU φ X := by
  simp only [UU, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  exact ⟨j, z, hz, rfl⟩

lemma geom_le (ρ : ℝ) (m : ℕ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1 / 8) :
    ∑ x ∈ Finset.Icc 1 m, ρ ^ x ≤ 1 / 7 := by
  have : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]
  rw [this]
  refine (geom_sum_Ico_le_of_lt_one h0 (by linarith)).trans ?_
  rw [pow_one, div_le_iff₀ (by linarith)]
  linarith

lemma aux_div (c F K n : ℝ) (x d : ℕ) (hn : 0 < n)
    (h : c * (n ^ x) ^ d ≤ F * (K ^ x) ^ d) : c ≤ F * (K / n) ^ (x * d) := by
  rw [pow_mul, div_pow, div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact h

lemma bad_le (M k : ℕ) (hM : 1 ≤ M) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hρ : Real.exp 1 ^ (M + 1) * M * θ ^ k ≤ 1 / 8)
    (hcard : Fintype.card α = Fintype.card β) (n m : ℕ) (hn : Fintype.card β = n) (hn0 : 0 < n)
    (hm : ∀ x, 1 ≤ x → x ≤ m → ((M * x : ℕ) : ℝ) / n ≤ θ) :
    ((Finset.univ.filter (fun φ : Fin (M + 1 + k) → (α ≃ β) => ¬ Good M m φ)).card : ℝ) * 7 ≤
      (Fintype.card (α ≃ β) : ℝ) ^ (M + 1 + k) := by
  set d := M + 1 + k with hd
  set F : ℝ := (Fintype.card (α ≃ β) : ℝ) with hF
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hMn : ∀ x, 1 ≤ x → x ≤ m → M * x ≤ n := by
    intro x hx1 hxm
    have := hm x hx1 hxm
    rw [div_le_iff₀ hnR] at this
    have h2 : ((M * x : ℕ) : ℝ) ≤ n := by nlinarith
    exact_mod_cast h2
  let Bs : ℕ → Finset α → Finset β → Finset (Fin d → (α ≃ β)) := fun _ X T =>
    Finset.univ.filter (fun φ : Fin d → (α ≃ β) => ∀ j, ∀ z ∈ X, φ j z ∈ T)
  have hsub : Finset.univ.filter (fun φ : Fin d → (α ≃ β) => ¬ Good M m φ) ⊆
      (Finset.Icc 1 m).biUnion (fun x => (Finset.powersetCard x (Finset.univ : Finset α)).biUnion
        (fun X => (Finset.powersetCard (M * x) (Finset.univ : Finset β)).biUnion
          (fun T => Bs x X T))) := by
    intro φ hφ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Good, not_forall] at hφ
    obtain ⟨X, hXne, hXm, hlt⟩ := hφ
    have hx1 : 1 ≤ X.card := Finset.card_pos.mpr hXne
    have hle : (UU φ X).card ≤ M * X.card := not_lt.mp hlt
    have hMnx := hMn X.card hx1 hXm
    obtain ⟨T, hUT, -, hTc⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (UU φ X)) hle (by rw [Finset.card_univ, hn]; exact hMnx)
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard, Finset.mem_univ,
      Finset.subset_univ, true_and, Bs, Finset.mem_filter]
    refine ⟨X.card, ⟨hx1, hXm⟩, X, rfl, T, hTc, fun j z hz => hUT (mem_UU φ X j z hz)⟩
  have hcb : ((Finset.univ.filter (fun φ : Fin d → (α ≃ β) => ¬ Good M m φ)).card : ℝ) ≤
      ∑ x ∈ Finset.Icc 1 m, ∑ X ∈ Finset.powersetCard x (Finset.univ : Finset α),
        ∑ T ∈ Finset.powersetCard (M * x) (Finset.univ : Finset β), ((Bs x X T).card : ℝ) := by
    have hnat : (Finset.univ.filter (fun φ : Fin d → (α ≃ β) => ¬ Good M m φ)).card ≤
        ∑ x ∈ Finset.Icc 1 m, ∑ X ∈ Finset.powersetCard x (Finset.univ : Finset α),
          ∑ T ∈ Finset.powersetCard (M * x) (Finset.univ : Finset β), (Bs x X T).card := by
      refine (Finset.card_le_card hsub).trans ?_
      refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun x _ => ?_)
      refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun X _ => ?_)
      exact Finset.card_biUnion_le
    exact_mod_cast hnat
  -- bound each term
  have hterm : ∀ x ∈ Finset.Icc 1 m, ∑ X ∈ Finset.powersetCard x (Finset.univ : Finset α),
        ∑ T ∈ Finset.powersetCard (M * x) (Finset.univ : Finset β), ((Bs x X T).card : ℝ) ≤
      F ^ d * (Real.exp 1 ^ (M + 1) * M * θ ^ k) ^ x := by
    intro x hxI
    rw [Finset.mem_Icc] at hxI
    obtain ⟨hx1, hxm⟩ := hxI
    have hq := hm x hx1 hxm
    have hcount : ∀ X ∈ Finset.powersetCard x (Finset.univ : Finset α),
        ∀ T ∈ Finset.powersetCard (M * x) (Finset.univ : Finset β),
        ((Bs x X T).card : ℝ) ≤ F ^ d * (((M * x : ℕ) : ℝ) / n) ^ (x * d) := by
      intro X hX T hT
      rw [Finset.mem_powersetCard] at hX hT
      have := tuple_count hcard d X T
      rw [hX.2, hT.2, hn] at this
      have h' := (Nat.cast_le (α := ℝ)).mpr this
      simp only [Nat.cast_mul, Nat.cast_pow] at h'
      push_cast
      exact aux_div _ _ _ _ x d hnR h'
    calc _ ≤ ∑ X ∈ Finset.powersetCard x (Finset.univ : Finset α),
          ∑ T ∈ Finset.powersetCard (M * x) (Finset.univ : Finset β),
            F ^ d * (((M * x : ℕ) : ℝ) / n) ^ (x * d) := by
          apply Finset.sum_le_sum; intro X hX
          apply Finset.sum_le_sum; intro T hT
          exact hcount X hX T hT
      _ = (n.choose x : ℝ) * (n.choose (M * x) : ℝ) *
            (F ^ d * (((M * x : ℕ) : ℝ) / n) ^ (x * d)) := by
          simp only [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, hn, hcard,
            nsmul_eq_mul]
          ring
      _ = F ^ d * ((n.choose x : ℝ) * (n.choose (M * x) : ℝ) *
            (((M * x : ℕ) : ℝ) / n) ^ (x * d)) := by ring
      _ ≤ F ^ d * (Real.exp 1 ^ (M + 1) * M * θ ^ k) ^ x := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact term_bound M k n x θ hM hx1 hn0 hθ0 hq
  have hFpos : 0 ≤ F ^ d := by positivity
  have hρ0 : 0 ≤ Real.exp 1 ^ (M + 1) * M * θ ^ k := by positivity
  calc _ ≤ (∑ x ∈ Finset.Icc 1 m, F ^ d * (Real.exp 1 ^ (M + 1) * M * θ ^ k) ^ x) * 7 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        exact hcb.trans (Finset.sum_le_sum hterm)
    _ = F ^ d * (∑ x ∈ Finset.Icc 1 m, (Real.exp 1 ^ (M + 1) * M * θ ^ k) ^ x) * 7 := by
        rw [← Finset.mul_sum]
    _ ≤ F ^ d * (1 / 7) * 7 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left (geom_le _ m hρ0 hρ) hFpos
    _ = F ^ d := by ring

end Prob

section ExistsGood

lemma ceil_bound (M n : ℕ) (hM : 1 ≤ M) (hn : 2 * (M + 1) ^ 2 ≤ n) (x : ℕ)
    (hx : x ≤ ⌈(n : ℝ) / (M + 1)⌉₊) :
    ((M * x : ℕ) : ℝ) / n ≤ 1 - 1 / (2 * ((M : ℝ) + 1)) := by
  have hNpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hnR : (2 : ℝ) * ((M : ℝ) + 1) ^ 2 ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by nlinarith [sq_nonneg ((M : ℝ) + 1)]
  have hu : (n : ℝ) / (M + 1) < (n : ℝ) / (M + 1) + 1 := by linarith
  have hc := Nat.ceil_lt_add_one (a := (n : ℝ) / (M + 1)) (by positivity)
  have hxR : (x : ℝ) < (n : ℝ) / (M + 1) + 1 := by
    have : (x : ℝ) ≤ (⌈(n : ℝ) / (M + 1)⌉₊ : ℝ) := by exact_mod_cast hx
    linarith
  rw [div_le_iff₀ hnpos]
  push_cast
  have hMR : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h2 : (M : ℝ) * x ≤ M * ((n : ℝ) / (M + 1) + 1) :=
    mul_le_mul_of_nonneg_left hxR.le hMR
  refine h2.trans ?_
  have h3 : (2 : ℝ) * M * ((M : ℝ) + 1) ≤ n := by nlinarith
  have : (M : ℝ) * ((n : ℝ) / (M + 1) + 1) ≤ (1 - 1 / (2 * ((M : ℝ) + 1))) * n := by
    rw [show (M : ℝ) * ((n : ℝ) / (M + 1) + 1) = M * n / (M + 1) + M by field_simp]
    rw [show (1 - 1 / (2 * ((M : ℝ) + 1))) * n = n - n / (2 * (M + 1)) by field_simp]
    rw [← sub_nonneg]
    have : (n : ℝ) - n / (2 * (M + 1)) - (M * n / (M + 1) + M) =
        (n - 2 * M * (M + 1)) / (2 * (M + 1)) := by field_simp; ring
    rw [this]
    apply div_nonneg (by linarith) (by positivity)
  exact this

lemma exists_good (M : ℕ) (hM : 1 ≤ M) :
    ∃ d n0 : ℕ, ∀ (α β : Type) [Fintype α] [Fintype β], Fintype.card α = Fintype.card β →
      n0 ≤ Fintype.card β →
      ∃ φ : Fin d → (α ≃ β),
        Good M ⌈(Fintype.card β : ℝ) / (M + 1)⌉₊ φ ∧
        Good M ⌈(Fintype.card β : ℝ) / (M + 1)⌉₊ (fun j => (φ j).symm) := by
  set θ : ℝ := 1 - 1 / (2 * ((M : ℝ) + 1)) with hθ
  have hθ1 : θ < 1 := by rw [hθ]; have : (0:ℝ) < 1 / (2 * ((M : ℝ) + 1)) := by positivity
                         linarith
  have hθ0 : 0 ≤ θ := by
    rw [hθ, sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hEpos : 0 < Real.exp 1 ^ (M + 1) * M := by
    have : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (x := 1 / (8 * (Real.exp 1 ^ (M + 1) * M)))
    (y := θ) (by positivity) hθ1
  have hρ : Real.exp 1 ^ (M + 1) * M * θ ^ k ≤ 1 / 8 := by
    calc Real.exp 1 ^ (M + 1) * M * θ ^ k ≤ Real.exp 1 ^ (M + 1) * M *
          (1 / (8 * (Real.exp 1 ^ (M + 1) * M))) := mul_le_mul_of_nonneg_left hk.le hEpos.le
      _ = 1 / 8 := by field_simp
  refine ⟨M + 1 + k, 2 * (M + 1) ^ 2, ?_⟩
  intro α β _ _ hcard hn0
  set n := Fintype.card β with hn
  have hn0' : 0 < n := by nlinarith [sq_nonneg (M + 1)]
  have hmain : ∀ (γ δ : Type) [Fintype γ] [Fintype δ], Fintype.card γ = Fintype.card δ →
      Fintype.card δ = n →
      ((Finset.univ.filter (fun φ : Fin (M + 1 + k) → (γ ≃ δ) =>
        ¬ Good M ⌈(n : ℝ) / (M + 1)⌉₊ φ)).card : ℝ) * 7 ≤
        (Fintype.card (γ ≃ δ) : ℝ) ^ (M + 1 + k) := by
    intro γ δ _ _ h1 h2
    exact bad_le M k hM θ hθ0 hθ1 hρ h1 n _ h2 hn0'
      (fun x _ hx => ceil_bound M n hM hn0 x hx)
  have hB1 := hmain α β hcard hn.symm
  have hB2 := hmain β α hcard.symm hcard
  have hF : Fintype.card (β ≃ α) = Fintype.card (α ≃ β) :=
    Fintype.card_congr ⟨Equiv.symm, Equiv.symm, fun e => e.symm_symm, fun e => e.symm_symm⟩
  rw [hF] at hB2
  set d := M + 1 + k with hd
  set Bad1 := Finset.univ.filter (fun φ : Fin d → (α ≃ β) => ¬ Good M ⌈(n : ℝ) / (M + 1)⌉₊ φ)
    with hBad1
  set Bad2 := Finset.univ.filter (fun φ : Fin d → (α ≃ β) =>
    ¬ Good M ⌈(n : ℝ) / (M + 1)⌉₊ (fun j => (φ j).symm)) with hBad2
  set Bad' := Finset.univ.filter (fun φ : Fin d → (β ≃ α) => ¬ Good M ⌈(n : ℝ) / (M + 1)⌉₊ φ)
    with hBad'
  have hinj : Bad2.card ≤ Bad'.card := by
    apply Finset.card_le_card_of_injOn (fun φ j => (φ j).symm)
    · intro φ hφ
      simpa [hBad2, hBad'] using hφ
    · intro φ _ ψ _ h
      funext j
      simpa using congrArg Equiv.symm (congrFun h j)
  haveI : Nonempty (α ≃ β) := ⟨Fintype.equivOfCardEq hcard⟩
  have hFpos : (0 : ℝ) < (Fintype.card (α ≃ β) : ℝ) ^ d := by
    have : 0 < Fintype.card (α ≃ β) := Fintype.card_pos
    positivity
  by_contra hcon
  have hsub : (Finset.univ : Finset (Fin d → (α ≃ β))) ⊆ Bad1 ∪ Bad2 := by
    intro φ _
    by_cases h1 : Good M ⌈(n : ℝ) / (M + 1)⌉₊ φ
    · by_cases h2 : Good M ⌈(n : ℝ) / (M + 1)⌉₊ (fun j => (φ j).symm)
      · exact absurd ⟨φ, h1, h2⟩ hcon
      · exact Finset.mem_union_right _ (by simp [hBad2, h2])
    · exact Finset.mem_union_left _ (by simp [hBad1, h1])
  have hc1 := Finset.card_le_card hsub
  have hc2 := (Finset.card_union_le Bad1 Bad2).trans (Nat.add_le_add_left hinj _)
  have hcu : (Finset.univ : Finset (Fin d → (α ≃ β))).card = Fintype.card (α ≃ β) ^ d := by
    simp [Finset.card_univ, Fintype.card_fun]
  rw [hcu] at hc1
  have h3 : (Fintype.card (α ≃ β) : ℝ) ^ d ≤ (Bad1.card : ℝ) + Bad'.card := by
    have := hc1.trans hc2
    exact_mod_cast this
  linarith

end ExistsGood

section Base

lemma coef_eq (M : ℕ) : (1 - 1 / ((M : ℝ) + 1)) * (1 / (1 / ((M : ℝ) + 1))) = M := by
  have : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  field_simp
  ring

lemma good_expands {α β : Type} [Fintype α] [Fintype β] {d : ℕ} (M n : ℕ)
    (φ : Fin d → (α ≃ β)) (hφ : Good M ⌈(n : ℝ) / (M + 1)⌉₊ φ)
    (hn : 0 < n) (hcard : Fintype.card α = n) (X : Finset α) (hX : X.Nonempty) :
    (M : ℝ) * min (X.card : ℝ) ((n : ℝ) / (M + 1)) < (UU φ X).card := by
  have hNpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hxm : X.card ≤ ⌈(n : ℝ) / (M + 1)⌉₊
  · have := hφ X hX hxm
    have h2 : (M : ℝ) * (X.card : ℝ) < (UU φ X).card := by exact_mod_cast this
    calc _ ≤ (M : ℝ) * X.card := mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg M)
      _ < _ := h2
  · push_neg at hxm
    obtain ⟨X0, hX0, hX0c⟩ := Finset.exists_subset_card_eq hxm.le
    have hm1 : 0 < ⌈(n : ℝ) / (M + 1)⌉₊ := Nat.ceil_pos.mpr (by positivity)
    have hne : X0.Nonempty := Finset.card_pos.mp (by rw [hX0c]; exact hm1)
    have h1 := hφ X0 hne hX0c.le
    rw [hX0c] at h1
    have h2 : (M : ℝ) * (⌈(n : ℝ) / (M + 1)⌉₊ : ℝ) < (UU φ X0).card := by exact_mod_cast h1
    have h3 : (UU φ X0).card ≤ (UU φ X).card := by
      apply Finset.card_le_card
      intro b hb
      simp only [UU, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hb ⊢
      obtain ⟨j, z, hz, rfl⟩ := hb
      exact ⟨j, z, hX0 hz, rfl⟩
    have h4 : (UU φ X0).card ≤ ((UU φ X).card : ℝ) := by exact_mod_cast h3
    calc _ ≤ (M : ℝ) * ((n : ℝ) / (M + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg M)
      _ ≤ (M : ℝ) * (⌈(n : ℝ) / (M + 1)⌉₊ : ℝ) :=
          mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg M)
      _ < _ := by linarith

/-- complete bipartite graph. -/
lemma complete_expander {V : Type} (M n0 : ℕ) (A B : Finset V) (hd : Disjoint A B)
    (hAB : A.card = B.card) (hn : A.card < n0) (k : ℕ) (hk : 2 * n0 ≤ k) :
    ∃ G : SimpleGraph V, IsExpander G A B k (1 / ((M : ℝ) + 1)) := by
  let G : SimpleGraph V := SimpleGraph.fromRel (fun u v => u ∈ A ∧ v ∈ B)
  have hadj : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u v h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2, h.1⟩
  have hNpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  refine ⟨G, mk_expander G A B k _ hd hadj ?_ ?_ ?_⟩
  · intro w
    have hsub : G.neighborSet w ⊆ ↑(A ∪ B) := by
      intro v hv
      have := hadj w v hv
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      rcases this with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inr h
      · exact Or.inl h
    refine (Set.encard_le_encard hsub).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard]
    have : (A ∪ B).card ≤ k := by
      calc _ ≤ A.card + B.card := Finset.card_union_le _ _
        _ ≤ k := by omega
    exact_mod_cast this
  · intro X hXA hXne
    have hnb : nbf G B X = B := by
      ext v
      simp only [nbf, Finset.mem_filter, and_iff_left_iff_imp]
      intro hv
      obtain ⟨x, hx⟩ := hXne
      refine ⟨x, hx, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨hXA hx, hv⟩⟩
      rintro rfl
      exact Finset.disjoint_left.mp hd (hXA hx) hv
    rw [hnb, coef_eq]
    have hBpos : (0 : ℝ) < B.card := by
      have : 0 < B.card := by
        rw [← hAB]; exact lt_of_lt_of_le hXne.card_pos (Finset.card_le_card hXA)
      exact_mod_cast this
    calc _ ≤ (M : ℝ) * (1 / ((M : ℝ) + 1) * B.card) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg M)
      _ < B.card := by
          rw [show (M : ℝ) * (1 / ((M : ℝ) + 1) * B.card) = (M / ((M : ℝ) + 1)) * B.card by ring]
          have : (M : ℝ) / ((M : ℝ) + 1) < 1 := by
            rw [div_lt_one hNpos]; linarith
          nlinarith
  · intro Y hYB hYne
    have hnb : nbf G A Y = A := by
      ext v
      simp only [nbf, Finset.mem_filter, and_iff_left_iff_imp]
      intro hv
      obtain ⟨x, hx⟩ := hYne
      refine ⟨x, hx, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inr ⟨hv, hYB hx⟩⟩
      rintro rfl
      exact Finset.disjoint_left.mp hd hv (hYB hx)
    rw [hnb, coef_eq]
    have hApos : (0 : ℝ) < A.card := by
      have : 0 < A.card := by
        rw [hAB]; exact lt_of_lt_of_le hYne.card_pos (Finset.card_le_card hYB)
      exact_mod_cast this
    calc _ ≤ (M : ℝ) * (1 / ((M : ℝ) + 1) * A.card) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg M)
      _ < A.card := by
          rw [show (M : ℝ) * (1 / ((M : ℝ) + 1) * A.card) = (M / ((M : ℝ) + 1)) * A.card by ring]
          have : (M : ℝ) / ((M : ℝ) + 1) < 1 := by
            rw [div_lt_one hNpos]; linarith
          nlinarith

end Base

section PermGraph

lemma subtype_card {V : Type} (A X : Finset V) (hXA : X ⊆ A) :
    (X.subtype (· ∈ A)).card = X.card := by
  rw [Finset.card_subtype, Finset.filter_true_of_mem (fun x hx => hXA hx)]

lemma perm_expander {V : Type} (M d : ℕ) (A B : Finset V) (hd : Disjoint A B)
    (hAB : A.card = B.card) (hpos : 0 < A.card)
    (φ : Fin d → ({x // x ∈ A} ≃ {x // x ∈ B}))
    (h1 : Good M ⌈(A.card : ℝ) / (M + 1)⌉₊ φ)
    (h2 : Good M ⌈(A.card : ℝ) / (M + 1)⌉₊ (fun j => (φ j).symm))
    (k : ℕ) (hk : 2 * d ≤ k) :
    ∃ G : SimpleGraph V, IsExpander G A B k (1 / ((M : ℝ) + 1)) := by
  let R : V → V → Prop := fun u v => ∃ j : Fin d, ∃ hu : u ∈ A, (((φ j) ⟨u, hu⟩ : {x // x ∈ B}) : V) = v
  have hR : ∀ u v, R u v → u ∈ A ∧ v ∈ B := by
    rintro u v ⟨j, hu, rfl⟩
    exact ⟨hu, (φ j ⟨u, hu⟩).2⟩
  let G : SimpleGraph V := SimpleGraph.fromRel R
  have hadj : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u v h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with h | h
    · exact Or.inl (hR u v h)
    · exact Or.inr ⟨(hR v u h).2, (hR v u h).1⟩
  have hNpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hcA : Fintype.card {x // x ∈ A} = A.card := Fintype.card_coe A
  have hcB : Fintype.card {x // x ∈ B} = A.card := by rw [Fintype.card_coe, hAB]
  refine ⟨G, mk_expander G A B k _ hd hadj ?_ ?_ ?_⟩
  · intro w
    let S1 : Finset V := Finset.univ.image (fun j : Fin d =>
      if h : w ∈ A then (((φ j) ⟨w, h⟩ : {x // x ∈ B}) : V) else w)
    let S2 : Finset V := Finset.univ.image (fun j : Fin d =>
      if h : w ∈ B then ((((φ j).symm) ⟨w, h⟩ : {x // x ∈ A}) : V) else w)
    have hsub : G.neighborSet w ⊆ ↑(S1 ∪ S2) := by
      intro v hv
      rw [SimpleGraph.mem_neighborSet, SimpleGraph.fromRel_adj] at hv
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      rcases hv.2 with ⟨j, hu, hjv⟩ | ⟨j, hv', hjw⟩
      · left
        simp only [S1, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨j, by simp [hu, hjv]⟩
      · right
        have hwB : w ∈ B := by rw [← hjw]; exact (φ j ⟨v, hv'⟩).2
        simp only [S2, Finset.mem_image, Finset.mem_univ, true_and]
        refine ⟨j, ?_⟩
        simp only [hwB, dite_true]
        have : (φ j).symm ⟨w, hwB⟩ = ⟨v, hv'⟩ := by
          rw [Equiv.symm_apply_eq]; ext; exact hjw.symm
        rw [this]
    refine (Set.encard_le_encard hsub).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard]
    have : (S1 ∪ S2).card ≤ k := by
      calc _ ≤ S1.card + S2.card := Finset.card_union_le _ _
        _ ≤ d + d := Nat.add_le_add
            ((Finset.card_image_le).trans (by simp)) ((Finset.card_image_le).trans (by simp))
        _ ≤ k := by omega
    exact_mod_cast this
  · intro X hXA hXne
    have hX' : (X.subtype (· ∈ A)).Nonempty := by
      rw [← Finset.card_pos, subtype_card A X hXA]; exact hXne.card_pos
    have key := good_expands M A.card (fun j => φ j) h1 hpos hcA _ hX'
    rw [subtype_card A X hXA] at key
    have hB : (B.card : ℝ) = A.card := by exact_mod_cast hAB.symm
    have hsub : ((UU φ (X.subtype (· ∈ A))).map (Function.Embedding.subtype _)) ⊆ nbf G B X := by
      intro b hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨b', hb', rfl⟩ := hb
      simp only [UU, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hb'
      obtain ⟨j, ⟨x, hxA⟩, hx, rfl⟩ := hb'
      simp only [Finset.mem_subtype] at hx
      simp only [nbf, Finset.mem_filter]
      refine ⟨(φ j ⟨x, hxA⟩).2, x, hx, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl ⟨j, hxA, rfl⟩⟩
      rintro h
      have hb := (φ j ⟨x, hxA⟩).2
      rw [← h] at hb
      exact Finset.disjoint_left.mp hd hxA hb
    have := Finset.card_le_card hsub
    rw [Finset.card_map] at this
    rw [coef_eq, hB, one_div_mul_eq_div]
    exact lt_of_lt_of_le key (by exact_mod_cast this)
  · intro Y hYB hYne
    have hY' : (Y.subtype (· ∈ B)).Nonempty := by
      rw [← Finset.card_pos, subtype_card B Y hYB]; exact hYne.card_pos
    have key := good_expands M A.card (fun j => (φ j).symm) h2 hpos hcB _ hY'
    rw [subtype_card B Y hYB] at key
    have hsub : ((UU (fun j => (φ j).symm) (Y.subtype (· ∈ B))).map
        (Function.Embedding.subtype _)) ⊆ nbf G A Y := by
      intro a hb
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hb
      obtain ⟨a', hb', rfl⟩ := hb
      simp only [UU, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hb'
      obtain ⟨j, ⟨y, hyB⟩, hy, rfl⟩ := hb'
      simp only [Finset.mem_subtype] at hy
      simp only [nbf, Finset.mem_filter]
      refine ⟨((φ j).symm ⟨y, hyB⟩).2, y, hy, ?_⟩
      rw [SimpleGraph.fromRel_adj]
      have hya := ((φ j).symm ⟨y, hyB⟩).2
      refine ⟨?_, Or.inr ⟨j, hya, ?_⟩⟩
      · rintro h
        rw [h] at hyB
        exact Finset.disjoint_left.mp hd hya hyB
      · simp
    have := Finset.card_le_card hsub
    rw [Finset.card_map] at this
    rw [coef_eq, one_div_mul_eq_div]
    exact lt_of_lt_of_le key (by exact_mod_cast this)

end PermGraph

lemma base_expander (M : ℕ) (hM : 1 ≤ M) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ ∀ (V : Type) (A B : Finset V), Disjoint A B → A.card = B.card →
      ∃ G : SimpleGraph V, IsExpander G A B k₀ (1 / ((M : ℝ) + 1)) := by
  obtain ⟨d, n0, hgood⟩ := exists_good M hM
  refine ⟨2 * d + 2 * (n0 + 1) + 1, by omega, ?_⟩
  intro V A B hd hAB
  by_cases hlt : A.card < n0 + 1
  · exact complete_expander M (n0 + 1) A B hd hAB hlt _ (by omega)
  · push_neg at hlt
    have hcA : Fintype.card {x // x ∈ A} = Fintype.card {x // x ∈ B} := by
      rw [Fintype.card_coe, Fintype.card_coe, hAB]
    have hn : n0 ≤ Fintype.card {x // x ∈ B} := by
      rw [Fintype.card_coe, ← hAB]; omega
    obtain ⟨φ, h1, h2⟩ := hgood {x // x ∈ A} {x // x ∈ B} hcA hn
    rw [Fintype.card_coe, ← hAB] at h1 h2
    exact perm_expander M d A B hd hAB (by omega) φ h1 h2 _ (by omega)

section Cover

lemma cover_blocks {V : Type} (B : Finset V) (a : ℕ) (haB : a ≤ B.card) :
    ∀ (q : ℕ) (R : Finset V), R ⊆ B → R.card ≤ q * a →
      ∃ F : Finset (Finset V), F.card ≤ q ∧ (∀ S ∈ F, S ⊆ B ∧ S.card = a) ∧
        ∀ y ∈ R, ∃ S ∈ F, y ∈ S := by
  intro q
  induction q with
  | zero =>
    intro R hRB hRc
    refine ⟨∅, by simp, by simp, ?_⟩
    have : R = ∅ := Finset.card_eq_zero.mp (by simpa using hRc)
    simp [this]
  | succ q ih =>
    intro R hRB hRc
    by_cases hRa : R.card < a
    · obtain ⟨S, hRS, hSB, hSc⟩ := Finset.exists_subsuperset_card_eq hRB hRa.le haB
      refine ⟨{S}, by simp, by simpa using ⟨hSB, hSc⟩, ?_⟩
      intro y hy; exact ⟨S, by simp, hRS hy⟩
    · push_neg at hRa
      obtain ⟨S, hSR, hSc⟩ := Finset.exists_subset_card_eq hRa
      have hRc' : (R \ S).card ≤ q * a := by
        rw [Finset.card_sdiff_of_subset hSR, hSc]
        have : (q + 1) * a = q * a + a := by ring
        omega
      obtain ⟨F, hFc, hFS, hFcov⟩ := ih (R \ S) (Finset.sdiff_subset.trans hRB) hRc'
      by_cases hSF : S ∈ F
      · refine ⟨F, by omega, hFS, ?_⟩
        intro y hy
        by_cases hyS : y ∈ S
        · exact ⟨S, hSF, hyS⟩
        · exact hFcov y (Finset.mem_sdiff.mpr ⟨hy, hyS⟩)
      · refine ⟨insert S F, ?_, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hSF]; omega
        · intro T hT
          rcases Finset.mem_insert.mp hT with rfl | hT
          · exact ⟨hSR.trans hRB, hSc⟩
          · exact hFS T hT
        · intro y hy
          by_cases hyS : y ∈ S
          · exact ⟨S, Finset.mem_insert_self _ _, hyS⟩
          · obtain ⟨T, hT, hyT⟩ := hFcov y (Finset.mem_sdiff.mpr ⟨hy, hyS⟩)
            exact ⟨T, Finset.mem_insert_of_mem hT, hyT⟩

end Cover

section Union

lemma encard_union_nbrs {V : Type} (Gf : Finset V → SimpleGraph V) (k₀ : ℕ) (w : V) :
    ∀ F' : Finset (Finset V), (∀ S ∈ F', ((Gf S).neighborSet w).encard ≤ (k₀ : ℕ∞)) →
      {v | ∃ S ∈ F', (Gf S).Adj w v}.encard ≤ ((F'.card * k₀ : ℕ) : ℕ∞) := by
  intro F'
  induction F' using Finset.induction_on with
  | empty => intro _; simp
  | insert S F' hS ih =>
    intro h
    have h1 := h S (Finset.mem_insert_self _ _)
    have h2 := ih (fun T hT => h T (Finset.mem_insert_of_mem hT))
    have hsub : {v | ∃ T ∈ insert S F', (Gf T).Adj w v} ⊆
        (Gf S).neighborSet w ∪ {v | ∃ T ∈ F', (Gf T).Adj w v} := by
      intro v hv
      obtain ⟨T, hT, hadj⟩ := hv
      rcases Finset.mem_insert.mp hT with rfl | hT
      · exact Or.inl hadj
      · exact Or.inr ⟨T, hT, hadj⟩
    refine (Set.encard_le_encard hsub).trans ((Set.encard_union_le _ _).trans ?_)
    rw [Finset.card_insert_of_notMem hS]
    have : (F'.card + 1) * k₀ = k₀ + F'.card * k₀ := by ring
    rw [this, Nat.cast_add]
    exact add_le_add h1 h2

lemma union_expander {V : Type} (A B : Finset V) (hd : Disjoint A B) (a q M k₀ : ℕ) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hq : 1 ≤ q) (ha : A.card = a) (haB : a ≤ B.card)
    (hBq : B.card ≤ q * a)
    (hMε : 2 * q * (1 / ((M : ℝ) + 1)) ≤ ε)
    (F : Finset (Finset V)) (hFne : F.Nonempty) (hFq : F.card ≤ q)
    (hFS : ∀ S ∈ F, S ⊆ B ∧ S.card = a)
    (hcov : ∀ y ∈ B, ∃ S ∈ F, y ∈ S)
    (Gf : Finset V → SimpleGraph V)
    (hG : ∀ S ∈ F, IsExpander (Gf S) A S k₀ (1 / ((M : ℝ) + 1))) :
    ∃ G : SimpleGraph V, IsExpander G A B (q * k₀) ε := by
  set e : ℝ := 1 / ((M : ℝ) + 1) with he
  have he0 : 0 < e := by rw [he]; positivity
  obtain ⟨G, hGadj⟩ : ∃ G : SimpleGraph V, ∀ u v, G.Adj u v ↔ ∃ S ∈ F, (Gf S).Adj u v := by
    refine ⟨SimpleGraph.fromRel (fun u v => ∃ S ∈ F, (Gf S).Adj u v), ?_⟩
    intro u v
    rw [SimpleGraph.fromRel_adj]
    constructor
    · rintro ⟨_, ⟨S, hS, h⟩ | ⟨S, hS, h⟩⟩
      · exact ⟨S, hS, h⟩
      · exact ⟨S, hS, h.symm⟩
    · rintro ⟨S, hS, h⟩
      exact ⟨h.ne, Or.inl ⟨S, hS, h⟩⟩
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hFqR : (F.card : ℝ) ≤ q := by exact_mod_cast hFq
  have hFpos : (1 : ℝ) ≤ F.card := by exact_mod_cast Finset.card_pos.mpr hFne
  have hqe : 2 * q * e ≤ ε := hMε
  have he_le : e ≤ ε / 2 := by nlinarith
  have he_half : e ≤ 1 / 2 := by linarith
  set c : ℝ := (1 - ε) * (1 / ε) with hc
  set l : ℝ := (1 - e) * (1 / e) with hl
  have hlm : l * e = 1 - e := by rw [hl]; field_simp
  have hcm : c * ε = 1 - ε := by rw [hc]; field_simp
  have hc0 : 0 ≤ c := by rw [hc]; apply mul_nonneg <;> [linarith; positivity]
  have hcq : c * q ≤ l := by
    rw [hc, hl]
    rw [show (1 - ε) * (1 / ε) * q = (1 - ε) * q / ε by ring,
        show (1 - e) * (1 / e) = (1 - e) / e by ring, div_le_div_iff₀ hε0 he0]
    nlinarith
  have hcl : c ≤ l := by nlinarith
  have hel : (a : ℝ) ≥ 0 := Nat.cast_nonneg a
  -- monotonicity of neighbourhoods
  have hmonoX : ∀ S ∈ F, ∀ X : Finset V, nbf (Gf S) S X ⊆ nbf G B X := by
    intro S hS X v hv
    simp only [nbf, Finset.mem_filter] at hv ⊢
    obtain ⟨hvS, x, hx, hadj⟩ := hv
    exact ⟨(hFS S hS).1 hvS, x, hx, (hGadj x v).mpr ⟨S, hS, hadj⟩⟩
  have hmonoY : ∀ S ∈ F, ∀ Y Y' : Finset V, Y' ⊆ Y → nbf (Gf S) A Y' ⊆ nbf G A Y := by
    intro S hS Y Y' hYY v hv
    simp only [nbf, Finset.mem_filter] at hv ⊢
    obtain ⟨hvA, x, hx, hadj⟩ := hv
    exact ⟨hvA, x, hYY hx, (hGadj x v).mpr ⟨S, hS, hadj⟩⟩
  refine ⟨G, mk_expander G A B (q * k₀) ε hd ?_ ?_ ?_ ?_⟩
  · intro u v h
    obtain ⟨S, hS, hadj⟩ := (hGadj u v).mp h
    rcases (hG S hS).2.1 u v hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, (hFS S hS).1 h2⟩
    · exact Or.inr ⟨(hFS S hS).1 h1, h2⟩
  · intro w
    have hset : G.neighborSet w = {v | ∃ S ∈ F, (Gf S).Adj w v} := by
      ext v
      simp only [SimpleGraph.mem_neighborSet, Set.mem_setOf_eq]
      exact hGadj w v
    rw [hset]
    refine (encard_union_nbrs Gf k₀ w F (fun S hS => (hG S hS).2.2.1 w)).trans ?_
    exact_mod_cast Nat.mul_le_mul_right k₀ hFq
  · -- X side
    intro X hXA hXne
    have hSX : ∀ S ∈ F, l * min (X.card : ℝ) (e * a) < (nbf (Gf S) S X).card := by
      intro S hS
      have := expander_X (hG S hS) hXA hXne
      rwa [(hFS S hS).2] at this
    obtain ⟨S0, hS0⟩ := hFne
    have hBa : (a : ℝ) ≤ B.card := by exact_mod_cast haB
    by_cases hsmall : (X.card : ℝ) ≤ e * a
    · have h1 := hSX S0 hS0
      rw [min_eq_left hsmall] at h1
      have h2 : ((nbf (Gf S0) S0 X).card : ℝ) ≤ (nbf G B X).card := by
        exact_mod_cast Finset.card_le_card (hmonoX S0 hS0 X)
      calc c * min (X.card : ℝ) (ε * B.card) ≤ c * X.card :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hc0
        _ ≤ l * X.card := mul_le_mul_of_nonneg_right hcl (Nat.cast_nonneg _)
        _ < _ := lt_of_lt_of_le h1 h2
    · push_neg at hsmall
      have hS' : ∀ S ∈ F, (a : ℝ) - e * a < (nbf (Gf S) S X).card := by
        intro S hS
        have h1 := hSX S hS
        rw [min_eq_right hsmall.le] at h1
        have : l * (e * a) = a - e * a := by rw [← mul_assoc, hlm]; ring
        linarith
      have hΓB : nbf G B X ⊆ B := Finset.filter_subset _ _
      have hsub : B \ nbf G B X ⊆ F.biUnion (fun S => S \ nbf (Gf S) S X) := by
        intro y hy
        rw [Finset.mem_sdiff] at hy
        obtain ⟨S, hS, hyS⟩ := hcov y hy.1
        simp only [Finset.mem_biUnion, Finset.mem_sdiff]
        exact ⟨S, hS, hyS, fun h => hy.2 (hmonoX S hS X h)⟩
      have hcard1 : (B \ nbf G B X).card ≤ ∑ S ∈ F, (S \ nbf (Gf S) S X).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      have hcard2 : ∀ S ∈ F, ((S \ nbf (Gf S) S X).card : ℝ) = a - (nbf (Gf S) S X).card := by
        intro S hS
        have hsubS : nbf (Gf S) S X ⊆ S := Finset.filter_subset _ _
        rw [Finset.card_sdiff_of_subset hsubS, Nat.cast_sub (Finset.card_le_card hsubS),
          (hFS S hS).2]
      have hsum : ∑ S ∈ F, ((S \ nbf (Gf S) S X).card : ℝ) < ∑ S ∈ F, (e * a) := by
        apply Finset.sum_lt_sum_of_nonempty ⟨S0, hS0⟩
        intro S hS
        rw [hcard2 S hS]
        linarith [hS' S hS]
      rw [Finset.sum_const, nsmul_eq_mul] at hsum
      have hcard1R : ((B \ nbf G B X).card : ℝ) ≤ ∑ S ∈ F, ((S \ nbf (Gf S) S X).card : ℝ) := by
        exact_mod_cast hcard1
      rw [Finset.card_sdiff_of_subset hΓB, Nat.cast_sub (Finset.card_le_card hΓB)] at hcard1R
      have hk1 : (F.card : ℝ) * (e * a) ≤ q * (e * a) :=
        mul_le_mul_of_nonneg_right hFqR (by positivity)
      have hk2 : (q : ℝ) * (e * a) ≤ ε / 2 * a := by nlinarith
      have hk3 : ε / 2 * a ≤ ε / 2 * B.card := mul_le_mul_of_nonneg_left hBa (by positivity)
      calc c * min (X.card : ℝ) (ε * B.card) ≤ c * (ε * B.card) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hc0
        _ = (1 - ε) * B.card := by rw [← mul_assoc, hcm]
        _ < (nbf G B X).card := by
            have ha1 : 1 ≤ a := by
              rw [← ha]; exact hXne.card_pos.trans_le (Finset.card_le_card hXA)
            have hBpos : (0 : ℝ) < B.card := by
              have : 0 < B.card := lt_of_lt_of_le ha1 haB
              exact_mod_cast this
            nlinarith
  · -- Y side
    intro Y hYB hYne
    have hex : ∃ S ∈ F, Y.card ≤ F.card * (Y.filter (· ∈ S)).card := by
      apply Finset.exists_le_of_sum_le hFne
      calc ∑ S ∈ F, Y.card = F.card * Y.card := by simp
        _ ≤ F.card * ∑ S ∈ F, (Y.filter (· ∈ S)).card := by
            apply Nat.mul_le_mul_left
            calc Y.card ≤ (F.biUnion (fun S => Y.filter (· ∈ S))).card := by
                  apply Finset.card_le_card
                  intro y hy
                  obtain ⟨S, hS, hyS⟩ := hcov y (hYB hy)
                  simp only [Finset.mem_biUnion, Finset.mem_filter]
                  exact ⟨S, hS, hy, hyS⟩
              _ ≤ _ := Finset.card_biUnion_le
        _ = ∑ S ∈ F, F.card * (Y.filter (· ∈ S)).card := by rw [Finset.mul_sum]
    obtain ⟨S, hS, hYS⟩ := hex
    set YS := Y.filter (· ∈ S) with hYSdef
    have hYSsub : YS ⊆ S := fun y hy => (Finset.mem_filter.mp hy).2
    have hYSY : YS ⊆ Y := Finset.filter_subset _ _
    have hYSne : YS.Nonempty := by
      rw [← Finset.card_pos]
      by_contra h0
      have : YS.card = 0 := by omega
      rw [this] at hYS
      have := hYne.card_pos
      omega
    have hY1 := expander_Y (hG S hS) hYSsub hYSne
    rw [ha] at hY1
    have hY2 : ((nbf (Gf S) A YS).card : ℝ) ≤ (nbf G A Y).card := by
      exact_mod_cast Finset.card_le_card (hmonoY S hS Y YS hYSY)
    have hYSR : (Y.card : ℝ) ≤ q * YS.card := by
      have : (Y.card : ℝ) ≤ F.card * YS.card := by exact_mod_cast hYS
      calc _ ≤ _ := this
        _ ≤ q * YS.card := mul_le_mul_of_nonneg_right hFqR (Nat.cast_nonneg _)
    have hAa : (A.card : ℝ) = a := by exact_mod_cast ha
    rw [hAa]
    by_cases hbig : e * a ≤ (YS.card : ℝ)
    · rw [min_eq_right hbig] at hY1
      have : l * (e * a) = a - e * a := by rw [← mul_assoc, hlm]; ring
      calc c * min (Y.card : ℝ) (ε * a) ≤ c * (ε * a) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hc0
        _ = (1 - ε) * a := by rw [← mul_assoc, hcm]
        _ ≤ a - e * a := by nlinarith
        _ < _ := by linarith
    · push_neg at hbig
      rw [min_eq_left hbig.le] at hY1
      calc c * min (Y.card : ℝ) (ε * a) ≤ c * Y.card :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hc0
        _ ≤ c * (q * YS.card) := mul_le_mul_of_nonneg_left hYSR hc0
        _ = (c * q) * YS.card := by ring
        _ ≤ l * YS.card := mul_le_mul_of_nonneg_right hcq (Nat.cast_nonneg _)
        _ < _ := lt_of_lt_of_le hY1 hY2

end Union

lemma unbal_expander (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (q M k₀ : ℕ) (hq : 1 ≤ q)
    (hMε : 2 * q * (1 / ((M : ℝ) + 1)) ≤ ε)
    (hbase : ∀ (V : Type) (A B : Finset V), Disjoint A B → A.card = B.card →
      ∃ G : SimpleGraph V, IsExpander G A B k₀ (1 / ((M : ℝ) + 1)))
    {V : Type} (A B : Finset V) (hd : Disjoint A B) (hab : A.card ≤ B.card)
    (hba : B.card ≤ q * A.card) :
    ∃ G : SimpleGraph V, IsExpander G A B (q * k₀) ε := by
  by_cases h0 : A.card = 0
  · have hA : A = ∅ := Finset.card_eq_zero.mp h0
    have hB : B.card = 0 := by rw [h0] at hba; simpa using hba
    have hB' : B = ∅ := Finset.card_eq_zero.mp hB
    refine ⟨⊥, mk_expander ⊥ A B _ ε hd (by simp) (by intro v; simp) ?_ ?_⟩
    · intro X hXA hXne
      exfalso; rw [hA] at hXA
      exact (Finset.nonempty_iff_ne_empty.mp hXne) (Finset.subset_empty.mp hXA)
    · intro Y hYB hYne
      exfalso; rw [hB'] at hYB
      exact (Finset.nonempty_iff_ne_empty.mp hYne) (Finset.subset_empty.mp hYB)
  · have ha1 : 0 < A.card := Nat.pos_of_ne_zero h0
    obtain ⟨F, hFq, hFS, hcov⟩ := cover_blocks B A.card hab q B (Finset.Subset.refl _) hba
    have hBne : B.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le ha1 hab)
    have hFne : F.Nonempty := by
      obtain ⟨y, hy⟩ := hBne
      obtain ⟨S, hS, _⟩ := hcov y hy
      exact ⟨S, hS⟩
    have hex : ∀ S : Finset V, ∃ G : SimpleGraph V, S ∈ F →
        IsExpander G A S k₀ (1 / ((M : ℝ) + 1)) := by
      intro S
      by_cases hS : S ∈ F
      · obtain ⟨G, hG⟩ := hbase V A S
          (Finset.disjoint_of_subset_right (hFS S hS).1 hd) (hFS S hS).2.symm
        exact ⟨G, fun _ => hG⟩
      · exact ⟨⊥, fun h => absurd h hS⟩
    choose Gf hGf using hex
    exact union_expander A B hd A.card q M k₀ ε hε0 hε1 hq rfl hab hba hMε F hFne hFq hFS hcov Gf
      hGf

theorem expander_core (ε c : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hc : 1 ≤ c) :
    ∃ k : ℕ, 0 < k ∧ ∀ (V : Type) (A B : Finset V), Disjoint A B →
      (A.card : ℝ) ≤ c * B.card → (B.card : ℝ) ≤ c * A.card →
      ∃ G : SimpleGraph V, IsExpander G A B k ε := by
  set q : ℕ := ⌈c⌉₊ with hq
  have hq1 : 1 ≤ q := Nat.one_le_ceil_iff.mpr (by linarith)
  have hqc : c ≤ q := Nat.le_ceil c
  set M : ℕ := max 1 ⌈2 * (q : ℝ) / ε⌉₊ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMε : 2 * q * (1 / ((M : ℝ) + 1)) ≤ ε := by
    have h1 : 2 * (q : ℝ) / ε ≤ M := by
      calc 2 * (q : ℝ) / ε ≤ ⌈2 * (q : ℝ) / ε⌉₊ := Nat.le_ceil _
        _ ≤ M := Nat.cast_le.mpr (by rw [hM]; exact le_max_right _ _)
    rw [div_le_iff₀ hε₀] at h1
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_iff₀ hpos]
    nlinarith
  obtain ⟨k₀, hk0, hbase⟩ := base_expander M hM1
  refine ⟨q * k₀, Nat.mul_pos (by omega) hk0, ?_⟩
  intro V A B hd hAB hBA
  by_cases hle : A.card ≤ B.card
  · have : B.card ≤ q * A.card := by
      have h1 : (B.card : ℝ) ≤ q * A.card :=
        hBA.trans (mul_le_mul_of_nonneg_right hqc (Nat.cast_nonneg _))
      exact_mod_cast h1
    exact unbal_expander ε hε₀ hε₁ q M k₀ hq1 hMε hbase A B hd hle this
  · push_neg at hle
    have : A.card ≤ q * B.card := by
      have h1 : (A.card : ℝ) ≤ q * B.card :=
        hAB.trans (mul_le_mul_of_nonneg_right hqc (Nat.cast_nonneg _))
      exact_mod_cast h1
    obtain ⟨G, hG⟩ := unbal_expander ε hε₀ hε₁ q M k₀ hq1 hMε hbase B A hd.symm hle.le this
    exact ⟨G, expander_symm hG⟩


end AKSSorting.Core

open AKSSorting.Core


theorem solution (ε c : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1) (hc : 1 ≤ c) :
    ∃ k : ℕ, 0 < k ∧ ∀ (V : Type) (A B : Finset V), Disjoint A B →
      (A.card : ℝ) ≤ c * B.card → (B.card : ℝ) ≤ c * A.card →
      ∃ G : SimpleGraph V, IsExpander G A B k ε := by
  exact expander_core ε c hε₀ hε₁ hc
