-- Prove2me | solution 1 for AdaptSubCover.Rounds.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:13:44.014125+00:00
-- url     : https://prove2.me/submissions/bdd239bf-c714-4456-8906-35319e1e386d

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_ParCA
import Theorems.Thm_AdaptSubCover_Rounds_lemma_3_3

open AdaptSubCover.Rounds

namespace ASCT31

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-! ### Probability bookkeeping -/

theorem prob_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (ω : Fin m → U) :
    0 ≤ I.prob ω := Finset.prod_nonneg fun i _ => hp0 i (ω i)

theorem sum_prob (I : Instance U m) (hp1 : ∀ i, ∑ u, I.p i u = 1) :
    ∑ ω, I.prob ω = 1 := by
  unfold Instance.prob
  rw [← Fintype.prod_sum (fun i u => I.p i u)]
  simp [hp1]

/-- Expectations are monotone on the support. -/
theorem E_mono (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F G : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 < I.prob ω → F ω ≤ G ω) : I.E F ≤ I.E G := by
  unfold Instance.E
  apply Finset.sum_le_sum
  intro ω _
  rcases (prob_nonneg I hp0 ω).lt_or_eq with hp | hp
  · exact mul_le_mul_of_nonneg_left (h ω hp) hp.le
  · rw [← hp]; simp

/-! ### Executions of rounds and adaptive policies -/

theorem go_prefix (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U), h <+: Round.go stop ω L h
  | [], h => by simp [Round.go]
  | i :: L, h => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact List.prefix_refl _
    · exact go_prefix stop ω L h
    · exact (List.prefix_append h _).trans (go_prefix stop ω L _)

theorem items_mono {h h' : History m U} (hp : h <+: h') : h.items ⊆ h'.items := by
  obtain ⟨t, rfl⟩ := hp
  intro x hx
  simp only [History.items, List.map_append, List.toFinset_append, Finset.mem_union] at hx ⊢
  exact Or.inl hx

/-- A round either ends because its stopping rule fires, or it has probed every listed item. -/
theorem go_stop_or_all (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U),
      stop (Round.go stop ω L h) = true ∨ ∀ x ∈ L, x ∈ (Round.go stop ω L h).items
  | [], h => by simp [Round.go]
  | i :: L, h => by
    by_cases hs : stop h = true
    · left; simp [Round.go, hs]
    · have hs' : stop h = false := by simpa using hs
      by_cases hm : i ∈ h.items
      · have e : Round.go stop ω (i :: L) h = Round.go stop ω L h := by
          simp [Round.go, hs', hm]
        rw [e]
        rcases go_stop_or_all stop ω L h with h1 | h1
        · exact Or.inl h1
        · right
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact items_mono (go_prefix stop ω L h) hm
          · exact h1 x hx
      · have e : Round.go stop ω (i :: L) h = Round.go stop ω L (h ++ [(i, ω i)]) := by
          simp [Round.go, hs', hm]
        rw [e]
        rcases go_stop_or_all stop ω L (h ++ [(i, ω i)]) with h1 | h1
        · exact Or.inl h1
        · right
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · apply items_mono (go_prefix stop ω L _)
            simp [History.items]
          · exact h1 x hx

/-- Histories produced by executions record true realizations. -/
def Honest (ω : Fin m → U) (h : History m U) : Prop := ∀ p ∈ h, p.2 = ω p.1

theorem go_honest (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U), Honest ω h → Honest ω (Round.go stop ω L h)
  | [], h, hh => by simpa [Round.go] using hh
  | i :: L, h, hh => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact hh
    · exact go_honest stop ω L h hh
    · apply go_honest stop ω L
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hh p hp
      · simp at hp; subst hp; rfl

theorem run_honest (π : AdaptivePolicy m U) (ω : Fin m → U) : Honest ω (π.run ω) := by
  unfold AdaptivePolicy.run
  suffices ∀ n (h : History m U), Honest ω h → Honest ω ((π.step ω)^[n] h) from
    this m [] (by simp [Honest])
  intro n
  induction n with
  | zero => intro h hh; simpa using hh
  | succ n ih =>
    intro h hh
    rw [Function.iterate_succ_apply]
    apply ih
    unfold AdaptivePolicy.step
    split
    · split_ifs
      · exact hh
      · intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hh p hp
        · simp at hp; subst hp; rfl
    · exact hh

theorem realized_eq (ω : Fin m → U) (h : History m U) (hh : Honest ω h) :
    h.realized = h.items.image ω := by
  ext u
  simp only [History.realized, History.items, List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, ⟨p, hp, rfl⟩, (hh p hp).symm⟩
  · rintro ⟨i, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, hh p hp⟩

end ASCT31

namespace ASCT31

/-! ### Pointwise dyadic bounds -/

theorem geom_two (N : ℕ) : ∑ i ∈ Finset.range N, (2 : ℝ) ^ i = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

/-- `X ≤ α + α Σ_{i<N} 2^i 1[α 2^i ≤ X]` whenever `0 ≤ X < α 2^N`. -/
theorem upper_pt (α X : ℝ) (hα : 0 < α) (hX : 0 ≤ X) (ind : ℕ → ℝ)
    (hind1 : ∀ i, α * 2 ^ i ≤ X → ind i = 1) (hind0 : ∀ i, ¬ α * 2 ^ i ≤ X → ind i = 0) :
    ∀ N : ℕ, X < α * 2 ^ N → X ≤ α + α * ∑ i ∈ Finset.range N, 2 ^ i * ind i := by
  have hnn : ∀ i, 0 ≤ ind i := by
    intro i; by_cases h : α * 2 ^ i ≤ X
    · rw [hind1 i h]; norm_num
    · rw [hind0 i h]
  intro N
  induction N with
  | zero => intro h; simp at h ⊢; linarith
  | succ N ih =>
    intro hN
    by_cases h : X < α * 2 ^ N
    · have := ih h
      rw [Finset.sum_range_succ]
      have : 0 ≤ α * (2 ^ N * ind N) := mul_nonneg hα.le (mul_nonneg (by positivity) (hnn N))
      linarith
    · push_neg at h
      have hall : ∀ i ∈ Finset.range (N + 1), (2 : ℝ) ^ i * ind i = 2 ^ i := by
        intro i hi
        rw [hind1 i, mul_one]
        refine le_trans ?_ h
        have : (2 : ℝ) ^ i ≤ 2 ^ N :=
          pow_le_pow_right₀ (by norm_num) (by simp at hi; omega)
        exact mul_le_mul_of_nonneg_left this hα.le
      rw [Finset.sum_congr rfl hall, geom_two]
      nlinarith

/-- `Σ_{i<M} 2^{i+1} 1[2^{i+1} ≤ Y] ≤ 2Y - 2` for `Y ≥ 1`. -/
theorem lower_pt (Y : ℝ) (hY : 1 ≤ Y) (ind : ℕ → ℝ)
    (hind1 : ∀ i, (2 : ℝ) ^ (i + 1) ≤ Y → ind i = 1)
    (hind0 : ∀ i, ¬ (2 : ℝ) ^ (i + 1) ≤ Y → ind i = 0) :
    ∀ M : ℕ, ∑ i ∈ Finset.range M, 2 ^ (i + 1) * ind i ≤ 2 * Y - 2 := by
  intro M
  induction M with
  | zero => simp; linarith
  | succ M ih =>
    by_cases h : (2 : ℝ) ^ (M + 1) ≤ Y
    · have hall : ∀ i ∈ Finset.range (M + 1), (2 : ℝ) ^ (i + 1) * ind i = 2 * 2 ^ i := by
        intro i hi
        rw [hind1 i, mul_one, pow_succ, mul_comm]
        refine le_trans ?_ h
        exact pow_le_pow_right₀ (by norm_num) (by simp at hi; omega)
      rw [Finset.sum_congr rfl hall, ← Finset.mul_sum, geom_two, pow_succ]
      rw [pow_succ] at h
      linarith
    · rw [Finset.sum_range_succ, hind0 M h]
      simpa using ih

/-! ### Existence of a greedy list -/

variable {m : ℕ}

theorem greedy_exists (sc : Finset (Fin m) → Fin m → ℝ) :
    ∀ n ≤ m, ∃ l : List (Fin m), l.length = n ∧ l.Nodup ∧
      ∀ k (hk : k < l.length), ∀ e ∈ Finset.univ \ (l.take k).toFinset,
        sc (l.take k).toFinset e ≤ sc (l.take k).toFinset (l[k]'hk) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨[], rfl, List.nodup_nil, fun k hk => by simp at hk⟩
  | succ n ih =>
    intro hn
    obtain ⟨l, hlen, hnd, hgr⟩ := ih (by omega)
    have hcard : l.toFinset.card = n := by rw [List.toFinset_card_of_nodup hnd, hlen]
    have hR : (Finset.univ \ l.toFinset).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset (Finset.subset_univ _), hcard,
        Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨e, he, hemax⟩ := Finset.exists_max_image _ (sc l.toFinset) hR
    have hel : e ∉ l := by simpa using he
    refine ⟨l ++ [e], by simp [hlen], ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton e, ?_⟩
      intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hel ha
    · intro k hk e' he'
      simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k l.length with hkl | hkl
      · have ht : (l ++ [e]).take k = l.take k := List.take_append_of_le_length hkl.le
        rw [ht] at he' ⊢
        rw [List.getElem_append_left hkl]
        exact hgr k hkl e' he'
      · have hk' : k = l.length := by omega
        subst hk'
        have ht : (l ++ [e]).take l.length = l := by simp
        rw [ht] at he' ⊢
        rw [List.getElem_append_right (le_refl _)]
        simpa using hemax e' he'

end ASCT31

namespace ASCT31

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem E_lin (I : Instance U m) (a b : ℝ) (s : Finset ℕ) (w : ℕ → ℝ)
    (G : ℕ → (Fin m → U) → ℝ) :
    I.E (fun ω => a + b * ∑ i ∈ s, w i * G i ω) =
      a * ∑ ω, I.prob ω + b * ∑ i ∈ s, w i * I.E (G i) := by
  unfold Instance.E
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro ω _; ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro ω _; ring

theorem E_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 ≤ F ω) : 0 ≤ I.E F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (prob_nonneg I hp0 ω) (h ω)

theorem P_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (A : (Fin m → U) → Prop) :
    0 ≤ I.P A := by
  unfold Instance.P
  apply E_nonneg I hp0
  intro ω; split <;> norm_num

theorem P_le_one (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (hp1 : ∀ i, ∑ u, I.p i u = 1)
    (A : (Fin m → U) → Prop) : I.P A ≤ 1 := by
  unfold Instance.P
  have : I.E (fun _ => (1 : ℝ)) = 1 := by
    unfold Instance.E; simp [sum_prob I hp1]
  refine le_trans ?_ this.le
  apply E_mono I hp0
  intro ω _; split <;> norm_num

end ASCT31

open ASCT31 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → 0 < I.Q → (∃ π : AdaptivePolicy m U, I.Feasible π) → ∀ z : ℕ,
          (∃ L : List (Fin m), I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L) ∧
          ∀ L : List (Fin m), I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L →
            (∀ ω, 0 < I.prob ω → I.tau z < (I.f (I.NA (I.tau z) L ω).realized : ℝ)) ∧
            ∀ π : AdaptivePolicy m U, I.Feasible π →
              I.E (fun ω => (I.costOf (I.NA (I.tau z) L ω) : ℝ)) ≤
                C * ((1 + Real.log (1 / delta z)) / delta z) * I.expCost π := by
  obtain ⟨β, hβ, h33⟩ := lemma_3_3
  refine ⟨48 * β, by positivity, ?_⟩
  intro U _ _ m I hI hQ hfeas z
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, -⟩ := hI'
  have hδ : 0 < delta z := by unfold delta; positivity
  have hδ1 : delta z ≤ 1 := by unfold delta; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
  have hτQ : I.tau z < I.Q := by unfold Instance.tau; nlinarith
  have hfQ : ∀ A : Finset U, (I.f A : ℝ) ≤ I.Q := by
    intro A; unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ A)
  have hlog : 0 ≤ Real.log (1 / delta z) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  refine ⟨?_, ?_⟩
  · obtain ⟨l, hlen, hnd, hgr⟩ := greedy_exists
      (fun S e => I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z) S e) m le_rfl
    refine ⟨l, hnd, ?_, hgr⟩
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup hnd, hlen, Fintype.card_fin]
  intro L hL
  obtain ⟨π0, hπ0⟩ := hfeas
  have hLall : ∀ x, x ∈ L := by
    intro x
    have := hL.2.1
    rw [Finset.ext_iff] at this
    simpa using (this x).2 (Finset.mem_univ x)
  set stop := (I.parcaRound (I.tau z) L).stop with hstop_def
  have hNA : ∀ ω, I.NA (I.tau z) L ω = Round.go stop ω L [] := fun _ => rfl
  have hcov : ∀ ω, 0 < I.prob ω → I.tau z < (I.f (I.NA (I.tau z) L ω).realized : ℝ) := by
    intro ω hω
    rcases go_stop_or_all stop ω L [] with h | h
    · rw [hNA]; simpa [stop, Instance.parcaRound] using h
    · have hH : Honest ω (I.NA (I.tau z) L ω) := go_honest stop ω L [] (by simp [Honest])
      have hcovπ := hπ0 ω hω
      have hsub : (π0.run ω).realized ⊆ (I.NA (I.tau z) L ω).realized := by
        rw [realized_eq ω _ (run_honest π0 ω), realized_eq ω _ hH]
        apply Finset.image_subset_image
        intro x _; rw [hNA]; exact h x (hLall x)
      have h1 := hmon hsub
      unfold Instance.Covers at hcovπ
      rw [hcovπ] at h1
      have : (I.Q : ℝ) ≤ I.f (I.NA (I.tau z) L ω).realized := by exact_mod_cast h1
      linarith
  refine ⟨hcov, ?_⟩
  intro π hπ
  have hEY0 : 0 ≤ I.expCost π := E_nonneg I hp0 _ (fun ω => by positivity)
  by_cases h0 : I.tau z < (I.f ∅ : ℝ)
  · -- NA probes nothing
    have hX0 : ∀ ω, I.NA (I.tau z) L ω = [] := by
      intro ω
      rw [hNA]
      cases L with
      | nil => rfl
      | cons i L' =>
        have : stop [] = true := by simpa [stop, Instance.parcaRound, History.realized] using h0
        simp [Round.go, this]
    have : I.E (fun ω => (I.costOf (I.NA (I.tau z) L ω) : ℝ)) = 0 := by
      unfold Instance.E
      apply Finset.sum_eq_zero
      intro ω _
      simp [hX0 ω, Instance.costOf, History.items]
    rw [this]
    apply mul_nonneg _ hEY0
    apply mul_nonneg (by positivity)
    exact div_nonneg (by linarith) hδ.le
  push Not at h0
  -- OPT pays at least one on the support
  set X : (Fin m → U) → ℝ := fun ω => (I.costOf (I.NA (I.tau z) L ω) : ℝ) with hXdef
  set Y : (Fin m → U) → ℝ := fun ω => (I.costOf (π.run ω) : ℝ) with hYdef
  have hY1 : ∀ ω, 0 < I.prob ω → 1 ≤ Y ω := by
    intro ω hω
    have hc := hπ ω hω
    unfold Instance.Covers at hc
    have hne : (π.run ω).realized.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      rw [he] at hc
      have : (I.f ∅ : ℝ) = I.Q := by exact_mod_cast hc
      linarith
    obtain ⟨u, hu⟩ := hne
    simp only [History.realized, List.mem_toFinset, List.mem_map] at hu
    obtain ⟨p, hp, -⟩ := hu
    have hpi : p.1 ∈ (π.run ω).items := by
      simp only [History.items, List.mem_toFinset, List.mem_map]; exact ⟨p, hp, rfl⟩
    have : I.c p.1 ≤ I.costOf (π.run ω) :=
      Finset.single_le_sum (f := I.c) (fun _ _ => Nat.zero_le _) hpi
    have : 1 ≤ I.costOf (π.run ω) := le_trans (hc1 p.1) this
    simp only [hYdef]; exact_mod_cast this
  set α : ℝ := 8 * β / delta z * (1 + Real.log (1 / delta z)) with hαdef
  have hα : 0 < α := by positivity
  -- a uniform bound on the cost of NA
  set T : ℝ := ∑ i, (I.c i : ℝ)
  have hXT : ∀ ω, X ω ≤ T := by
    intro ω
    simp only [hXdef, Instance.costOf]
    push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => by simp only [hXdef]; positivity
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (T / α) (by norm_num : (1 : ℝ) < 2)
  have hXN : ∀ ω, X ω < α * 2 ^ (N + 1) := by
    intro ω
    have h1 : T < α * 2 ^ N := by rw [div_lt_iff₀ hα] at hN; linarith
    have h2 : α * 2 ^ N ≤ α * 2 ^ (N + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) hα.le
    linarith [hXT ω]
  set u : ℕ → ℝ := fun i => I.uPhase (I.tau z) α L i with hudef
  set us : ℕ → ℝ := fun i => I.uStar π i with husdef
  have hrec : ∀ j, u (j + 1) ≤ u j / 4 + 6 / 5 * us (j + 1) := by
    intro j
    have := h33 U m I hI hQ z L hL π hπ (j + 1) (by omega)
    rw [Nat.add_sub_cancel] at this
    exact this
  have hu0 : ∀ i, 0 ≤ u i := fun i => P_nonneg I hp0 _
  have hu1 : u 0 ≤ 1 := P_le_one I hp0 hp1 _
  -- upper bound on E[NA]
  have hEX : I.E X ≤ α + α * ∑ i ∈ Finset.range (N + 1), 2 ^ i * u i := by
    have := E_lin I α α (Finset.range (N + 1)) (fun i => (2 : ℝ) ^ i)
      (fun i ω => @ite ℝ (α * 2 ^ i ≤ X ω) (Classical.propDecidable _) 1 0)
    rw [sum_prob I hp1, mul_one] at this
    have e2 : ∀ i, I.E (fun ω => @ite ℝ (α * 2 ^ i ≤ X ω) (Classical.propDecidable _) 1 0) = u i :=
      fun i => rfl
    simp only [e2] at this
    rw [← this]
    apply E_mono I hp0
    intro ω _
    exact upper_pt α (X ω) hα (hX0 ω) _ (fun i h => if_pos h) (fun i h => if_neg h) (N + 1) (hXN ω)
  -- lower bound on E[OPT]
  have hEY : 1 + 1 / 2 * ∑ j ∈ Finset.range N, 2 ^ (j + 1) * us (j + 1) ≤ I.E Y := by
    have := E_lin I 1 (1 / 2) (Finset.range N) (fun j => (2 : ℝ) ^ (j + 1))
      (fun j ω => @ite ℝ ((2 : ℝ) ^ (j + 1) ≤ Y ω) (Classical.propDecidable _) 1 0)
    rw [sum_prob I hp1, mul_one] at this
    have e2 : ∀ j, I.E (fun ω => @ite ℝ ((2 : ℝ) ^ (j + 1) ≤ Y ω) (Classical.propDecidable _) 1 0)
        = us (j + 1) := fun j => rfl
    simp only [e2] at this
    rw [← this]
    apply E_mono I hp0
    intro ω hω
    have := lower_pt (Y ω) (hY1 ω hω)
      (fun j => @ite ℝ ((2 : ℝ) ^ (j + 1) ≤ Y ω) (Classical.propDecidable _) 1 0)
      (fun i h => if_pos h) (fun i h => if_neg h) N
    linarith
  -- the recursion
  set Γ := ∑ i ∈ Finset.range (N + 1), 2 ^ i * u i with hΓ
  set S := ∑ j ∈ Finset.range N, (2 : ℝ) ^ (j + 1) * us (j + 1) with hS
  have hΓsplit : Γ = u 0 + ∑ j ∈ Finset.range N, 2 ^ (j + 1) * u (j + 1) := by
    rw [hΓ, Finset.sum_range_succ']; simp; ring
  have hΓ' : ∑ j ∈ Finset.range N, (2 : ℝ) ^ j * u j ≤ Γ := by
    rw [hΓ, Finset.sum_range_succ]
    have : 0 ≤ (2 : ℝ) ^ N * u N := mul_nonneg (by positivity) (hu0 N)
    linarith
  have hstep : ∑ j ∈ Finset.range N, (2 : ℝ) ^ (j + 1) * u (j + 1) ≤
      1 / 2 * ∑ j ∈ Finset.range N, (2 : ℝ) ^ j * u j + 6 / 5 * S := by
    rw [hS, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have := hrec j
    have h2 : (0 : ℝ) ≤ 2 ^ (j + 1) := by positivity
    have := mul_le_mul_of_nonneg_left this h2
    rw [pow_succ] at this ⊢
    nlinarith
  have hΓb : Γ ≤ 2 + 24 / 5 * (I.E Y - 1) := by nlinarith
  have hEY1 : 1 ≤ I.E Y := by
    have : 0 ≤ S := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (P_nonneg I hp0 _)
    nlinarith
  have hfin : I.E X ≤ 6 * α * I.E Y := by nlinarith
  have hC : 6 * α = 48 * β * ((1 + Real.log (1 / delta z)) / delta z) := by
    rw [hαdef]; field_simp; ring
  show I.E X ≤ 48 * β * ((1 + Real.log (1 / delta z)) / delta z) * I.E Y
  rw [← hC]; exact hfin
