-- Prove2me | solution 1 for AlgMechDesign.Local.generic_unique_maximizers
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:42:38.956284+00:00
-- url     : https://prove2.me/submissions/a43e06dd-ac26-4664-b717-6e665b10103f

import Mathlib
import Definitions.Def_AlgMechDesign_Local_Model
import Definitions.Def_AlgMechDesign_Local_Prices



namespace AlgMechDesign.Local

open Finset

lemma gu_util_eq {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (d : Fin n → Fin k → ℝ) (i : Fin n)
    (ti : Fin k → ℝ) :
    utility alloc pay d i ti = pay d i - setTime ti (agentSet alloc d i) := rfl

lemma gu_pay_eq_price {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
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
  rw [gu_util_eq, gu_util_eq, hwY, Function.update_eq_self] at h1 h2
  linarith

lemma gu_menu {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htr : IsTruthful alloc pay)
    {t : Fin n → Fin k → ℝ} (ht : IsType t) (i : Fin n) {Y : Finset (Fin k)}
    (hY : IsAttainable alloc i Y t) :
    price alloc pay i Y t - setTime (t i) Y ≤
      price alloc pay i (agentSet alloc t i) t - setTime (t i) (agentSet alloc t i) := by
  have hp : price alloc pay i Y t = pay (Function.update t i (Classical.choose hY)) i := by
    unfold price; rw [dif_pos hY]
  obtain ⟨hw, hwY⟩ := Classical.choose_spec hY
  have h1 := htr t ht i (t i) (Classical.choose hY) (fun j => ht i j) hw
  rw [gu_util_eq, gu_util_eq, hwY, Function.update_eq_self] at h1
  rw [hp, ← gu_pay_eq_price htr ht i]
  exact h1

/-- Proposition 4.4: for a truthful mechanism the price of an attainable set equals the payment
at any positive declaration obtaining it. -/
lemma gu_price_witness {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htr : IsTruthful alloc pay)
    {t : Fin n → Fin k → ℝ} (ht : IsType t) (i : Fin n) {X : Finset (Fin k)}
    (w : Fin k → ℝ) (hw : IsAgentType w) (hwX : agentSet alloc (Function.update t i w) i = X) :
    price alloc pay i X t = pay (Function.update t i w) i := by
  have hA : IsAttainable alloc i X t := ⟨w, hw, hwX⟩
  have hp : price alloc pay i X t = pay (Function.update t i (Classical.choose hA)) i := by
    unfold price; rw [dif_pos hA]
  obtain ⟨hc, hcX⟩ := Classical.choose_spec hA
  have h1 := htr t ht i w (Classical.choose hA) hw hc
  have h2 := htr t ht i (Classical.choose hA) w hc hw
  rw [gu_util_eq, gu_util_eq, hwX, hcX] at h1 h2
  rw [hp]; linarith

/-- The price offered to `i` depends only on the other agents' declarations. -/
lemma gu_price_update {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htr : IsTruthful alloc pay) (i : Fin n)
    (X : Finset (Fin k)) {t t' : Fin n → Fin k → ℝ} (ht : IsType t) (ht' : IsType t')
    (hoff : ∀ l, l ≠ i → t l = t' l) :
    price alloc pay i X t = price alloc pay i X t' := by
  have hupd : ∀ w : Fin k → ℝ, Function.update t i w = Function.update t' i w := by
    intro w; funext l
    by_cases hl : l = i
    · subst hl; simp
    · rw [Function.update_of_ne hl, Function.update_of_ne hl, hoff l hl]
  by_cases h : IsAttainable alloc i X t
  · obtain ⟨w, hw, hwX⟩ := h
    rw [gu_price_witness htr ht i w hw hwX, hupd w] at *
    rw [gu_price_witness htr ht' i w hw hwX]
  · have h' : ¬ IsAttainable alloc i X t' := by
      rintro ⟨w, hw, hwX⟩
      exact h ⟨w, hw, by rw [hupd w]; exact hwX⟩
    unfold price
    rw [dif_neg h, dif_neg h']

/-- A tie: if `xⁱ(t)` is not the unique maximizer, some other attainable set has equal utility. -/
lemma gu_tie {n k : ℕ} {alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)}
    {pay : (Fin n → Fin k → ℝ) → Fin n → ℝ} (htr : IsTruthful alloc pay)
    {t : Fin n → Fin k → ℝ} (ht : IsType t) (i : Fin n)
    (h : ¬ IsUniqueMaximizer alloc pay t i) :
    ∃ X : Finset (Fin k), X ≠ agentSet alloc t i ∧
      price alloc pay i X t - price alloc pay i (agentSet alloc t i) t
        = setTime (t i) X - setTime (t i) (agentSet alloc t i) := by
  unfold IsUniqueMaximizer at h
  push_neg at h
  obtain ⟨X, hX, hne, hle⟩ := h
  refine ⟨X, hne, ?_⟩
  have := gu_menu htr ht i hX
  unfold setUtility at hle
  linarith

/-- Binary weight of a set of tasks; injective. -/
lemma gu_W_inj {k : ℕ} (X Y : Finset (Fin k))
    (h : ∑ j ∈ X, (2:ℝ) ^ (j : ℕ) = ∑ j ∈ Y, (2:ℝ) ^ (j : ℕ)) : X = Y := by
  have h' : ∑ j ∈ X, 2 ^ (j : ℕ) = ∑ j ∈ Y, (2:ℕ) ^ (j : ℕ) := by exact_mod_cast h
  have h2 : ∑ j ∈ X.map Fin.valEmbedding, 2 ^ j = ∑ j ∈ Y.map Fin.valEmbedding, 2 ^ j := by
    simpa [Finset.sum_map] using h'
  have h3 := Finset.geomSum_injective (n := 2) le_rfl h2
  exact Finset.map_injective Fin.valEmbedding h3

/-- The perturbed type vector on the grid: agent `i` is moved by `(mᵢ+1) δ (1, 2, 4, …)`. -/
noncomputable def guT {n k N : ℕ} (t : Fin n → Fin k → ℝ) (δ : ℝ) (m : Fin n → Fin N) :
    Fin n → Fin k → ℝ :=
  fun i j => t i j + (((m i : ℕ) : ℝ) + 1) * δ * 2 ^ (j : ℕ)

lemma guT_setTime {n k N : ℕ} (t : Fin n → Fin k → ℝ) (δ : ℝ) (m : Fin n → Fin N)
    (i : Fin n) (X : Finset (Fin k)) :
    setTime (guT t δ m i) X =
      setTime (t i) X + (((m i : ℕ) : ℝ) + 1) * δ * ∑ j ∈ X, (2:ℝ) ^ (j : ℕ) := by
  unfold setTime guT
  simp only [sum_add_distrib, mul_sum]

lemma guT_update {n k N : ℕ} (t : Fin n → Fin k → ℝ) (δ : ℝ) (m m' : Fin n → Fin N)
    (i : Fin n) (hoff : ∀ l, l ≠ i → m l = m' l) :
    guT t δ m' = Function.update (guT t δ m) i (guT t δ m' i) := by
  funext l j
  by_cases hl : l = i
  · subst hl; simp
  · rw [Function.update_of_ne hl]
    simp only [guT]
    rw [hoff l hl]

theorem gu_core {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : Fin n → Fin k → ℝ, IsType t' ∧ ‖t - t'‖ < ε ∧
      ∀ i : Fin n, IsUniqueMaximizer alloc pay t' i := by
  classical
  set K := Fintype.card (Finset (Fin k) × Finset (Fin k)) with hK
  set N := n * K + 1 with hN
  have hN0 : (0:ℝ) < N := by positivity
  set δ : ℝ := ε / (2 * N * 2 ^ k) with hδ
  have hδ0 : 0 < δ := by positivity
  have hT : ∀ m : Fin n → Fin N, IsType (guT t δ m) := fun m i j => by
    have := ht i j; simp only [guT]; positivity
  have hTnorm : ∀ m : Fin n → Fin N, ‖t - guT t δ m‖ < ε := by
    intro m
    rw [pi_norm_lt_iff hε]; intro i
    rw [pi_norm_lt_iff hε]; intro j
    simp only [Pi.sub_apply, guT, Real.norm_eq_abs]
    have h1 : ((m i : ℕ) : ℝ) + 1 ≤ N := by
      have := (m i).isLt; exact_mod_cast this
    have h2 : (2:ℝ) ^ (j : ℕ) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) (j.isLt.le)
    rw [show t i j - (t i j + (((m i : ℕ) : ℝ) + 1) * δ * 2 ^ (j:ℕ))
        = -((((m i : ℕ) : ℝ) + 1) * δ * 2 ^ (j:ℕ)) by ring, abs_neg,
      abs_of_nonneg (by positivity)]
    calc (((m i : ℕ) : ℝ) + 1) * δ * 2 ^ (j:ℕ) ≤ N * δ * 2 ^ k := by gcongr
      _ = ε / 2 := by rw [hδ]; field_simp
      _ < ε := by linarith
  let Bad : Fin n → Finset (Fin n → Fin N) :=
    fun i => univ.filter (fun m => ¬ IsUniqueMaximizer alloc pay (guT t δ m) i)
  have hBad : ∀ i, (Bad i).card ≤ K * N ^ (n - 1) := by
    intro i
    have hpair : ∀ m ∈ Bad i, ∃ X : Finset (Fin k), X ≠ agentSet alloc (guT t δ m) i ∧
        price alloc pay i X (guT t δ m)
          - price alloc pay i (agentSet alloc (guT t δ m) i) (guT t δ m)
          = setTime (guT t δ m i) X - setTime (guT t δ m i) (agentSet alloc (guT t δ m) i) := by
      intro m hm
      simp only [Bad, mem_filter, mem_univ, true_and] at hm
      exact gu_tie htr (hT m) i hm
    choose! f hf using hpair
    let r : (Fin n → Fin N) → ({l : Fin n // l ≠ i} → Fin N) := fun m l => m l.1
    have hfib : ∀ b ∈ (Bad i).image r, ((Bad i).filter (fun m => r m = b)).card ≤ K := by
      intro b _
      rw [hK, ← Finset.card_univ]
      apply card_le_card_of_injOn (fun m => (f m, agentSet alloc (guT t δ m) i))
        (fun _ _ => mem_univ _)
      intro m hm m' hm' heq
      simp only [coe_filter, Set.mem_setOf_eq] at hm hm'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hf1, hf2⟩ := heq
      have hoff : ∀ l, l ≠ i → m l = m' l := fun l hl => by
        have := congrFun (hm.2.trans hm'.2.symm) ⟨l, hl⟩
        simpa [r] using this
      have hprice : ∀ Y, price alloc pay i Y (guT t δ m') = price alloc pay i Y (guT t δ m) := by
        intro Y
        apply gu_price_update htr i Y (hT m') (hT m)
        intro l hl
        show (fun j => t l j + (((m' l : ℕ) : ℝ) + 1) * δ * 2 ^ (j : ℕ))
          = (fun j => t l j + (((m l : ℕ) : ℝ) + 1) * δ * 2 ^ (j : ℕ))
        rw [hoff l hl]
      obtain ⟨hne, e1⟩ := hf m hm.1
      obtain ⟨_, e2⟩ := hf m' hm'.1
      rw [hprice, hprice, ← hf2, ← hf1] at e2
      rw [guT_setTime, guT_setTime] at e1 e2
      have hW : ∑ j ∈ f m, (2:ℝ) ^ (j : ℕ)
          - ∑ j ∈ agentSet alloc (guT t δ m) i, (2:ℝ) ^ (j : ℕ) ≠ 0 := by
        intro h0
        exact hne (gu_W_inj _ _ (sub_eq_zero.mp h0))
      have e3 : ((((m i : ℕ) : ℝ) + 1) * δ) * (∑ j ∈ f m, (2:ℝ) ^ (j : ℕ)
          - ∑ j ∈ agentSet alloc (guT t δ m) i, (2:ℝ) ^ (j : ℕ))
          = ((((m' i : ℕ) : ℝ) + 1) * δ) * (∑ j ∈ f m, (2:ℝ) ^ (j : ℕ)
          - ∑ j ∈ agentSet alloc (guT t δ m) i, (2:ℝ) ^ (j : ℕ)) := by
        linarith
      have e4 := mul_right_cancel₀ hW e3
      have e5 := mul_right_cancel₀ hδ0.ne' e4
      have e6 : ((m i : ℕ) : ℝ) = ((m' i : ℕ) : ℝ) := by linarith
      have e7 : m i = m' i := Fin.ext (by exact_mod_cast e6)
      funext l
      by_cases hl : l = i
      · rw [hl]; exact e7
      · exact hoff l hl
    have h1 := card_le_mul_card_image (Bad i) K hfib
    have h2 : ((Bad i).image r).card ≤ N ^ (n - 1) := by
      calc ((Bad i).image r).card ≤ Fintype.card ({l : Fin n // l ≠ i} → Fin N) :=
            card_le_univ _
        _ = N ^ (n - 1) := by
            rw [Fintype.card_fun, Fintype.card_fin]
            congr 1
            have := Set.card_ne_eq (α := Fin n) i
            simpa using this
    calc (Bad i).card ≤ K * ((Bad i).image r).card := h1
      _ ≤ K * N ^ (n - 1) := Nat.mul_le_mul_left _ h2
  have hcard : (univ : Finset (Fin n → Fin N)).card = N ^ n := by
    rw [card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  obtain ⟨m, hm⟩ : ∃ m, ∀ i, m ∉ Bad i := by
    by_contra hcon
    push_neg at hcon
    have hsub : (univ : Finset (Fin n → Fin N)) ⊆ univ.biUnion Bad := by
      intro m _
      obtain ⟨i, hi⟩ := hcon m
      exact mem_biUnion.mpr ⟨i, mem_univ _, hi⟩
    have h1 := card_le_card hsub
    have h2 := card_biUnion_le (s := (univ : Finset (Fin n))) (t := Bad)
    have h3 : ∑ i, (Bad i).card ≤ ∑ i : Fin n, K * N ^ (n - 1) :=
      sum_le_sum (fun i _ => hBad i)
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at h3
    rw [hcard] at h1
    have h4 : n * (K * N ^ (n - 1)) < N ^ n := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        have hNpos : 0 < N ^ n' := by positivity
        calc (n' + 1) * (K * N ^ n') = ((n' + 1) * K) * N ^ n' := by ring
          _ < N * N ^ n' := Nat.mul_lt_mul_of_pos_right (by omega) hNpos
          _ = N ^ n' * N := by ring
    omega
  refine ⟨guT t δ m, hT m, hTnorm m, fun i => ?_⟩
  have := hm i
  simp only [Bad, mem_filter, mem_univ, true_and, not_not] at this
  exact this

end AlgMechDesign.Local

open AlgMechDesign.Local


theorem solution {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (t : Fin n → Fin k → ℝ) (ht : IsType t) (ε : ℝ) (hε : 0 < ε) :
    ∃ t' : Fin n → Fin k → ℝ, IsType t' ∧ ‖t - t'‖ < ε ∧
      ∀ i : Fin n, IsUniqueMaximizer alloc pay t' i := by
  exact gu_core alloc pay htr t ht ε hε
