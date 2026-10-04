-- Prove2me | solution 1 for AlgMechDesign.CompBonus.cb_strongly_truthful
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:39:44.169971+00:00
-- url     : https://prove2.me/submissions/abc8ac80-a480-4235-8881-e662cb17a144

import Mathlib
import Definitions.Def_AlgMechDesign_CompBonus_Model
import Definitions.Def_AlgMechDesign_CompBonus_Mechanism



namespace AlgMechDesign.CompBonus

open Finset

lemma cbx_makespan_lt_iff {n k : ℕ} [NeZero n] (d : Fin n → Fin k → ℝ) (y : Fin k → Fin n)
    (B : ℝ) : makespan d y < B ↔ ∀ l, load d y l < B := by
  unfold makespan; simp [Finset.sup'_lt_iff]

lemma cbx_makespan_le_iff {n k : ℕ} [NeZero n] (d : Fin n → Fin k → ℝ) (y : Fin k → Fin n)
    (B : ℝ) : makespan d y ≤ B ↔ ∀ l, load d y l ≤ B := by
  unfold makespan; simp [Finset.sup'_le_iff]

lemma cbx_load_le_makespan {n k : ℕ} [NeZero n] (d : Fin n → Fin k → ℝ) (y : Fin k → Fin n)
    (l : Fin n) : load d y l ≤ makespan d y :=
  Finset.le_sup' (load d y) (Finset.mem_univ l)

lemma cbx_load_le_card {n k : ℕ} (d : Fin n → Fin k → ℝ) (y : Fin k → Fin n) (l : Fin n)
    (e : ℝ) (he : 0 ≤ e) (h : ∀ j, y j = l → d l j ≤ e) : load d y l ≤ k * e := by
  unfold load
  calc ∑ j ∈ univ.filter (fun j => y j = l), d l j
        ≤ (univ.filter (fun j => y j = l)).card • e :=
        Finset.sum_le_card_nsmul _ _ _ (fun j hj => h j (Finset.mem_filter.mp hj).2)
    _ ≤ k * e := by
        rw [nsmul_eq_mul]
        have h1 := Finset.card_filter_le (univ : Finset (Fin k)) (fun j => y j = l)
        simp only [Finset.card_univ, Fintype.card_fin] at h1
        have : ((univ.filter (fun j => y j = l)).card : ℝ) ≤ k := by exact_mod_cast h1
        exact mul_le_mul_of_nonneg_right this he

lemma cbx_le_makespan {n k : ℕ} [NeZero n] (d : Fin n → Fin k → ℝ) (hd : ∀ l j, 0 ≤ d l j)
    (y : Fin k → Fin n) (j : Fin k) : d (y j) j ≤ makespan d y := by
  refine le_trans ?_ (cbx_load_le_makespan d y (y j))
  unfold load
  exact Finset.single_le_sum (f := fun j' => d (y j) j') (fun j' _ => hd _ _) (by simp)

lemma cbx_sum_le_gT {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (τ : Fin k → ℝ) (l : Fin n) :
    ∑ j ∈ univ.filter (fun j => x j = l), τ j ≤ gT x τ :=
  Finset.le_sup' (f := fun l => ∑ j ∈ univ.filter (fun j => x j = l), τ j) (Finset.mem_univ l)

lemma cbx_le_gT {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (τ : Fin k → ℝ) (hτ : ∀ j, 0 ≤ τ j)
    (j : Fin k) : τ j ≤ gT x τ := by
  refine le_trans ?_ (cbx_sum_le_gT x τ (x j))
  exact Finset.single_le_sum (f := τ) (fun j' _ => hτ _) (by simp)

lemma cbx_gT_mono {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (τ σ : Fin k → ℝ)
    (h : ∀ j, τ j ≤ σ j) : gT x τ ≤ gT x σ :=
  Finset.sup'_le _ _ (fun l _ => le_trans (Finset.sum_le_sum (fun j _ => h j)) (cbx_sum_le_gT x σ l))

lemma cbx_gT_corrStar {n k : ℕ} [NeZero n] (x : Fin k → Fin n) (d : Fin n → Fin k → ℝ) :
    gT x (corrStar x d) = makespan d x := by
  unfold gT makespan load corrStar
  congr 1; funext l
  apply Finset.sum_congr rfl; intro j hj; rw [(Finset.mem_filter.mp hj).2]

lemma cbx_utility {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n) :
    utility alloc (cbPay alloc) d E i =
      -gT (alloc d) (corr i (alloc d) d (actualTimes alloc d E)) := by
  unfold utility cbPay compensation bonus; ring

lemma cbx_isType_update {n k : ℕ} (d : Fin n → Fin k → ℝ) (hd : IsType d) (i : Fin n)
    (ti : Fin k → ℝ) (hti : IsAgentType ti) : IsType (Function.update d i ti) := by
  intro l j
  by_cases h : l = i
  · subst h; simp [hti j]
  · simp [Function.update_apply, h, hd l j]

lemma cbx_corr_truth {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n) (ti : Fin k → ℝ) :
    corr i (alloc (Function.update d i ti)) (Function.update d i ti)
      (actualTimes alloc (Function.update d i ti) (Function.update E i (fun _ j => ti j))) =
      corrStar (alloc (Function.update d i ti)) (Function.update d i ti) := by
  funext j; unfold corr corrStar actualTimes
  split_ifs with hj
  · rw [hj]; simp
  · rfl

lemma cbx_corr_gen {n k : ℕ} (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (d : Fin n → Fin k → ℝ) (E : Fin n → ExecPlan n k) (i : Fin n) (di : Fin k → ℝ)
    (ei : ExecPlan n k) :
    corr i (alloc (Function.update d i di)) (Function.update d i di)
      (actualTimes alloc (Function.update d i di) (Function.update E i ei)) =
      fun j => if alloc (Function.update d i di) j = i then ei (alloc (Function.update d i di)) j
        else d (alloc (Function.update d i di) j) j := by
  funext j; unfold corr actualTimes
  split_ifs with hj
  · rw [hj]; simp
  · simp [Function.update_apply, hj]

lemma cbx_keyA {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (hopt : IsOptimalAlloc alloc) (i : Fin n) (ti di : Fin k → ℝ) (ei : ExecPlan n k)
    (hti : IsAgentType ti) (hdom : Dominant alloc (cbPay alloc) i ti di ei)
    (d : Fin n → Fin k → ℝ) (hd : IsType d) (y : Fin k → Fin n) :
    gT (alloc (Function.update d i di))
      (fun j => if alloc (Function.update d i di) j = i then ei (alloc (Function.update d i di)) j
        else d (alloc (Function.update d i di) j) j) ≤ makespan (Function.update d i ti) y := by
  obtain ⟨_, _, h⟩ := hdom
  have := h d hd (fun _ _ _ => 0) ti hti (fun _ j => ti j) (fun _ _ _ => le_rfl)
  rw [cbx_utility, cbx_utility, cbx_corr_truth, cbx_corr_gen, cbx_gT_corrStar] at this
  linarith [hopt _ (cbx_isType_update d hd i ti hti) y]

lemma cbx_truthful {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (hopt : IsOptimalAlloc alloc) : Truthful alloc (cbPay alloc) := by
  intro i ti hti
  refine ⟨fun _ j => ti j, hti, fun _ _ _ => le_rfl, ?_⟩
  intro d hd E di' hdi' ei' hei'
  rw [cbx_utility, cbx_utility, cbx_corr_truth, cbx_corr_gen, cbx_gT_corrStar]
  have h1 := hopt _ (cbx_isType_update d hd i ti hti) (alloc (Function.update d i di'))
  have h2 : makespan (Function.update d i ti) (alloc (Function.update d i di')) ≤
      gT (alloc (Function.update d i di'))
        (fun j => if alloc (Function.update d i di') j = i then ei' (alloc (Function.update d i di')) j
          else d (alloc (Function.update d i di') j) j) := by
    rw [← cbx_gT_corrStar]
    apply cbx_gT_mono
    intro j
    unfold corrStar
    split_ifs with hj
    · rw [hj]; simp only [Function.update_self]
      exact hei' _ j hj
    · simp [Function.update_apply, hj]
  linarith

lemma cbx_exec_min {n k : ℕ} [NeZero n] (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (hopt : IsOptimalAlloc alloc) (i : Fin n) (ti di : Fin k → ℝ) (ei : ExecPlan n k)
    (hti : IsAgentType ti) (hdom : Dominant alloc (cbPay alloc) i ti di ei)
    (x : Fin k → Fin n) (j0 : Fin k) (hj0 : x j0 = i) : ∀ j, x j = i → ei x j = ti j := by
  have hdi := hdom.1
  have hfe := hdom.2.1
  have hj0S : j0 ∈ univ.filter (fun j => x j = i) := by simp [hj0]
  have Ld : 0 < ∑ j ∈ univ.filter (fun j => x j = i), di j :=
    Finset.sum_pos (fun j _ => hdi j) ⟨j0, hj0S⟩
  have Lt : 0 < ∑ j ∈ univ.filter (fun j => x j = i), ti j :=
    Finset.sum_pos (fun j _ => hti j) ⟨j0, hj0S⟩
  obtain ⟨m, hm_def⟩ : ∃ m, m = min (∑ j ∈ univ.filter (fun j => x j = i), di j)
      (∑ j ∈ univ.filter (fun j => x j = i), ti j) := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; exact lt_min Ld Lt
  have hm1 : m ≤ ∑ j ∈ univ.filter (fun j => x j = i), di j := by rw [hm_def]; exact min_le_left _ _
  have hm2 : m ≤ ∑ j ∈ univ.filter (fun j => x j = i), ti j := by rw [hm_def]; exact min_le_right _ _
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = m / (k + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hkε : (k : ℝ) * ε ≤ m := by
    rw [hε_def, mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = ∑ j ∈ univ.filter (fun j => x j = i), di j + 1 := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM_def]; linarith
  let d : Fin n → Fin k → ℝ := fun l j => if x j = l then ε else M
  have hd : IsType d := by
    intro l j; simp only [d]; split_ifs <;> assumption
  have hP1 : alloc (Function.update d i di) = x := by
    by_contra hne
    have hle := hopt (Function.update d i di) (cbx_isType_update d hd i di hdi) x
    have hpos : ∀ l j, 0 ≤ Function.update d i di l j := fun l j =>
      (cbx_isType_update d hd i di hdi l j).le
    have hx : makespan (Function.update d i di) x ≤
        ∑ j ∈ univ.filter (fun j => x j = i), di j := by
      rw [cbx_makespan_le_iff]; intro l
      by_cases hl : l = i
      · subst hl; unfold load; simp
      · calc _ ≤ (k : ℝ) * ε := cbx_load_le_card _ _ _ _ hε.le
                (fun j hj => by simp [hl, d, hj])
             _ ≤ _ := hkε.trans hm1
    have hzi : ∀ j, alloc (Function.update d i di) j ≠ x j →
        alloc (Function.update d i di) j = i := by
      intro j hj; by_contra hzi
      have h1 := cbx_le_makespan (Function.update d i di) hpos (alloc (Function.update d i di)) j
      have h2 : Function.update d i di (alloc (Function.update d i di) j) j = M := by
        simp [hzi, d, Ne.symm hj]
      linarith
    obtain ⟨j1, hj1⟩ : ∃ j, alloc (Function.update d i di) j ≠ x j := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hz1 := hzi j1 hj1
    have hx1 : x j1 ≠ i := fun h => hj1 (hz1.trans h.symm)
    have hsub : insert j1 (univ.filter (fun j => x j = i)) ⊆
        univ.filter (fun j => alloc (Function.update d i di) j = i) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rcases hj with rfl | hj
      · exact hz1
      · by_cases hzx : alloc (Function.update d i di) j = x j
        · rw [hzx]; exact hj
        · exact hzi j hzx
    have h3 : ∑ j ∈ insert j1 (univ.filter (fun j => x j = i)), di j ≤
        load (Function.update d i di) (alloc (Function.update d i di)) i := by
      unfold load; simp only [Function.update_self]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => (hdi j).le)
    rw [Finset.sum_insert (by simp [hx1])] at h3
    have h4 := cbx_load_le_makespan (Function.update d i di) (alloc (Function.update d i di)) i
    linarith [hdi j1]
  have hA := cbx_keyA alloc hopt i ti di ei hti hdom d hd x
  rw [hP1] at hA
  have hx2 : makespan (Function.update d i ti) x ≤
      ∑ j ∈ univ.filter (fun j => x j = i), ti j := by
    rw [cbx_makespan_le_iff]; intro l
    by_cases hl : l = i
    · subst hl; unfold load; simp
    · calc _ ≤ (k : ℝ) * ε := cbx_load_le_card _ _ _ _ hε.le
              (fun j hj => by simp [hl, d, hj])
           _ ≤ _ := hkε.trans hm2
  have hlow : ∑ j ∈ univ.filter (fun j => x j = i), ei x j ≤
      gT x (fun j => if x j = i then ei x j else d (x j) j) := by
    refine le_trans (le_of_eq ?_) (cbx_sum_le_gT x _ i)
    apply Finset.sum_congr rfl; intro j hj
    rw [if_pos (Finset.mem_filter.mp hj).2]
  have hsum : ∑ j ∈ univ.filter (fun j => x j = i), ti j ≤
      ∑ j ∈ univ.filter (fun j => x j = i), ei x j :=
    Finset.sum_le_sum (fun j hj => hfe x j (Finset.mem_filter.mp hj).2)
  have heq : ∑ j ∈ univ.filter (fun j => x j = i), ti j =
      ∑ j ∈ univ.filter (fun j => x j = i), ei x j := by linarith
  intro j hj
  exact ((Finset.sum_eq_sum_iff_of_le (fun j hj => hfe x j (Finset.mem_filter.mp hj).2)).mp heq
    j (by simp [hj])).symm

lemma cbx_ystar {n k : ℕ} [NeZero n] (P : Fin n → Fin k → ℝ) (i l : Fin n) (hl : l ≠ i)
    (j0 : Fin k) (ε v : ℝ) (hε : 0 ≤ ε) (hkε : (k : ℝ) * ε < v) (hi : P i j0 < v)
    (hlj : ∀ j, j ≠ j0 → P l j ≤ ε) :
    makespan P (fun j => if j = j0 then i else l) < v := by
  rw [cbx_makespan_lt_iff]; intro m
  by_cases hm : m = i
  · subst hm
    have : univ.filter (fun j => (if j = j0 then m else l) = m) = {j0} := by
      ext j; by_cases hj : j = j0 <;> simp [hj, hl]
    unfold load; rw [this, Finset.sum_singleton]; exact hi
  · refine lt_of_le_of_lt (cbx_load_le_card _ _ _ ε hε ?_) hkε
    intro j hj
    by_cases hj0 : j = j0
    · simp [hj0] at hj; exact absurd hj.symm hm
    · simp [hj0] at hj; subst hj; exact hlj j hj0

lemma cbx_const {n k : ℕ} [NeZero n] (P : Fin n → Fin k → ℝ) (l : Fin n)
    (j0 : Fin k) (ε c b : ℝ) (hb : 0 < b) (hkε : (k : ℝ) * ε + c < b)
    (hlj : ∀ j, P l j = ε + if j = j0 then c else 0) :
    makespan P (fun _ => l) < b := by
  rw [cbx_makespan_lt_iff]; intro m
  by_cases hm : m = l
  · subst hm
    unfold load
    simp only [Finset.filter_true, hlj, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    linarith
  · refine lt_of_le_of_lt (cbx_load_le_card _ _ _ 0 le_rfl ?_) (by simpa using hb)
    intro j hj; exact absurd hj.symm hm

lemma cbx_params (k : ℕ) (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ a < ε + c ∧ ε + c < b ∧ (k : ℝ) * ε + c < b ∧
      (k : ℝ) * ε < ε + c := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkε : (k : ℝ) * ((b - a) / (4 * (k + 1))) < (b - a) / 4 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hε : 0 < (b - a) / (4 * (k + 1)) := by
    apply div_pos <;> [linarith; positivity]
  have hε2 : (b - a) / (4 * (k + 1)) ≤ (b - a) / 4 := by
    apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)
  refine ⟨(b - a) / (4 * (k + 1)), a + (b - a) / 4, hε, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

lemma cbx_decl_true {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (hopt : IsOptimalAlloc alloc) (i : Fin n) (ti di : Fin k → ℝ) (ei : ExecPlan n k)
    (hti : IsAgentType ti) (hdom : Dominant alloc (cbPay alloc) i ti di ei) : di = ti := by
  have hdi := hdom.1
  have hfe := hdom.2.1
  by_contra hne
  obtain ⟨j0, hj0⟩ : ∃ j, di j ≠ ti j := by
    by_contra h; push_neg at h; exact hne (funext h)
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨l, hl⟩ := exists_ne i
  rcases lt_or_gt_of_ne hj0 with h | h
  · -- di j0 < ti j0
    obtain ⟨ε, c, hε, hc, h1, h2, h3, h4⟩ := cbx_params k (di j0) (ti j0) (hdi j0) h
    let d : Fin n → Fin k → ℝ := fun m j =>
      if m = l then ε + (if j = j0 then c else 0) else ti j0 + 1
    have hd : IsType d := by
      intro m j; simp only [d]; split_ifs <;> linarith [hti j0]
    have hdl : ∀ j, Function.update d i di l j = ε + if j = j0 then c else 0 := by
      intro j; simp [hl, d]
    have hdl' : ∀ j, Function.update d i ti l j = ε + if j = j0 then c else 0 := by
      intro j; simp [hl, d]
    have hz : alloc (Function.update d i di) j0 = i := by
      by_contra hz
      have hle := hopt (Function.update d i di) (cbx_isType_update d hd i di hdi)
        (fun j => if j = j0 then i else l)
      have hys := cbx_ystar (Function.update d i di) i l hl j0 ε (ε + c) hε.le h4
        (by simpa using h1) (fun j hj => by rw [hdl]; simp [hj])
      have hlow := cbx_le_makespan (Function.update d i di)
        (fun m j => (cbx_isType_update d hd i di hdi m j).le) (alloc (Function.update d i di)) j0
      have : ε + c ≤ Function.update d i di (alloc (Function.update d i di) j0) j0 := by
        by_cases hzl : alloc (Function.update d i di) j0 = l
        · rw [hzl, hdl]; simp
        · simp [hz, hzl, d]; linarith
      linarith
    have hA := cbx_keyA alloc hopt i ti di ei hti hdom d hd (fun _ => l)
    have hc2 := cbx_const (Function.update d i ti) l j0 ε c (ti j0) (hti j0) h3 hdl'
    have hτ : ∀ j, 0 ≤ (fun j => if alloc (Function.update d i di) j = i then
        ei (alloc (Function.update d i di)) j else d (alloc (Function.update d i di) j) j) j := by
      intro j; simp only
      split_ifs with hj
      · exact le_trans (hti j).le (hfe _ j hj)
      · exact (hd _ _).le
    have hg := cbx_le_gT (alloc (Function.update d i di)) _ hτ j0
    simp only [hz, if_true] at hg
    have := hfe _ j0 hz
    linarith
  · -- ti j0 < di j0
    obtain ⟨ε, c, hε, hc, h1, h2, h3, h4⟩ := cbx_params k (ti j0) (di j0) (hti j0) h
    let d : Fin n → Fin k → ℝ := fun m j =>
      if m = l then ε + (if j = j0 then c else 0) else di j0 + 1
    have hd : IsType d := by
      intro m j; simp only [d]; split_ifs <;> linarith [hdi j0]
    have hdl : ∀ j, Function.update d i di l j = ε + if j = j0 then c else 0 := by
      intro j; simp [hl, d]
    have hdl' : ∀ j, Function.update d i ti l j = ε + if j = j0 then c else 0 := by
      intro j; simp [hl, d]
    have hz : alloc (Function.update d i di) j0 = l := by
      by_contra hz
      have hle := hopt (Function.update d i di) (cbx_isType_update d hd i di hdi) (fun _ => l)
      have hc1 := cbx_const (Function.update d i di) l j0 ε c (di j0) (hdi j0) h3 hdl
      have hlow := cbx_le_makespan (Function.update d i di)
        (fun m j => (cbx_isType_update d hd i di hdi m j).le) (alloc (Function.update d i di)) j0
      have : di j0 ≤ Function.update d i di (alloc (Function.update d i di) j0) j0 := by
        by_cases hzi : alloc (Function.update d i di) j0 = i
        · rw [hzi]; simp
        · simp [hz, hzi, d]
      linarith
    have hA := cbx_keyA alloc hopt i ti di ei hti hdom d hd (fun j => if j = j0 then i else l)
    have hys := cbx_ystar (Function.update d i ti) i l hl j0 ε (ε + c) hε.le h4
        (by simpa using h1) (fun j hj => by rw [hdl']; simp [hj])
    have hτ : ∀ j, 0 ≤ (fun j => if alloc (Function.update d i di) j = i then
        ei (alloc (Function.update d i di)) j else d (alloc (Function.update d i di) j) j) j := by
      intro j; simp only
      split_ifs with hj
      · exact le_trans (hti j).le (hfe _ j hj)
      · exact (hd _ _).le
    have hg := cbx_le_gT (alloc (Function.update d i di)) _ hτ j0
    simp only [hz, hl, if_false, d, if_true] at hg
    linarith

theorem cb_strongly_truthful_core {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc) :
    StronglyTruthful alloc (cbPay alloc) := by
  refine ⟨cbx_truthful alloc hopt, ?_⟩
  intro i ti hti di ei hdom
  refine ⟨cbx_decl_true hn alloc hopt i ti di ei hti hdom, ?_⟩
  intro x j hj
  exact cbx_exec_min alloc hopt i ti di ei hti hdom x j hj j hj

theorem comp_bonus_strongly_truthful_core {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc) :
    StronglyTruthful alloc (cbPay alloc) ∧ ImplementsOptimum alloc (cbPay alloc) := by
  have hST := cb_strongly_truthful_core hn alloc hopt
  refine ⟨hST, ?_⟩
  intro t ht D E hDE y
  have hD : D = t := funext fun l => (hST.2 l (t l) (ht l) (D l) (E l) (hDE l)).1
  have hE := fun l => (hST.2 l (t l) (ht l) (D l) (E l) (hDE l)).2
  subst hD
  have : actualTimes alloc D E = corrStar (alloc D) D := by
    funext j; unfold actualTimes corrStar; exact hE _ _ j rfl
  rw [this, cbx_gT_corrStar]
  exact hopt D ht y

end AlgMechDesign.CompBonus

open AlgMechDesign.CompBonus


theorem solution {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hopt : IsOptimalAlloc alloc) :
    StronglyTruthful alloc (cbPay alloc) := by
  exact cb_strongly_truthful_core hn alloc hopt
