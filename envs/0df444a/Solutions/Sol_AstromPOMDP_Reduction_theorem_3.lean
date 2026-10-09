-- Prove2me | solution 1 for AstromPOMDP.Reduction.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T14:07:21.712906+00:00
-- url     : https://prove2.me/submissions/e7d7a906-7780-438f-962b-ff490f557da1

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_BeliefProcess

set_option autoImplicit false

namespace AstromPOMDP.Reduction.T3

open AstromPOMDP.Reduction

/-! ## Basic facts on `l1`, `zvec`, `bayesNext` -/

lemma l1_nonneg {St : Type*} [Fintype St] [DecidableEq St] (z : St → ℝ) : 0 ≤ l1 z :=
  Finset.sum_nonneg fun i _ => abs_nonneg (z i)

lemma eq_zero_of_l1_eq_zero {St : Type*} [Fintype St] [DecidableEq St] {z : St → ℝ} (h : l1 z = 0) : z = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (z i))).mp h i (Finset.mem_univ i)
  simpa using this

lemma l1_smul {St : Type*} [Fintype St] [DecidableEq St] (c : ℝ) (z : St → ℝ) : l1 (c • z) = |c| * l1 z := by
  unfold l1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [abs_mul]

lemma l1_of_nonneg {St : Type*} [Fintype St] [DecidableEq St] {z : St → ℝ} (h : ∀ i, 0 ≤ z i) :
    l1 z = ∑ i, z i := by
  unfold l1
  exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (h i)

lemma zvec_smul {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (u : Fin r → ℝ) (t : ℕ) (c : ℝ) (w : St → ℝ) (j : Obs) :
    zvec M u t (c • w) j = c • zvec M u t w j := by
  funext i
  simp only [zvec, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

lemma zvec_zero {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (u : Fin r → ℝ) (t : ℕ) (j : Obs) : zvec M u t 0 j = 0 := by
  funext i
  simp [zvec]

lemma zvec_nonneg {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    {u : Fin r → ℝ} {t : ℕ} {w : St → ℝ} (j : Obs) (hu : u ∈ M.U) (hw : ∀ s, 0 ≤ w s) (i : St) :
    0 ≤ zvec M u t w j i :=
  Finset.sum_nonneg fun s _ =>
    mul_nonneg (mul_nonneg (M.q_nonneg _ _) (M.P_nonneg u hu _ _ _)) (hw s)

lemma normalize_mem {St : Type*} [Fintype St] [DecidableEq St] {z : St → ℝ} (hz : ∀ i, 0 ≤ z i) (h : l1 z ≠ 0) :
    (l1 z)⁻¹ • z ∈ stdSimplex ℝ St := by
  simp only [stdSimplex, Set.mem_setOf_eq]
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (l1_nonneg z)) (hz i)
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← l1_of_nonneg hz]
    exact inv_mul_cancel₀ h

lemma bayesNext_mem {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    {u : Fin r → ℝ} {t : ℕ} {w : St → ℝ} (j : Obs) (hu : u ∈ M.U) (hw : ∀ s, 0 ≤ w s)
    (h : l1 (zvec M u t w j) ≠ 0) : bayesNext M u t w j ∈ stdSimplex ℝ St :=
  normalize_mem (zvec_nonneg M j hu hw) h

lemma bayesNext_smul {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (u : Fin r → ℝ) (t : ℕ) {c : ℝ} (hc : 0 < c) (w : St → ℝ) (j : Obs) :
    bayesNext M u t (c • w) j = bayesNext M u t w j := by
  unfold bayesNext
  rw [zvec_smul, l1_smul, abs_of_pos hc, smul_smul]
  congr 1
  rw [mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

lemma prob1_nonneg {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (j : Obs) : 0 ≤ prob1 M j :=
  Finset.sum_nonneg fun s _ => mul_nonneg (M.p₁_nonneg s) (M.q_nonneg s j)

lemma l1_a1 {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r) (j : Obs) :
    l1 (fun i => M.p₁ i * M.q i j) = prob1 M j :=
  l1_of_nonneg fun i => mul_nonneg (M.p₁_nonneg i) (M.q_nonneg i j)

lemma bayes1_mem {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (j : Obs) (h : prob1 M j ≠ 0) : bayes1 M j ∈ stdSimplex ℝ St := by
  have := normalize_mem (z := fun i => M.p₁ i * M.q i j)
    (fun i => mul_nonneg (M.p₁_nonneg i) (M.q_nonneg i j)) (by rw [l1_a1]; exact h)
  rw [l1_a1] at this
  exact this

/-! ## C3: verification for P.2 -/

lemma p2_tail_ge {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (hV : IsSolution328 M V c₀) (d : BeliefLaw St r) (hd : BeliefAdmissible M d) :
    ∀ n t : ℕ, n + t = M.N → ∀ h : Fin (t + 1) → St → ℝ, h (Fin.last t) ∈ stdSimplex ℝ St →
      V (t + 1) (h (Fin.last t)) ≤ p2Tail M d n t h := by
  intro n
  induction n with
  | zero =>
    intro t ht h hh
    have : t = M.N := by omega
    subst this
    simp [p2Tail, hV.1 _ hh]
  | succ n ih =>
    intro t ht h hh
    have hu : d (t + 1) h ∈ M.U := hd (t + 1) (by omega) (by omega) h
    have hw : ∀ s, 0 ≤ h (Fin.last t) s := hh.1
    rw [p2Tail]
    refine le_trans ((hV.2.2 (t + 1) (by omega) (by omega) _ hh).2 _ hu) ?_
    unfold bellmanRHS
    refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
    by_cases hz : l1 (zvec M (d (t + 1) h) (t + 1) (h (Fin.last t)) j) = 0
    · rw [hz]; simp
    · rw [mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (l1_nonneg _)
      have := ih (t + 1) (by omega)
        (Fin.snoc h (bayesNext M (d (t + 1) h) (t + 1) (h (Fin.last t)) j))
        (by rw [Fin.snoc_last]; exact bayesNext_mem M j hu hw hz)
      rw [Fin.snoc_last] at this
      exact this

lemma p2_tail_eq {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (hV : IsSolution328 M V c₀) :
    ∀ n t : ℕ, n + t = M.N → ∀ h : Fin (t + 1) → St → ℝ, h (Fin.last t) ∈ stdSimplex ℝ St →
      p2Tail M (markovBeliefLaw M c₀) n t h = V (t + 1) (h (Fin.last t)) := by
  intro n
  induction n with
  | zero =>
    intro t ht h hh
    have : t = M.N := by omega
    subst this
    simp [p2Tail, hV.1 _ hh]
  | succ n ih =>
    intro t ht h hh
    have hu : c₀ (h (Fin.last t)) (t + 1) ∈ M.U := hV.2.1 _ _
    have hw : ∀ s, 0 ≤ h (Fin.last t) s := hh.1
    have hm : markovBeliefLaw M c₀ (t + 1) h = c₀ (h (Fin.last t)) (t + 1) := rfl
    rw [p2Tail, (hV.2.2 (t + 1) (by omega) (by omega) _ hh).1, hm]
    unfold bellmanRHS
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hz : l1 (zvec M (c₀ (h (Fin.last t)) (t + 1)) (t + 1) (h (Fin.last t)) j) = 0
    · rw [hz]; simp
    · rw [mul_comm, ih (t + 1) (by omega) _ (by rw [Fin.snoc_last]; exact bayesNext_mem M j hu hw hz),
        Fin.snoc_last]

theorem C3 {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (hV : IsSolution328 M V c₀) :
    IsOptimalP2 M (markovBeliefLaw M c₀) ∧
      p2Cost M (markovBeliefLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) := by
  have hadm : BeliefAdmissible M (markovBeliefLaw M c₀) := by
    intro t ht _ h
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    exact hV.2.1 _ _
  have key : ∀ d, BeliefAdmissible M d → ∑ j, prob1 M j * V 1 (bayes1 M j) ≤ p2Cost M d := by
    intro d hd
    unfold p2Cost
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hp : prob1 M j = 0
    · simp [hp]
    · refine mul_le_mul_of_nonneg_left ?_ (prob1_nonneg M j)
      exact p2_tail_ge M V c₀ hV d hd M.N 0 (by omega) (fun _ => bayes1 M j) (bayes1_mem M j hp)
  have heq : p2Cost M (markovBeliefLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) := by
    unfold p2Cost
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hp : prob1 M j = 0
    · simp [hp]
    · rw [show p2Tail M (markovBeliefLaw M c₀) M.N 0 (fun _ => bayes1 M j) = V 1 (bayes1 M j) from
        p2_tail_eq M V c₀ hV M.N 0 (by omega) (fun _ => bayes1 M j) (bayes1_mem M j hp)]
  refine ⟨⟨hadm, fun d hd => ?_⟩, heq⟩
  rw [heq]
  exact key d hd

/-! ## Existence of a solution of (3.28) -/

noncomputable def F {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (k : ℕ) (W : (St → ℝ) → ℝ) (u : Fin r → ℝ) (z : St → ℝ) : ℝ :=
  ∑ i, M.g u i k * z i + ∑ j, W (zvec M u k z j)

noncomputable def Wr {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r) :
    ℕ → (St → ℝ) → ℝ
  | 0 => fun _ => 0
  | m + 1 => fun z => ⨅ u : M.U, F M (M.N - m) (Wr M m) u.1 z

lemma cont_zvec {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (k : ℕ) (j : Obs) : Continuous fun p : (St → ℝ) × M.U => zvec M p.2.1 k p.1 j := by
  have hP : ∀ s i, Continuous fun p : (St → ℝ) × M.U => M.P p.2.1 (k + 1) s i := fun s i =>
    ((M.P_cont (k + 1) s i).comp_continuous continuous_subtype_val (fun x => x.2)).comp
      continuous_snd
  refine continuous_pi fun i => ?_
  simp only [zvec]
  exact continuous_finset_sum _ fun s _ =>
    (continuous_const.mul (hP s i)).mul ((continuous_apply s).comp continuous_fst)

lemma cont_F {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (k : ℕ) (W : (St → ℝ) → ℝ) (hW : Continuous W) :
    Continuous fun p : (St → ℝ) × M.U => F M k W p.2.1 p.1 := by
  have hg : ∀ i, Continuous fun p : (St → ℝ) × M.U => M.g p.2.1 i k := fun i =>
    ((M.g_cont i k).comp_continuous continuous_subtype_val (fun x => x.2)).comp continuous_snd
  simp only [F]
  exact (continuous_finset_sum _ fun i _ => (hg i).mul ((continuous_apply i).comp continuous_fst)).add
    (continuous_finset_sum _ fun j _ => hW.comp (cont_zvec M k j))

lemma Wr_cont {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r) :
    ∀ m, Continuous (Wr M m) := by
  intro m
  induction m with
  | zero => exact continuous_const
  | succ m ih =>
    haveI : CompactSpace M.U := isCompact_iff_compactSpace.mp M.U_compact
    have := (isCompact_univ (X := M.U)).continuous_sInf
      (f := fun z (u : M.U) => F M (M.N - m) (Wr M m) u.1 z) (cont_F M _ _ ih)
    have h2 : Wr M (m + 1) =
        fun z => sInf ((fun u : M.U => F M (M.N - m) (Wr M m) u.1 z) '' Set.univ) := by
      funext z
      rw [Set.image_univ]
      rfl
    rw [h2]
    exact this

lemma Wr_smul {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r) :
    ∀ m, ∀ c : ℝ, 0 ≤ c → ∀ z, Wr M m (c • z) = c * Wr M m z := by
  intro m
  induction m with
  | zero => intro c _ z; simp [Wr]
  | succ m ih =>
    intro c hc z
    simp only [Wr]
    rw [Real.mul_iInf_of_nonneg hc]
    congr 1
    funext u
    simp only [F, zvec_smul, ih c hc, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

lemma Wr_zero_vec {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (m : ℕ) : Wr M m 0 = 0 := by
  have := Wr_smul M m 0 le_rfl 0
  simpa using this

lemma bellman_eq {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (k m : ℕ) (w : St → ℝ) (u : Fin r → ℝ) :
    bellmanRHS M k (Wr M m) w u = F M k (Wr M m) u w := by
  unfold bellmanRHS F
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hz : l1 (zvec M u k w j) = 0
  · rw [hz, eq_zero_of_l1_eq_zero hz, Wr_zero_vec]
    simp
  · unfold bayesNext
    rw [Wr_smul M m _ (inv_nonneg.mpr (l1_nonneg _)), mul_comm, ← mul_assoc, mul_inv_cancel₀ hz,
      one_mul]

lemma exists_min {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (k m : ℕ) (w : St → ℝ) : ∃ u ∈ M.U, IsMinOn (fun u => F M k (Wr M m) u w) M.U u := by
  refine M.U_compact.exists_isMinOn M.U_nonempty ?_
  rw [continuousOn_iff_continuous_restrict]
  exact (cont_F M k _ (Wr_cont M m)).comp (continuous_const.prodMk continuous_id)

noncomputable def Vs {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (k : ℕ) : (St → ℝ) → ℝ := Wr M (M.N + 1 - k)

noncomputable def cs {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (w : St → ℝ) (k : ℕ) : Fin r → ℝ := (exists_min M k (M.N - k) w).choose

theorem exists_sol {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r) :
    IsSolution328 M (Vs M) (cs M) := by
  refine ⟨fun w _ => ?_, fun w t => (exists_min M t (M.N - t) w).choose_spec.1,
    fun k hk1 hkN w _ => ?_⟩
  · simp [Vs, Wr]
  · have hm : M.N + 1 - k = (M.N - k) + 1 := by omega
    have hk : M.N - (M.N - k) = k := by omega
    have hk1' : M.N + 1 - (k + 1) = M.N - k := by omega
    have spec : cs M w k ∈ M.U ∧ IsMinOn (fun u => F M k (Wr M (M.N - k)) u w) M.U (cs M w k) :=
      (exists_min M k (M.N - k) w).choose_spec
    have hV : Vs M k w = ⨅ u : M.U, F M k (Wr M (M.N - k)) u.1 w := by
      simp only [Vs]
      rw [hm]
      simp only [Wr, hk]
    have hV1 : Vs M (k + 1) = Wr M (M.N - k) := by
      simp only [Vs]
      rw [hk1']
    have : Nonempty M.U := M.U_nonempty.to_subtype
    have hbdd : BddBelow (Set.range fun u : M.U => F M k (Wr M (M.N - k)) u.1 w) :=
      ⟨F M k (Wr M (M.N - k)) (cs M w k) w, by rintro _ ⟨u, rfl⟩; exact spec.2 u.2⟩
    have hinf : (⨅ u : M.U, F M k (Wr M (M.N - k)) u.1 w) = F M k (Wr M (M.N - k)) (cs M w k) w :=
      le_antisymm (ciInf_le hbdd ⟨cs M w k, spec.1⟩) (le_ciInf fun u => spec.2 u.2)
    rw [hV, hV1, hinf]
    refine ⟨by rw [bellman_eq], fun u hu => ?_⟩
    rw [bellman_eq]
    exact spec.2 hu

/-! ## C2: verification for P.1 -/

/-- Unnormalized forward vector: `alpha t η s = P(x_t = s, y₁..y_t = η)`. -/
noncomputable def alpha {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (c : ControlLaw Obs r) : (t : ℕ) → (Fin t → Obs) → St → ℝ
  | 0, _ => fun _ => 0
  | 1, η => fun i => M.p₁ i * M.q i (η 0)
  | t + 2, η => zvec M (c (t + 1) (Fin.init η)) (t + 1) (alpha M c (t + 1) (Fin.init η))
      (η (Fin.last (t + 1)))

lemma alpha_two {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (c : ControlLaw Obs r) (n : ℕ) (y : Fin (n + 1 + 1) → Obs) :
    alpha M c (n + 1 + 1) y = zvec M (c (n + 1) (Fin.init y)) (n + 1) (alpha M c (n + 1) (Fin.init y))
      (y (Fin.last (n + 1))) := rfl

lemma alpha_snoc {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (c : ControlLaw Obs r) (n : ℕ) (y : Fin (n + 1) → Obs) (b : Obs) :
    alpha M c (n + 1 + 1) (Fin.snoc y b) = zvec M (c (n + 1) y) (n + 1) (alpha M c (n + 1) y) b := by
  rw [alpha_two, Fin.init_snoc, Fin.snoc_last]

lemma alpha_nonneg {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (c : ControlLaw Obs r) (hc : Admissible M c) :
    ∀ n, n ≤ M.N → ∀ (y : Fin (n + 1) → Obs) (s : St), 0 ≤ alpha M c (n + 1) y s := by
  intro n
  induction n with
  | zero => intro _ y s; exact mul_nonneg (M.p₁_nonneg s) (M.q_nonneg s _)
  | succ n ih =>
    intro hn y s
    rw [alpha_two]
    exact zvec_nonneg M _ (hc (n + 1) (by omega) hn _) (ih (by omega) _) s

lemma sum_snoc' {α : Type*} [Fintype α] {n : ℕ} (f : (Fin (n + 1) → α) → ℝ) :
    ∑ x, f x = ∑ x' : Fin n → α, ∑ a : α, f (Fin.snoc x' a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

lemma pathProb_snoc {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (c : ControlLaw Obs r) (n : ℕ) (x : Fin (n + 1) → St) (a : St) (y : Fin (n + 1 + 1) → Obs) :
    pathProb M c (n + 1 + 1) (Fin.snoc x a) y = pathProb M c (n + 1) x (Fin.init y) *
      M.P (c (n + 1) (Fin.init y)) (n + 1 + 1) (x (Fin.last n)) a * M.q a (y (Fin.last (n + 1))) := by
  show pathProb M c (n + 1) (Fin.init (Fin.snoc x a : Fin (n + 2) → St)) (Fin.init y) *
      M.P (c (n + 1) (Fin.init y)) (n + 2) ((Fin.snoc x a : Fin (n + 2) → St) (Fin.last n).castSucc)
        ((Fin.snoc x a : Fin (n + 2) → St) (Fin.last (n + 1))) *
      M.q ((Fin.snoc x a : Fin (n + 2) → St) (Fin.last (n + 1))) (y (Fin.last (n + 1))) = _
  rw [Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]

lemma marg_last {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (c : ControlLaw Obs r) :
    ∀ n (y : Fin (n + 1) → Obs) (s : St),
      ∑ x : Fin (n + 1) → St, (if x (Fin.last n) = s then pathProb M c (n + 1) x y else 0) =
        alpha M c (n + 1) y s := by
  intro n
  induction n with
  | zero =>
    intro y s
    rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) St)
      (fun x : Fin (0 + 1) → St => if x (Fin.last 0) = s then pathProb M c (0 + 1) x y else 0)
      (fun a => if a = s then M.p₁ a * M.q a (y 0) else 0) (fun x => rfl)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  | succ n ih =>
    intro y s
    rw [alpha_two]
    simp only [zvec, ← ih, Finset.mul_sum, mul_ite, mul_zero]
    rw [sum_snoc']
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x' _ => ?_
    simp only [Fin.snoc_last, pathProb_snoc, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    ring

lemma marg {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (c : ControlLaw Obs r) (m : ℕ) (hU : ∀ y' : Fin (m + 1) → Obs, c (m + 1) y' ∈ M.U)
    (G : (Fin (m + 1) → St) → (Fin (m + 1) → Obs) → ℝ) :
    ∑ x : Fin (m + 1 + 1) → St, ∑ y : Fin (m + 1 + 1) → Obs,
        pathProb M c (m + 1 + 1) x y * G (Fin.init x) (Fin.init y) =
      ∑ x' : Fin (m + 1) → St, ∑ y' : Fin (m + 1) → Obs, pathProb M c (m + 1) x' y' * G x' y' := by
  simp only [sum_snoc' (n := m + 1) (α := St), sum_snoc' (n := m + 1) (α := Obs), pathProb_snoc,
    Fin.init_snoc, Fin.snoc_last]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y' _ => ?_
  have hP := M.P_sum _ (hU y') (m + 1 + 1) (x' (Fin.last m))
  rw [show pathProb M c (m + 1) x' y' * G x' y' = ∑ a, ∑ b, pathProb M c (m + 1) x' y' * G x' y' *
      (M.P (c (m + 1) y') (m + 1 + 1) (x' (Fin.last m)) a * M.q a b) by
    simp only [← Finset.mul_sum, M.q_sum, mul_one, hP]]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

noncomputable def costN {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (c : ControlLaw Obs r) (n : ℕ) : ℝ :=
  ∑ x : Fin n → St, ∑ y : Fin n → Obs, pathProb M c n x y *
    ∑ i : Fin n, M.g (c (i.val + 1) (Fin.take (i.val + 1) i.isLt y)) (x i) (i.val + 1)

noncomputable def stepCost {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (c : ControlLaw Obs r) (t : ℕ) : ℝ :=
  ∑ y : Fin t → Obs, ∑ s, M.g (c t y) s t * alpha M c t y s

lemma costN_succ {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (c : ControlLaw Obs r) (hc : Admissible M c) (n : ℕ) (hn : n + 1 ≤ M.N) :
    costN M c (n + 1) = costN M c n + stepCost M c (n + 1) := by
  have part2 : ∑ x : Fin (n + 1) → St, ∑ y : Fin (n + 1) → Obs, pathProb M c (n + 1) x y *
      M.g (c ((Fin.last n).val + 1) (Fin.take ((Fin.last n).val + 1) (Fin.last n).isLt y))
        (x (Fin.last n)) ((Fin.last n).val + 1) = stepCost M c (n + 1) := by
    unfold stepCost
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [← marg_last, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact mul_comm _ _
  have part1 : ∑ x : Fin (n + 1) → St, ∑ y : Fin (n + 1) → Obs, pathProb M c (n + 1) x y *
      ∑ i : Fin n, M.g (c ((Fin.castSucc i).val + 1)
        (Fin.take ((Fin.castSucc i).val + 1) (Fin.castSucc i).isLt y))
          (x (Fin.castSucc i)) ((Fin.castSucc i).val + 1) = costN M c n := by
    cases n with
    | zero => simp [costN]
    | succ m =>
      exact marg M c m (fun y' => hc (m + 1) (by omega) (by omega) y')
        (fun x' y' => ∑ i : Fin (m + 1),
          M.g (c (i.val + 1) (Fin.take (i.val + 1) i.isLt y')) (x' i) (i.val + 1))
  rw [← part1, ← part2]
  unfold costN
  simp only [Fin.sum_univ_castSucc, mul_add, Finset.sum_add_distrib]

/-- Homogeneous extension of `V`. -/
noncomputable def W {St : Type*} [Fintype St] [DecidableEq St] (V : ℕ → (St → ℝ) → ℝ) (t : ℕ) (z : St → ℝ) : ℝ :=
  l1 z * V t ((l1 z)⁻¹ • z)

noncomputable def Φ {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (c : ControlLaw Obs r) (t : ℕ) : ℝ :=
  ∑ y : Fin t → Obs, W V t (alpha M c t y)

lemma key_id {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (t : ℕ) (u : Fin r → ℝ) (z : St → ℝ) (hz : l1 z ≠ 0) :
    l1 z * bellmanRHS M t (V (t + 1)) ((l1 z)⁻¹ • z) u =
      ∑ i, M.g u i t * z i + ∑ j, W V (t + 1) (zvec M u t z j) := by
  have hL : 0 < l1 z := lt_of_le_of_ne (l1_nonneg z) (Ne.symm hz)
  unfold bellmanRHS W
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [bayesNext_smul M u t (inv_pos.mpr hL), zvec_smul, l1_smul, abs_of_pos (inv_pos.mpr hL)]
    unfold bayesNext
    field_simp

lemma W_zero {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (t : ℕ) (u : Fin r → ℝ) :
    W V t (0 : St → ℝ) = ∑ i, M.g u i t * (0 : St → ℝ) i +
      ∑ j, W V (t + 1) (zvec M u t (0 : St → ℝ) j) := by
  simp [W, l1, zvec_zero]

lemma W_le {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) (hV : IsSolution328 M V c₀)
    (t : ℕ) (h1 : 1 ≤ t) (hN : t ≤ M.N) (z : St → ℝ) (hz : ∀ i, 0 ≤ z i) (u : Fin r → ℝ)
    (hu : u ∈ M.U) :
    W V t z ≤ ∑ i, M.g u i t * z i + ∑ j, W V (t + 1) (zvec M u t z j) := by
  by_cases h0 : l1 z = 0
  · have hz0 := eq_zero_of_l1_eq_zero h0
    subst hz0
    exact le_of_eq (W_zero M V t u)
  · have hw := normalize_mem hz h0
    calc W V t z = l1 z * V t ((l1 z)⁻¹ • z) := rfl
      _ ≤ l1 z * bellmanRHS M t (V (t + 1)) ((l1 z)⁻¹ • z) u :=
          mul_le_mul_of_nonneg_left ((hV.2.2 t h1 hN _ hw).2 u hu) (l1_nonneg z)
      _ = _ := key_id M V t u z h0

lemma W_eq {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) (hV : IsSolution328 M V c₀)
    (t : ℕ) (h1 : 1 ≤ t) (hN : t ≤ M.N) (z : St → ℝ) (hz : ∀ i, 0 ≤ z i) (u : Fin r → ℝ)
    (hu : l1 z ≠ 0 → u = c₀ ((l1 z)⁻¹ • z) t) :
    W V t z = ∑ i, M.g u i t * z i + ∑ j, W V (t + 1) (zvec M u t z j) := by
  by_cases h0 : l1 z = 0
  · have hz0 := eq_zero_of_l1_eq_zero h0
    subst hz0
    exact W_zero M V t u
  · have hw := normalize_mem hz h0
    rw [hu h0]
    calc W V t z = l1 z * V t ((l1 z)⁻¹ • z) := rfl
      _ = l1 z * bellmanRHS M t (V (t + 1)) ((l1 z)⁻¹ • z) (c₀ ((l1 z)⁻¹ • z) t) := by
          rw [(hV.2.2 t h1 hN _ hw).1]
      _ = _ := key_id M V t _ z h0

lemma Phi_succ {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (c : ControlLaw Obs r) (n : ℕ) :
    Φ M V c (n + 1 + 1) = ∑ y' : Fin (n + 1) → Obs, ∑ b,
      W V (n + 1 + 1) (zvec M (c (n + 1) y') (n + 1) (alpha M c (n + 1) y') b) := by
  unfold Φ
  rw [sum_snoc']
  simp only [alpha_snoc]

lemma Phi_step {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) (c : ControlLaw Obs r)
    (hV : IsSolution328 M V c₀) (hc : Admissible M c) (n : ℕ) (hn : n + 1 ≤ M.N) :
    Φ M V c (n + 1) ≤ stepCost M c (n + 1) + Φ M V c (n + 1 + 1) := by
  rw [Phi_succ]
  unfold Φ stepCost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y' _ => ?_
  exact W_le M V c₀ hV (n + 1) (by omega) hn _ (alpha_nonneg M c hc n (by omega) y') _
    (hc (n + 1) (by omega) hn y')

lemma belief_eq {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) :
    ∀ n (y : Fin (n + 1) → Obs), l1 (alpha M (markovLaw M c₀) (n + 1) y) ≠ 0 →
      markovBelief M c₀ (n + 1) y =
        (l1 (alpha M (markovLaw M c₀) (n + 1) y))⁻¹ • alpha M (markovLaw M c₀) (n + 1) y := by
  intro n
  induction n with
  | zero =>
    intro y _
    show (prob1 M (y 0))⁻¹ • (fun i => M.p₁ i * M.q i (y 0)) =
      (l1 (fun i => M.p₁ i * M.q i (y 0)))⁻¹ • (fun i => M.p₁ i * M.q i (y 0))
    rw [l1_a1]
  | succ n ih =>
    intro y hy
    have ha' : l1 (alpha M (markovLaw M c₀) (n + 1) (Fin.init y)) ≠ 0 := by
      intro h0
      apply hy
      rw [alpha_two, eq_zero_of_l1_eq_zero h0, zvec_zero]
      simp [l1]
    have hL : 0 < l1 (alpha M (markovLaw M c₀) (n + 1) (Fin.init y)) :=
      lt_of_le_of_ne (l1_nonneg _) (Ne.symm ha')
    show bayesNext M (c₀ (markovBelief M c₀ (n + 1) (Fin.init y)) (n + 1)) (n + 1)
        (markovBelief M c₀ (n + 1) (Fin.init y)) (y (Fin.last (n + 1))) =
      (l1 (zvec M (c₀ (markovBelief M c₀ (n + 1) (Fin.init y)) (n + 1)) (n + 1)
        (alpha M (markovLaw M c₀) (n + 1) (Fin.init y)) (y (Fin.last (n + 1)))))⁻¹ •
        zvec M (c₀ (markovBelief M c₀ (n + 1) (Fin.init y)) (n + 1)) (n + 1)
          (alpha M (markovLaw M c₀) (n + 1) (Fin.init y)) (y (Fin.last (n + 1)))
    rw [ih (Fin.init y) ha', bayesNext_smul M _ _ (inv_pos.mpr hL)]
    rfl

lemma Phi_step_eq {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (hV : IsSolution328 M V c₀) (n : ℕ) (hn : n + 1 ≤ M.N) :
    Φ M V (markovLaw M c₀) (n + 1) =
      stepCost M (markovLaw M c₀) (n + 1) + Φ M V (markovLaw M c₀) (n + 1 + 1) := by
  have hc : Admissible M (markovLaw M c₀) := fun t _ _ η => hV.2.1 _ _
  rw [Phi_succ]
  unfold Φ stepCost
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y' _ => ?_
  refine W_eq M V c₀ hV (n + 1) (by omega) hn _ (alpha_nonneg M _ hc n (by omega) y') _
    (fun h => ?_)
  show c₀ (markovBelief M c₀ (n + 1) y') (n + 1) = _
  rw [belief_eq M c₀ n y' h]

lemma Phi_last {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) (c : ControlLaw Obs r)
    (hV : IsSolution328 M V c₀) (hc : Admissible M c) : Φ M V c (M.N + 1) = 0 := by
  unfold Φ
  refine Finset.sum_eq_zero fun y _ => ?_
  unfold W
  by_cases h0 : l1 (alpha M c (M.N + 1) y) = 0
  · rw [h0, zero_mul]
  · rw [hV.1 _ (normalize_mem (alpha_nonneg M c hc M.N le_rfl y) h0), mul_zero]

lemma Phi_one {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ} (M : Model St Obs r)
    (V : ℕ → (St → ℝ) → ℝ) (c : ControlLaw Obs r) :
    Φ M V c 1 = ∑ j, prob1 M j * V 1 (bayes1 M j) := by
  unfold Φ
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) Obs) _ _ fun y => ?_
  show l1 (fun i => M.p₁ i * M.q i (y 0)) * V 1 ((l1 (fun i => M.p₁ i * M.q i (y 0)))⁻¹ •
      (fun i => M.p₁ i * M.q i (y 0))) = prob1 M (y 0) * V 1 (bayes1 M (y 0))
  rw [l1_a1]
  rfl

lemma tele_le {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (c : ControlLaw Obs r) (hV : IsSolution328 M V c₀) (hc : Admissible M c) :
    ∀ n, n ≤ M.N → Φ M V c 1 ≤ costN M c n + Φ M V c (n + 1) := by
  intro n
  induction n with
  | zero => intro _; simp [costN]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := Phi_step M V c₀ c hV hc n hn
    rw [costN_succ M c hc n hn]
    linarith

lemma tele_eq {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (hV : IsSolution328 M V c₀) :
    ∀ n, n ≤ M.N → Φ M V (markovLaw M c₀) 1 =
      costN M (markovLaw M c₀) n + Φ M V (markovLaw M c₀) (n + 1) := by
  have hc : Admissible M (markovLaw M c₀) := fun t _ _ η => hV.2.1 _ _
  intro n
  induction n with
  | zero => intro _; simp [costN]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 := Phi_step_eq M V c₀ hV n hn
    rw [costN_succ M _ hc n hn]
    linarith

theorem C2 {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (hV : IsSolution328 M V c₀) :
    IsOptimalP1 M (markovLaw M c₀) ∧
      expectedCost M (markovLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) := by
  have hadm : Admissible M (markovLaw M c₀) := fun t _ _ η => hV.2.1 _ _
  have hlow : ∀ c, Admissible M c → ∑ j, prob1 M j * V 1 (bayes1 M j) ≤ expectedCost M c := by
    intro c hc
    have := tele_le M V c₀ c hV hc M.N le_rfl
    rw [Phi_last M V c₀ c hV hc, Phi_one M V c, add_zero] at this
    exact this
  have heq : expectedCost M (markovLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) := by
    have := tele_eq M V c₀ hV M.N le_rfl
    rw [Phi_last M V c₀ _ hV hadm, Phi_one M V, add_zero] at this
    exact this.symm
  refine ⟨⟨hadm, fun c hc => ?_⟩, heq⟩
  rw [heq]
  exact hlow c hc

end AstromPOMDP.Reduction.T3

open AstromPOMDP.Reduction in
theorem solution {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) :
    ((∃ c : ControlLaw Obs r, IsOptimalP1 M c) ↔ (∃ d : BeliefLaw St r, IsOptimalP2 M d)) ∧
    ∀ (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)), IsSolution328 M V c₀ →
      IsOptimalP1 M (markovLaw M c₀) ∧ IsOptimalP2 M (markovBeliefLaw M c₀) ∧
        expectedCost M (markovLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) ∧
        p2Cost M (markovBeliefLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) := by
  have hs := AstromPOMDP.Reduction.T3.exists_sol M
  refine ⟨⟨fun _ => ⟨_, (AstromPOMDP.Reduction.T3.C3 M _ _ hs).1⟩,
    fun _ => ⟨_, (AstromPOMDP.Reduction.T3.C2 M _ _ hs).1⟩⟩, fun V c₀ hV => ?_⟩
  obtain ⟨h1, h2⟩ := AstromPOMDP.Reduction.T3.C2 M V c₀ hV
  obtain ⟨h3, h4⟩ := AstromPOMDP.Reduction.T3.C3 M V c₀ hV
  exact ⟨h1, h3, h2, h4⟩
