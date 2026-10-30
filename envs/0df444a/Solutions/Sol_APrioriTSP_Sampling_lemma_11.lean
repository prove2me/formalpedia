-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T14:44:39.407261+00:00
-- url     : https://prove2.me/submissions/43569deb-675b-43a3-b1c5-d47f22824684

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP
import Theorems.Thm_APrioriTSP_Sampling_proposition_10
import Theorems.Thm_APrioriTSP_Sampling_lemma_11_connection

open APrioriTSP.Sampling Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace APTSPL11

variable {V : Type} [Fintype V] [DecidableEq V]

theorem c_nonneg {c : V → V → ℝ} {p : V → ℝ} {d : V} (hI : IsDepotInstance c p d) (u v : V) :
    0 ≤ c u v := by
  have h1 := hI.c_triangle u v u
  rw [hI.c_self u, hI.c_symm v u] at h1
  linarith

theorem subsetProb_nonneg (q : V → ℝ) (hq : ∀ v, 0 ≤ q v ∧ q v ≤ 1) (A : Finset V) :
    0 ≤ subsetProb q A := by
  unfold subsetProb
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun v _ => (hq v).1)
  · exact Finset.prod_nonneg (fun v _ => by linarith [(hq v).2])

theorem cycleCost_nonneg (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (l : List V) :
    0 ≤ cycleCost c l := by
  unfold cycleCost
  apply List.sum_nonneg
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨e, _, rfl⟩ := hx
  exact hc _ _

theorem aPrioriCost_nonneg (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (q : V → ℝ)
    (hq : ∀ v, 0 ≤ q v ∧ q v ≤ 1) (T : List V) : 0 ≤ aPrioriCost c q T := by
  unfold aPrioriCost
  exact Finset.sum_nonneg (fun A _ =>
    mul_nonneg (subsetProb_nonneg q hq A) (cycleCost_nonneg c hc _))

/-- path cost of a list -/
def pathCost (c : V → V → ℝ) : List V → ℝ
  | [] => 0
  | [_] => 0
  | x :: y :: l => c x y + pathCost c (y :: l)

theorem zip_sum_eq_pathCost (c : V → V → ℝ) (y : V) :
    ∀ (F : List V) (x : V), (((x :: F).zip (F ++ [y])).map (fun e => c e.1 e.2)).sum =
      pathCost c (x :: F ++ [y]) := by
  intro F
  induction F with
  | nil => intro x; simp [pathCost]
  | cons z F ih =>
    intro x
    have := ih z
    simp only [List.cons_append, List.zip_cons_cons, List.map_cons, List.sum_cons] at this ⊢
    rw [this]
    simp [pathCost]

theorem cycleCost_cons (c : V → V → ℝ) (x : V) (F : List V) :
    cycleCost c (x :: F) = pathCost c (x :: F ++ [x]) := by
  unfold cycleCost
  rw [List.rotate_cons_succ, List.rotate_zero]
  exact zip_sum_eq_pathCost c x F x

theorem pathCost_append_single (c : V → V → ℝ) (z : V) :
    ∀ (L : List V) (u : V), pathCost c ((u :: L) ++ [z]) =
      pathCost c (u :: L) + c ((u :: L).getLast (by simp)) z := by
  intro L
  induction L with
  | nil => intro u; simp [pathCost]
  | cons v L ih =>
    intro u
    have := ih v
    simp only [List.cons_append] at this ⊢
    rw [show pathCost c (u :: v :: (L ++ [z])) = c u v + pathCost c (v :: (L ++ [z])) from rfl,
      this, List.getLast_cons_cons]
    rw [show pathCost c (u :: v :: L) = c u v + pathCost c (v :: L) from rfl]
    ring

theorem pathCost_cons_cons (c : V → V → ℝ) (x y : V) (L : List V) :
    pathCost c (x :: y :: L) = c x y + pathCost c (y :: L) := rfl

theorem cycleCost_rotate_one (c : V → V → ℝ) (l : List V) :
    cycleCost c (l.rotate 1) = cycleCost c l := by
  rcases l with _ | ⟨x, t⟩
  · rfl
  · rw [List.rotate_cons_succ, List.rotate_zero]
    rcases t with _ | ⟨y, t⟩
    · rfl
    · rw [List.cons_append, cycleCost_cons, cycleCost_cons]
      have h1 := pathCost_append_single c y (t ++ [x]) y
      have hl : (y :: (t ++ [x])).getLast (by simp) = x := by simp
      rw [hl] at h1
      simp only [List.cons_append, List.append_assoc] at h1 ⊢
      rw [h1, pathCost_cons_cons]; ring

theorem cycleCost_filter_rotate_one (c : V → V → ℝ) (A : Finset V) (l : List V) :
    cycleCost c ((l.rotate 1).filter (· ∈ A)) = cycleCost c (l.filter (· ∈ A)) := by
  rcases l with _ | ⟨x, t⟩
  · rfl
  · rw [List.rotate_cons_succ, List.rotate_zero, List.filter_append]
    by_cases hx : x ∈ A
    · have e1 : List.filter (fun x => decide (x ∈ A)) [x] = [x] := by simp [hx]
      have e2 : List.filter (fun x => decide (x ∈ A)) (x :: t) =
          x :: List.filter (fun x => decide (x ∈ A)) t := by simp [hx]
      rw [e1, e2, ← cycleCost_rotate_one c (x :: List.filter (fun x => decide (x ∈ A)) t),
        List.rotate_cons_succ, List.rotate_zero]
    · have e1 : List.filter (fun x => decide (x ∈ A)) [x] = [] := by simp [hx]
      have e2 : List.filter (fun x => decide (x ∈ A)) (x :: t) =
          List.filter (fun x => decide (x ∈ A)) t := by simp [hx]
      rw [e1, e2, List.append_nil]

theorem aPrioriCost_rotate (c : V → V → ℝ) (q : V → ℝ) (l : List V) (m : ℕ) :
    aPrioriCost c q (l.rotate m) = aPrioriCost c q l := by
  induction m with
  | zero => rw [List.rotate_zero]
  | succ k ih =>
    rw [← List.rotate_rotate, ← ih]
    unfold aPrioriCost
    apply Finset.sum_congr rfl
    intro A _
    rw [cycleCost_filter_rotate_one]

theorem tours_finite : {T : List V | IsTour T}.Finite := by
  apply Set.Finite.subset (List.toFinset ((Finset.univ : Finset V).toList.permutations)).finite_toSet
  intro T hT
  simp only [Set.mem_ofPred_eq] at hT
  simp only [Finset.coe_sort_coe, List.coe_toFinset, Set.mem_ofPred_eq, List.mem_permutations]
  rw [List.perm_ext_iff_of_nodup hT.1 (Finset.nodup_toList _)]
  intro a; simp [hT.2 a]

theorem exists_opt_tour (c : V → V → ℝ) (q : V → ℝ) (d : V) :
    ∃ T : List V, IsTour T ∧ T.head? = some d ∧ aPrioriCost c q T = aPrioriOpt c q := by
  have hne : {T : List V | IsTour T}.Nonempty :=
    ⟨(Finset.univ : Finset V).toList, Finset.nodup_toList _, fun v => by simp⟩
  obtain ⟨T0, hT0, hmin⟩ := Set.exists_min_image _ (aPrioriCost c q) tours_finite hne
  have hopt : aPrioriOpt c q = aPrioriCost c q T0 := by
    unfold aPrioriOpt
    apply le_antisymm
    · apply csInf_le ((tours_finite.image _).bddBelow) (Set.mem_image_of_mem _ hT0)
    · apply le_csInf (hne.image _)
      rintro _ ⟨T, hT, rfl⟩
      exact hmin T hT
  have hdT : d ∈ T0 := hT0.2 d
  refine ⟨T0.rotate (T0.idxOf d), ⟨List.nodup_rotate.2 hT0.1, fun v => List.mem_rotate.2 (hT0.2 v)⟩,
    ?_, by rw [aPrioriCost_rotate, hopt]⟩
  rw [List.rotate_eq_drop_append_take (le_of_lt (List.idxOf_lt_length_iff.2 hdT)),
    List.head?_append, List.head?_drop, List.getElem?_idxOf hdT]
  rfl

theorem tspOpt_le (c : V → V → ℝ) (T : List V) (hT : IsTour T) (S : Finset V) :
    tspOpt c S ≤ cycleCost c (T.filter (· ∈ S)) := by
  unfold tspOpt
  have hfin : {l : List V | l.Nodup ∧ l.toFinset = S}.Finite := by
    apply Set.Finite.subset (List.toFinset (S.toList.permutations)).finite_toSet
    intro l hl
    simp only [Set.mem_ofPred_eq] at hl
    simp only [List.coe_toFinset, Set.mem_ofPred_eq, List.mem_permutations]
    rw [List.perm_ext_iff_of_nodup hl.1 (Finset.nodup_toList _)]
    intro a
    rw [Finset.mem_toList, ← hl.2, List.mem_toFinset]
  apply csInf_le (hfin.image _).bddBelow
  refine Set.mem_image_of_mem _ ⟨hT.1.filter _, ?_⟩
  ext v
  simp [List.mem_filter, hT.2 v]

theorem hopC_scale (c : V → V → ℝ) (σ p : ℝ) (d : V) (T : List V) (k : ℕ) :
    hopC c (σ * p) d T k = σ ^ 2 * hopC c p d T k := by
  unfold hopC; ring

theorem tourVertex_out (d : V) (T : List V) (hd : T.head? = some d) (j : ℤ)
    (hj : j < 0 ∨ (T.length : ℤ) ≤ j) : tourVertex d T j = d := by
  unfold tourVertex
  split_ifs with h
  · apply List.getD_eq_default
    omega
  · rfl

theorem hopC_window (c : V → V → ℝ) (p : ℝ) (d : V) (T : List V) (hd : T.head? = some d)
    (hcdd : c d d = 0) (k K : ℕ) (M : ℤ) (hK : k ≤ K) (hM : (T.length : ℤ) - 1 ≤ M) :
    hopC c p d T k = p ^ 2 * ∑ j ∈ Finset.Icc (-(K : ℤ)) M,
      c (tourVertex d T j) (tourVertex d T (j + k)) := by
  unfold hopC
  congr 1
  apply Finset.sum_subset
  · intro j hj; simp at hj ⊢; omega
  · intro j hj hnj
    simp at hj hnj
    rcases lt_or_ge j (-(k : ℤ)) with h | h
    · rw [tourVertex_out d T hd j (Or.inl (by omega)),
        tourVertex_out d T hd (j + k) (Or.inl (by omega)), hcdd]
    · have := hnj h
      rw [tourVertex_out d T hd j (Or.inr (by omega)),
        tourVertex_out d T hd (j + k) (Or.inr (by omega)), hcdd]

theorem hopC_nonneg (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (p : ℝ) (d : V) (T : List V)
    (k : ℕ) : 0 ≤ hopC c p d T k := by
  unfold hopC
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => hc _ _))

theorem hopC_triangle {pf : V → ℝ} (c : V → V → ℝ) (p : ℝ) (d : V)
    (hI : IsDepotInstance c pf d) (T : List V) (hd : T.head? = some d) (i j : ℕ) :
    hopC c p d T (i + j) ≤ hopC c p d T i + hopC c p d T j := by
  have hcdd : c d d = 0 := hI.c_self d
  rw [hopC_window c p d T hd hcdd i (i + j) ((T.length : ℤ) - 1) (by omega) le_rfl,
    hopC_window c p d T hd hcdd j j ((T.length : ℤ) - 1 + i) le_rfl (by omega)]
  unfold hopC
  rw [← mul_add]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg p)
  have hshift : ∑ l ∈ Finset.Icc (-((i + j : ℕ) : ℤ)) ((T.length : ℤ) - 1),
      c (tourVertex d T (l + i)) (tourVertex d T (l + i + j)) =
      ∑ l ∈ Finset.Icc (-(j : ℤ)) ((T.length : ℤ) - 1 + i),
        c (tourVertex d T l) (tourVertex d T (l + j)) := by
    apply Finset.sum_nbij' (fun l : ℤ => l + (i : ℤ)) (fun l : ℤ => l - (i : ℤ))
    · intro l hl; simp at hl ⊢; omega
    · intro l hl; simp at hl ⊢; omega
    · intro l _; simp
    · intro l _; simp
    · intro l _; rfl
  rw [← hshift, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l _
  have := hI.c_triangle (tourVertex d T l) (tourVertex d T (l + i)) (tourVertex d T (l + i + j))
  have e : l + ((i + j : ℕ) : ℤ) = l + i + j := by push_cast; ring
  rw [e]; exact this

end APTSPL11

open APTSPL11 in
theorem solution (α σ p μ : ℝ) (hα : 0 ≤ α) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ : 0 < μ)
    (hval : ∀ C : ℕ → ℝ, SamplingOPFeasible α σ p C → μ ≤ samplingOPObj p C) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (pf : V → ℝ) (d : V),
      IsNormalized c pf d p →
      samplingCost α (linSampling σ) c pf ≤ μ⁻¹ * aPrioriOpt c pf := by
  intro V _ _ c pf d hnorm
  obtain ⟨hI, hnp⟩ := hnorm
  have hc := c_nonneg hI
  have hcdd : c d d = 0 := hI.c_self d
  have hpf : ∀ v, 0 ≤ pf v ∧ pf v ≤ 1 := fun v => ⟨(hI.p_pos v).le, hI.p_le_one v⟩
  obtain ⟨T, hT, hTd, hTopt⟩ := exists_opt_tour c pf d
  set q : V → ℝ := fun v => linSampling σ (pf v) with hq
  have hσp0 : 0 < σ * p := mul_pos hσ0 hp0
  have hσp1 : σ * p < 1 := by nlinarith
  have hqd : q d = 1 := by simp [hq, linSampling, hI.p_depot]
  have hqv : ∀ v, v ≠ d → q v = σ * p := by
    intro v hv
    simp only [hq, linSampling, hnp v hv]
    rw [if_neg (by linarith)]
  have hq01 : ∀ v, 0 < q v ∧ q v ≤ 1 := by
    intro v
    by_cases hv : v = d
    · rw [hv, hqd]; norm_num
    · rw [hqv v hv]; exact ⟨hσp0, hσp1.le⟩
  have hqI : IsNormalized c q d (σ * p) :=
    ⟨⟨hI.c_self, hI.c_symm, hI.c_triangle, fun v => (hq01 v).1, fun v => (hq01 v).2, hqd⟩, hqv⟩
  set C : ℕ → ℝ := fun k => hopC c p d T k with hC
  have hC0 : ∀ k, 0 ≤ C k := fun k => hopC_nonneg c hc p d T k
  have hCt : ∀ i j, C (i + j) ≤ C i + C j := fun i j => hopC_triangle c p d hI T hTd i j
  have hClin : ∀ k : ℕ, C (k + 1) ≤ ((k : ℝ) + 1) * C 1 := by
    intro k
    induction k with
    | zero => simp
    | succ m ih =>
      have := hCt (m + 1) 1
      push_cast
      linarith
  set r : ℝ := 1 - σ * p with hr
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hnorm_r : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  -- a summable majorant
  have hmaj : ∀ K : ℝ, Summable (fun k : ℕ => r ^ k * (((k : ℝ) + 1) ^ 2 * K)) := by
    intro K
    have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hnorm_r
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hnorm_r
    have h0 := summable_geometric_of_lt_one hr0 hr1
    have := ((h2.add (h1.mul_left 2)).add h0).mul_right K
    refine this.congr (fun k => ?_)
    ring
  have hsumM : Summable (fun i : ℕ => r ^ i * C (i + 1)) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (pow_nonneg hr0 _) (hC0 _)) _ (hmaj (C 1))
    intro i
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 _)
    have := hClin i
    have h1 : ((i : ℝ) + 1) ≤ ((i : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [hC0 1]
  have hminle : ∀ k, ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) ≤
      ((k : ℝ) + 1) ^ 2 * C 1 := by
    intro k
    have hb : ∀ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) ≤ ((k : ℝ) + 1) * C 1 := by
      intro i hi
      simp at hi
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have := hClin i'
      have hle : ((i' : ℝ) + 1) ≤ (k : ℝ) + 1 := by
        have : (i' : ℝ) + 1 ≤ k := by exact_mod_cast hi.2
        linarith
      calc min (C (i' + 1)) (C (k + 1 - (i' + 1))) ≤ C (i' + 1) := min_le_left _ _
        _ ≤ ((i' : ℝ) + 1) * C 1 := this
        _ ≤ ((k : ℝ) + 1) * C 1 := mul_le_mul_of_nonneg_right hle (hC0 1)
    calc ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))
        ≤ ∑ i ∈ Finset.Icc 1 k, ((k : ℝ) + 1) * C 1 := Finset.sum_le_sum hb
      _ = (k : ℝ) * (((k : ℝ) + 1) * C 1) := by simp
      _ ≤ ((k : ℝ) + 1) ^ 2 * C 1 := by nlinarith [hC0 1]
  have hsumN : Summable (fun k : ℕ => r ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := by
    apply Summable.of_nonneg_of_le _ _ (hmaj (C 1))
    · intro k
      exact mul_nonneg (pow_nonneg hr0 _)
        (Finset.sum_nonneg (fun i _ => le_min (hC0 _) (hC0 _)))
    · intro k
      exact mul_le_mul_of_nonneg_left (hminle k) (pow_nonneg hr0 _)
  set Y : ℝ := ∑' k : ℕ, r ^ k *
    (α * C (k + 1) + 2 * p * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) with hY
  have hYsplit : Y = α * ∑' i : ℕ, r ^ i * C (i + 1) +
      2 * p * ∑' k : ℕ, r ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)) := by
    rw [hY, ← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hsumM.mul_left _)
      (hsumN.mul_left _)]
    apply tsum_congr; intro k; ring
  have hY0 : 0 ≤ Y := by
    rw [hY]
    apply tsum_nonneg; intro k
    apply mul_nonneg (pow_nonneg hr0 _)
    exact add_nonneg (mul_nonneg hα (hC0 _))
      (mul_nonneg (by linarith) (Finset.sum_nonneg (fun i _ => le_min (hC0 _) (hC0 _))))
  -- master tour part
  have hmaster : ∑ S : Finset V, subsetProb q S * tspOpt c S ≤
      σ ^ 2 * ∑' i : ℕ, r ^ i * C (i + 1) := by
    calc ∑ S : Finset V, subsetProb q S * tspOpt c S
        ≤ ∑ S : Finset V, subsetProb q S * cycleCost c (T.filter (· ∈ S)) :=
          Finset.sum_le_sum (fun S _ => mul_le_mul_of_nonneg_left (tspOpt_le c T hT S)
            (subsetProb_nonneg q (fun v => ⟨(hq01 v).1.le, (hq01 v).2⟩) S))
      _ = aPrioriCost c q T := rfl
      _ = ∑' i : ℕ, (1 - σ * p) ^ i * hopC c (σ * p) d T (i + 1) :=
          proposition_10 c q d (σ * p) hσp0 hqI T hT hTd
      _ = σ ^ 2 * ∑' i : ℕ, r ^ i * C (i + 1) := by
          rw [← tsum_mul_left]
          apply tsum_congr; intro i
          rw [hopC_scale]; simp only [hC, hr]; ring
  have hconn := lemma_11_connection c pf d σ p hσ0 hσ1 hp0 hp1 ⟨hI, hnp⟩ T hT hTd
  have hOPT : aPrioriOpt c pf = ∑' i : ℕ, (1 - p) ^ i * C (i + 1) := by
    rw [← hTopt]; exact proposition_10 c pf d p hp0 ⟨hI, hnp⟩ T hT hTd
  -- the sampling cost is at most σ² Y
  have hcost : samplingCost α (linSampling σ) c pf ≤ σ ^ 2 * Y := by
    unfold samplingCost
    have e : ∑ S : Finset V, subsetProb (fun v => linSampling σ (pf v)) S *
        (α * tspOpt c S + 2 * ∑ v, pf v * distToSet c v S) =
        α * ∑ S : Finset V, subsetProb q S * tspOpt c S +
        2 * ∑ S : Finset V, subsetProb q S * ∑ v, pf v * distToSet c v S := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro S _; simp only [hq]; ring
    rw [e, hYsplit]
    have h1 := mul_le_mul_of_nonneg_left hmaster hα
    have h2 : 2 * ∑ S : Finset V, subsetProb q S * ∑ v, pf v * distToSet c v S ≤
        2 * (σ ^ 2 * p * ∑' k : ℕ, r ^ k * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hconn
    nlinarith
  -- scaling
  rcases eq_or_lt_of_le hY0 with hY00 | hYpos
  · rw [← hY00, mul_zero] at hcost
    have hO : 0 ≤ aPrioriOpt c pf := by
      rw [← hTopt]; exact aPrioriCost_nonneg c hc pf hpf T
    have : 0 ≤ μ⁻¹ * aPrioriOpt c pf := mul_nonneg (inv_nonneg.2 hμ.le) hO
    linarith
  · set lam : ℝ := 1 / (σ ^ 2 * Y) with hlam
    have hlam0 : 0 < lam := by positivity
    set C' : ℕ → ℝ := fun k => lam * C k with hC'
    have hfeas : SamplingOPFeasible α σ p C' := by
      refine ⟨fun i _ => mul_nonneg hlam0.le (hC0 i), fun i j _ _ => ?_, ?_⟩
      · simp only [hC']
        have := mul_le_mul_of_nonneg_left (hCt i j) hlam0.le
        linarith
      · have e : (fun k : ℕ => (1 - σ * p) ^ k * (α * C' (k + 1) + 2 * p *
            ∑ i ∈ Finset.Icc 1 k, min (C' i) (C' (k + 1 - i)))) =
            fun k : ℕ => lam * (r ^ k * (α * C (k + 1) + 2 * p *
              ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)))) := by
          funext k
          simp only [hC', ← mul_min_of_nonneg _ _ hlam0.le, ← Finset.mul_sum, hr]
          ring
        rw [e, tsum_mul_left, ← hY, hlam]
        field_simp
        rfl
    have hv := hval C' hfeas
    have hobj : samplingOPObj p C' = lam * aPrioriOpt c pf := by
      unfold samplingOPObj
      rw [hOPT, ← tsum_mul_left]
      apply tsum_congr; intro i; simp only [hC']; ring
    rw [hobj, hlam] at hv
    have hS : σ ^ 2 * Y ≤ μ⁻¹ * aPrioriOpt c pf := by
      have hpos : 0 < σ ^ 2 * Y := by positivity
      rw [one_div, inv_mul_eq_div, le_div_iff₀ hpos] at hv
      rw [← div_eq_inv_mul, le_div_iff₀ hμ]
      linarith
    linarith
