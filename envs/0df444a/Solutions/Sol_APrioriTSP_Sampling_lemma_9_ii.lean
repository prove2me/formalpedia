-- Prove2me | solution 1 for APrioriTSP.Sampling.lemma_9_ii
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:08:49.037995+00:00
-- url     : https://prove2.me/submissions/c2ad9fd1-9275-402d-a446-dfd084d569f9

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Theorems.Thm_APrioriTSP_Sampling_lemma_32
import Theorems.Thm_APrioriTSP_Sampling_lemma_33

open APrioriTSP.Sampling Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace APTSPL9

section general
variable {V : Type} [Fintype V] [DecidableEq V]

/-- probability of a pattern: all of `S` active, none of `U` active. -/
theorem pattern (q : V → ℝ) (S U : Finset V) (hSU : Disjoint S U) :
    ∑ A : Finset V, subsetProb q A * (if S ⊆ A ∧ Disjoint U A then 1 else 0) =
      (∏ v ∈ S, q v) * ∏ v ∈ U, (1 - q v) := by
  set f : V → ℝ := fun v => if v ∈ U then 0 else q v with hf
  set g : V → ℝ := fun v => if v ∈ S then 0 else 1 - q v with hg
  have key : ∀ A : Finset V, subsetProb q A * (if S ⊆ A ∧ Disjoint U A then 1 else 0) =
      (∏ v ∈ A, f v) * ∏ v ∈ univ \ A, g v := by
    intro A
    unfold subsetProb
    by_cases hc : S ⊆ A ∧ Disjoint U A
    · rw [if_pos hc, mul_one]
      congr 1
      · apply Finset.prod_congr rfl; intro v hv
        simp only [hf]; rw [if_neg]; intro hvU
        exact Finset.disjoint_left.1 hc.2 hvU hv
      · apply Finset.prod_congr rfl; intro v hv
        simp only [hg]; rw [if_neg]; intro hvS
        simp at hv; exact hv (hc.1 hvS)
    · rw [if_neg hc, mul_zero]
      rw [not_and_or] at hc
      rcases hc with h1 | h1
      · rw [Finset.not_subset] at h1
        obtain ⟨s, hsS, hsA⟩ := h1
        have : ∏ v ∈ univ \ A, g v = 0 := by
          apply Finset.prod_eq_zero (i := s) (by simp [hsA])
          simp [hg, hsS]
        rw [this, mul_zero]
      · rw [Finset.not_disjoint_iff] at h1
        obtain ⟨u, huU, huA⟩ := h1
        have : ∏ v ∈ A, f v = 0 := by
          apply Finset.prod_eq_zero huA
          simp [hf, huU]
        rw [this, zero_mul]
  rw [Finset.sum_congr rfl (fun A _ => key A)]
  have h2 := (Finset.prod_add f g (univ : Finset V)).symm
  rw [Finset.powerset_univ] at h2
  rw [h2]
  have h3 : ∀ v, f v + g v = (if v ∈ S then q v else 1) * (if v ∈ U then 1 - q v else 1) := by
    intro v
    simp only [hf, hg]
    by_cases hS : v ∈ S
    · have hU : v ∉ U := Finset.disjoint_left.1 hSU hS
      simp [hS, hU]
    · by_cases hU : v ∈ U
      · simp [hS, hU]
      · simp [hS, hU]
  rw [Finset.prod_congr rfl (fun v _ => h3 v), Finset.prod_mul_distrib,
    Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter, Finset.univ_inter]


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


theorem exists_opt_tour_min (c : V → V → ℝ) (q : V → ℝ) (d : V) :
    ∃ T : List V, IsTour T ∧ T.head? = some d ∧
      ∀ T' : List V, IsTour T' → aPrioriCost c q T ≤ aPrioriCost c q T' := by
  have hne : {T : List V | IsTour T}.Nonempty :=
    ⟨(Finset.univ : Finset V).toList, Finset.nodup_toList _, fun v => by simp⟩
  obtain ⟨T0, hT0, hmin⟩ := Set.exists_min_image _ (aPrioriCost c q) tours_finite hne
  have hdT : d ∈ T0 := hT0.2 d
  refine ⟨T0.rotate (T0.idxOf d), ⟨List.nodup_rotate.2 hT0.1, fun v => List.mem_rotate.2 (hT0.2 v)⟩,
    ?_, fun T' hT' => by rw [aPrioriCost_rotate]; exact hmin T' hT'⟩
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

/-- probability that the set of nonempty fibers within `A` covers `A`, while `X` is avoided -/
theorem fiber_claim {V' : Type} [Fintype V'] [DecidableEq V'] (π : V' → V) (q : V' → ℝ) :
    ∀ (A : Finset V) (X : Finset V'), (∀ x ∈ X, π x ∉ A) →
      ∑ A' : Finset V', subsetProb q A' *
        ((∏ v ∈ A, (if ∃ x ∈ A', π x = v then (1 : ℝ) else 0)) *
          (if Disjoint X A' then 1 else 0)) =
      (∏ v ∈ A, (1 - ∏ x ∈ univ.filter (fun x => π x = v), (1 - q x))) *
        ∏ x ∈ X, (1 - q x) := by
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro X _
    simp only [Finset.prod_empty, one_mul]
    have := pattern q ∅ X (Finset.disjoint_empty_left _)
    simp only [Finset.empty_subset, true_and, Finset.prod_empty, one_mul] at this
    exact this
  | insert a A0 ha IH =>
    intro X hX
    set F : V' → Finset V' := fun _ => univ.filter (fun x => π x = a) with hF
    have hXF : ∀ x ∈ X ∪ univ.filter (fun x => π x = a), π x ∉ A0 := by
      intro x hx
      rcases Finset.mem_union.1 hx with h | h
      · exact fun h' => hX x h (Finset.mem_insert_of_mem h')
      · simp at h; rw [h]; exact ha
    have hX0 : ∀ x ∈ X, π x ∉ A0 := fun x hx h => hX x hx (Finset.mem_insert_of_mem h)
    have key : ∀ A' : Finset V', (∏ v ∈ insert a A0, (if ∃ x ∈ A', π x = v then (1 : ℝ) else 0)) *
        (if Disjoint X A' then 1 else 0) =
        (∏ v ∈ A0, (if ∃ x ∈ A', π x = v then (1 : ℝ) else 0)) * (if Disjoint X A' then 1 else 0) -
        (∏ v ∈ A0, (if ∃ x ∈ A', π x = v then (1 : ℝ) else 0)) *
          (if Disjoint (X ∪ univ.filter (fun x => π x = a)) A' then 1 else 0) := by
      intro A'
      rw [Finset.prod_insert ha]
      have e : (if Disjoint (X ∪ univ.filter (fun x => π x = a)) A' then (1 : ℝ) else 0) =
          (if Disjoint X A' then 1 else 0) * (if ∃ x ∈ A', π x = a then 0 else 1) := by
        by_cases h1 : Disjoint X A'
        · by_cases h2 : ∃ x ∈ A', π x = a
          · rw [if_pos h1, if_pos h2, if_neg]; · ring
            intro hd
            obtain ⟨x, hx, hxa⟩ := h2
            exact Finset.disjoint_left.1 hd (Finset.mem_union_right _ (by simp [hxa])) hx
          · rw [if_pos h1, if_neg h2, if_pos]; · ring
            rw [Finset.disjoint_union_left]
            refine ⟨h1, Finset.disjoint_left.2 ?_⟩
            intro x hx hxA
            simp at hx
            exact h2 ⟨x, hxA, hx⟩
        · rw [if_neg h1, if_neg]; · ring
          intro hd; exact h1 (Finset.disjoint_union_left.1 hd).1
      rw [e]
      split_ifs <;> ring
    simp_rw [key, mul_sub, Finset.sum_sub_distrib]
    rw [IH X hX0, IH _ hXF]
    have hdisj : Disjoint X (univ.filter (fun x => π x = a)) := by
      rw [Finset.disjoint_left]; intro x hx hx'
      simp at hx'; exact hX x hx (by rw [hx']; exact Finset.mem_insert_self _ _)
    rw [Finset.prod_union hdisj, Finset.prod_insert ha]
    ring

/-- pushforward of a product Bernoulli measure along `π` -/
theorem pushforward_prob {V' : Type} [Fintype V'] [DecidableEq V'] (π : V' → V) (q : V' → ℝ)
    (A : Finset V) :
    ∑ A' : Finset V', subsetProb q A' * (if A'.image π = A then (1 : ℝ) else 0) =
      subsetProb (fun v => 1 - ∏ x ∈ univ.filter (fun x => π x = v), (1 - q x)) A := by
  have hX : ∀ x ∈ univ.filter (fun x => π x ∉ A), π x ∉ A := by intro x hx; simpa using hx
  have h := fiber_claim π q A (univ.filter (fun x => π x ∉ A)) hX
  have e : ∀ A' : Finset V', (if A'.image π = A then (1 : ℝ) else 0) =
      (∏ v ∈ A, (if ∃ x ∈ A', π x = v then (1 : ℝ) else 0)) *
        (if Disjoint (univ.filter (fun x => π x ∉ A)) A' then 1 else 0) := by
    intro A'
    rw [Finset.prod_boole]
    by_cases hc : A'.image π = A
    · rw [if_pos hc, if_pos, if_pos]; · ring
      · rw [Finset.disjoint_left]; intro x hx hxA
        simp at hx; apply hx; rw [← hc]; exact Finset.mem_image_of_mem _ hxA
      · intro v hv; rw [← hc] at hv; simpa using hv
    · rw [if_neg hc]
      by_cases h1 : ∀ v ∈ A, ∃ x ∈ A', π x = v
      · rw [if_pos h1, if_neg]; · ring
        intro hd
        apply hc
        ext v
        constructor
        · intro hv
          simp only [Finset.mem_image] at hv
          obtain ⟨x, hx, rfl⟩ := hv
          by_contra hn
          exact Finset.disjoint_left.1 hd (by simpa using hn) hx
        · intro hv
          obtain ⟨x, hx, hxv⟩ := h1 v hv
          exact Finset.mem_image.2 ⟨x, hx, hxv⟩
      · rw [if_neg h1]; ring
  simp_rw [e]
  rw [h]
  unfold subsetProb
  congr 1
  rw [← Finset.prod_fiberwise_of_maps_to (g := π) (t := univ \ A)]
  · apply Finset.prod_congr rfl
    intro v hv
    simp at hv
    simp only [sub_sub_cancel]
    apply Finset.prod_congr
    · ext x; simp; intro h; rw [h]; exact hv
    · intro _ _; rfl
  · intro x hx; simpa using hx

/-- expectation along the pushforward -/
theorem pushforward_expect {V' : Type} [Fintype V'] [DecidableEq V'] (π : V' → V) (q : V' → ℝ)
    (F : Finset V → ℝ) :
    ∑ A' : Finset V', subsetProb q A' * F (A'.image π) =
      ∑ A : Finset V, subsetProb (fun v => 1 - ∏ x ∈ univ.filter (fun x => π x = v), (1 - q x)) A *
        F A := by
  simp_rw [← pushforward_prob π q]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro A' _
  rw [Finset.sum_eq_single (A'.image π)]
  · rw [if_pos rfl]; ring
  · intro A _ hA; rw [if_neg (Ne.symm hA)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

theorem distToSet_nonneg (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (v : V) (S : Finset V) :
    0 ≤ distToSet c v S := by
  unfold distToSet
  apply Real.sInf_nonneg
  rintro _ ⟨u, _, rfl⟩; exact hc _ _

theorem tspOpt_nonneg (c : V → V → ℝ) (hc : ∀ u v, 0 ≤ c u v) (S : Finset V) :
    0 ≤ tspOpt c S := by
  unfold tspOpt
  apply Real.sInf_nonneg
  rintro _ ⟨l, _, rfl⟩; exact cycleCost_nonneg c hc l

theorem cycleCost_rotate (c : V → V → ℝ) (l : List V) (m : ℕ) :
    cycleCost c (l.rotate m) = cycleCost c l := by
  induction m with
  | zero => rw [List.rotate_zero]
  | succ k ih => rw [← List.rotate_rotate, cycleCost_rotate_one, ih]

theorem cycleCost_erase_le {c : V → V → ℝ} {pf : V → ℝ} {d : V} (hI : IsDepotInstance c pf d)
    (s t : List V) (a : V) : cycleCost c (s ++ t) ≤ cycleCost c (s ++ a :: t) := by
  have hc := c_nonneg hI
  rw [← cycleCost_rotate c (s ++ t) s.length, ← cycleCost_rotate c (s ++ a :: t) s.length,
    List.rotate_append_length_eq, List.rotate_append_length_eq]
  simp only [List.cons_append]
  generalize t ++ s = L
  rcases L with _ | ⟨u, t'⟩
  · have : cycleCost c ([] : List V) = 0 := rfl
    rw [this]; exact cycleCost_nonneg c hc _
  · rw [← cycleCost_rotate_one c (a :: u :: t'), List.rotate_cons_succ, List.rotate_zero]
    rw [show u :: t' ++ [a] = u :: (t' ++ [a]) by simp, cycleCost_cons, cycleCost_cons]
    have h1 := pathCost_append_single c u (t' ++ [a]) u
    have h2 := pathCost_append_single c a t' u
    have h3 := pathCost_append_single c u t' u
    have hl : (u :: (t' ++ [a])).getLast (by simp) = a := by simp
    rw [hl] at h1
    simp only [List.cons_append, List.append_assoc] at h1 h2 h3 ⊢
    rw [h1, h2, h3]
    have := hI.c_triangle ((u :: t').getLast (by simp)) a u
    linarith

theorem shortcut {c : V → V → ℝ} {pf : V → ℝ} {d : V} (hI : IsDepotInstance c pf d) :
    ∀ l : List V, tspOpt c l.toFinset ≤ cycleCost c l := by
  have hc := c_nonneg hI
  intro l
  obtain ⟨m, hlen⟩ : ∃ m, l.length = m := ⟨_, rfl⟩
  induction m using Nat.strong_induction_on generalizing l with
  | _ m ih =>
    by_cases hnd : l.Nodup
    · unfold tspOpt
      apply csInf_le
      · exact ⟨0, by rintro _ ⟨l', _, rfl⟩; exact cycleCost_nonneg c hc l'⟩
      · exact ⟨l, ⟨hnd, rfl⟩, rfl⟩
    · rw [List.nodup_iff_count_le_one] at hnd
      push Not at hnd
      obtain ⟨a, ha⟩ := hnd
      have hal : a ∈ l := List.count_pos_iff.1 (by omega)
      obtain ⟨l1, l2, _, hl, he⟩ := List.exists_erase_eq hal
      have hae : a ∈ l.erase a := by
        apply List.count_pos_iff.1
        rw [List.count_erase_self]; omega
      have hfin : (l.erase a).toFinset = l.toFinset := by
        ext x
        simp only [List.mem_toFinset]
        by_cases hx : x = a
        · subst hx; exact ⟨fun _ => hal, fun _ => hae⟩
        · exact List.mem_erase_of_ne hx
      have hlt : (l.erase a).length < m := by
        have := List.length_pos_of_mem hal
        rw [List.length_erase_of_mem hal]; omega
      have := ih _ hlt (l.erase a) rfl
      rw [hfin] at this
      calc tspOpt c l.toFinset ≤ cycleCost c (l.erase a) := this
        _ = cycleCost c (l1 ++ l2) := by rw [he]
        _ ≤ cycleCost c (l1 ++ a :: l2) := cycleCost_erase_le hI l1 l2 a
        _ = cycleCost c l := by rw [← hl]

theorem cycleCost_map {V' : Type} (c : V → V → ℝ) (π : V' → V) (l : List V') :
    cycleCost (fun x y => c (π x) (π y)) l = cycleCost c (l.map π) := by
  unfold cycleCost
  rw [← List.map_rotate, List.zip_map, List.map_map]
  rfl

end general

section copies
variable {V : Type} [Fintype V] [DecidableEq V] (d : V) (k : {v : V // v ≠ d} → ℕ)

/-- the instance with `k v` copies of each customer `v` -/
abbrev Cp := Option (Σ v : {v : V // v ≠ d}, Fin (k v))

def proj : Cp d k → V
  | none => d
  | some x => x.1.1

theorem proj_some (x : Σ v : {v : V // v ≠ d}, Fin (k v)) : proj d k (some x) = x.1.1 := rfl

theorem proj_eq_d (x : Cp d k) : proj d k x = d ↔ x = none := by
  rcases x with _ | ⟨⟨v, hv⟩, i⟩
  · simp [proj]
  · simp [proj, hv]

theorem fiber_d : (univ : Finset (Cp d k)).filter (fun x => proj d k x = d) = {none} := by
  ext x; simp [proj_eq_d]

theorem fiber_v (v : V) (hv : v ≠ d) :
    (univ : Finset (Cp d k)).filter (fun x => proj d k x = v) =
      (univ : Finset (Fin (k ⟨v, hv⟩))).map
        ⟨fun i => some ⟨⟨v, hv⟩, i⟩, fun i j h => by simpa using h⟩ := by
  ext x
  rcases x with _ | ⟨⟨u, hu⟩, i⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, reduceCtorEq, exists_false, iff_false]
    show ¬ d = v
    exact fun h => hv h.symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, proj_some, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro h; subst h; exact ⟨i, rfl⟩
    · rintro ⟨j, hj⟩
      have := congrArg (fun y : Cp d k => proj d k y) hj
      simp only [Function.Embedding.coeFn_mk, proj_some] at this
      exact this.symm

theorem fiber_prod_v (g : Cp d k → ℝ) (v : V) (hv : v ≠ d) (a : ℝ)
    (hg : ∀ x, proj d k x = v → g x = a) :
    ∏ x ∈ (univ : Finset (Cp d k)).filter (fun x => proj d k x = v), g x = a ^ (k ⟨v, hv⟩) := by
  rw [Finset.prod_congr rfl (fun x hx => hg x (by simpa using hx)), Finset.prod_const,
    fiber_v d k v hv, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem fiber_prod_d (g : Cp d k → ℝ) :
    ∏ x ∈ (univ : Finset (Cp d k)).filter (fun x => proj d k x = d), g x = g none := by
  rw [fiber_d]; simp

/-- the copies of a vertex, as a list -/
def copiesL (v : V) : List (Cp d k) :=
  if h : v = d then [none] else (List.finRange (k ⟨v, h⟩)).map (fun i => some ⟨⟨v, h⟩, i⟩)

theorem proj_of_mem_copiesL (v : V) (x : Cp d k) (hx : x ∈ copiesL d k v) : proj d k x = v := by
  unfold copiesL at hx
  split_ifs at hx with h
  · rw [List.mem_singleton] at hx; subst hx; exact h.symm
  · rw [List.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx; rfl

theorem mem_copiesL (x : Cp d k) : x ∈ copiesL d k (proj d k x) := by
  rcases x with _ | ⟨⟨u, hu⟩, i⟩
  · simp [copiesL, proj]
  · rw [proj_some]
    unfold copiesL
    rw [dif_neg hu]
    simp

theorem nodup_copiesL (v : V) : (copiesL d k v).Nodup := by
  unfold copiesL
  split_ifs with h
  · simp
  · apply List.Nodup.map _ (List.nodup_finRange _)
    intro i j hij; simpa using hij

theorem expand_tour (T : List V) (hT : IsTour T) : IsTour (T.flatMap (copiesL d k)) := by
  constructor
  · rw [List.nodup_flatMap]
    refine ⟨fun v _ => nodup_copiesL d k v, ?_⟩
    apply hT.1.imp
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro x hxa hxb
    exact hab ((proj_of_mem_copiesL d k a x hxa).symm.trans (proj_of_mem_copiesL d k b x hxb))
  · intro x
    rw [List.mem_flatMap]
    exact ⟨proj d k x, hT.2 _, mem_copiesL d k x⟩

theorem rep_pathCost (c : V → V → ℝ) (hcv : ∀ v, c v v = 0) (u : V) :
    ∀ (j : ℕ) (y : V) (L : List V),
      pathCost c (y :: (List.replicate (j + 1) u ++ L)) = pathCost c (y :: u :: L) := by
  intro j
  induction j with
  | zero => intro y L; rfl
  | succ j ih =>
    intro y L
    rw [List.replicate_succ, List.cons_append, pathCost_cons_cons, ih u L, pathCost_cons_cons,
      hcv, zero_add, pathCost_cons_cons]

theorem flat_pathCost (c : V → V → ℝ) (hcv : ∀ v, c v v = 0) (m : V → ℕ) (z : V) :
    ∀ (R : List V) (y : V),
      pathCost c (y :: (R.flatMap (fun v => List.replicate (m v) v) ++ [z])) =
        pathCost c (y :: (R.filter (fun v => 0 < m v) ++ [z])) := by
  intro R
  induction R with
  | nil => intro y; rfl
  | cons u R ih =>
    intro y
    rw [List.flatMap_cons, List.filter_cons]
    rcases Nat.eq_zero_or_pos (m u) with hm | hm
    · rw [hm, if_neg (by simp)]
      simp only [List.replicate_zero, List.nil_append]
      exact ih y
    · rw [if_pos (by simpa using hm)]
      obtain ⟨j, hj⟩ : ∃ j, m u = j + 1 := ⟨m u - 1, by omega⟩
      rw [hj, List.append_assoc, rep_pathCost c hcv u j y, pathCost_cons_cons, ih u,
        List.cons_append, pathCost_cons_cons]

theorem D1 {pf : V → ℝ} (c : V → V → ℝ) (hI : IsDepotInstance c pf d) (R : List V)
    (A' : Finset (Cp d k)) (hA : none ∈ A') :
    cycleCost (fun x y => c (proj d k x) (proj d k y))
        (((d :: R).flatMap (copiesL d k)).filter (· ∈ A')) =
      cycleCost c ((d :: R).filter (· ∈ A'.image (proj d k))) := by
  have hcv : ∀ v, c v v = 0 := hI.c_self
  rw [cycleCost_map, List.filter_flatMap, List.map_flatMap]
  set m : V → ℕ := fun v => ((copiesL d k v).filter (· ∈ A')).length with hm
  have hrep : ∀ v, ((copiesL d k v).filter (· ∈ A')).map (proj d k) = List.replicate (m v) v := by
    intro v
    rw [List.eq_replicate_iff]
    refine ⟨by simp [hm], ?_⟩
    intro b hb
    rw [List.mem_map] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    exact proj_of_mem_copiesL d k v x (List.mem_of_mem_filter hx)
  simp_rw [hrep]
  have hmd : m d = 1 := by
    simp only [hm, copiesL, dif_pos rfl]
    simp [hA]
  rw [List.flatMap_cons, hmd, List.replicate_one, List.singleton_append, cycleCost_cons,
    List.cons_append, flat_pathCost c hcv m d R d]
  have hdi : d ∈ A'.image (proj d k) := Finset.mem_image.2 ⟨none, hA, rfl⟩
  rw [List.filter_cons, if_pos (by simpa using hdi), cycleCost_cons, List.cons_append]
  congr 3
  apply List.filter_congr
  intro v _
  simp only [decide_eq_decide, hm, Finset.mem_image]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos h
    rw [List.mem_filter] at hx
    exact ⟨x, by simpa using hx.2, proj_of_mem_copiesL d k v x hx.1⟩
  · rintro ⟨x, hx, rfl⟩
    apply List.length_pos_of_mem (a := x)
    rw [List.mem_filter]
    exact ⟨mem_copiesL d k x, by simpa using hx⟩

theorem D2 {pf : V → ℝ} (c : V → V → ℝ) (hI : IsDepotInstance c pf d) (A' : Finset (Cp d k)) :
    tspOpt c (A'.image (proj d k)) ≤ tspOpt (fun x y => c (proj d k x) (proj d k y)) A' := by
  unfold tspOpt
  apply le_csInf
  · exact ⟨_, A'.toList, ⟨Finset.nodup_toList _, Finset.toList_toFinset _⟩, rfl⟩
  · rintro _ ⟨l', ⟨_, hl'⟩, rfl⟩
    rw [cycleCost_map]
    have := shortcut hI (l'.map (proj d k))
    have he : (l'.map (proj d k)).toFinset = A'.image (proj d k) := by
      rw [← hl']; ext v; simp
    rw [he] at this
    exact this

theorem D3 (c : V → V → ℝ) (x : Cp d k) (A' : Finset (Cp d k)) :
    distToSet (fun x y => c (proj d k x) (proj d k y)) x A' =
      distToSet c (proj d k x) (A'.image (proj d k)) := by
  unfold distToSet
  congr 1
  ext r
  simp

end copies

section twopoint

theorem two_point (α σ : ℝ) (hα : 0 ≤ α) (hσ0 : 0 < σ) (hσ1 : σ < 1) (e : ℝ) (he0 : 0 < e)
    (he1 : e ≤ 1) (ρ : ℝ)
    (H : ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
      IsNormalized c p d e → samplingCost α (linSampling σ) c p ≤ ρ * aPrioriOpt c p) :
    0 ≤ ρ := by
  by_contra hneg
  push Not at hneg
  set c2 : Bool → Bool → ℝ := fun u v => if u = v then 0 else 1 with hc2
  set p2 : Bool → ℝ := fun v => if v = true then 1 else e with hp2
  have hI : IsDepotInstance c2 p2 true := by
    refine ⟨fun v => by simp [hc2], fun u v => ?_, fun u v w => ?_, fun v => ?_, fun v => ?_, ?_⟩
    · simp only [hc2]; by_cases h : u = v
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    · simp only [hc2]; cases u <;> cases v <;> cases w <;> norm_num
    · simp only [hp2]; split_ifs <;> linarith
    · simp only [hp2]; split_ifs <;> linarith
    · simp [hp2]
  have hnorm : IsNormalized c2 p2 true e := ⟨hI, fun v hv => by simp [hp2, hv]⟩
  have h1 := H Bool c2 p2 true hnorm
  have hc := c_nonneg hI
  -- the sampling cost is nonnegative
  have hS : 0 ≤ samplingCost α (linSampling σ) c2 p2 := by
    unfold samplingCost
    apply Finset.sum_nonneg; intro S _
    apply mul_nonneg
    · apply subsetProb_nonneg
      intro v
      simp only [linSampling, hp2]
      split_ifs <;> constructor <;> nlinarith
    · apply add_nonneg (mul_nonneg hα (tspOpt_nonneg c2 hc S))
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg; intro v _
      apply mul_nonneg _ (distToSet_nonneg c2 hc v S)
      simp only [hp2]; split_ifs <;> linarith
  -- the optimum is at least 2e
  have hO : 2 * e ≤ aPrioriOpt c2 p2 := by
    unfold aPrioriOpt
    apply le_csInf
    · exact ⟨_, (Finset.univ : Finset Bool).toList, ⟨Finset.nodup_toList _, fun v => by simp⟩, rfl⟩
    · rintro _ ⟨T, hT, rfl⟩
      have hlen : T.length = 2 := by
        rw [← List.toFinset_card_of_nodup hT.1]
        have : T.toFinset = Finset.univ := by ext v; simp [hT.2 v]
        rw [this]; rfl
      obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
      have hab : a ≠ b := by
        have := hT.1; simp at this; exact this
      unfold aPrioriCost
      have hterm := Finset.single_le_sum (s := (Finset.univ : Finset (Finset Bool)))
        (f := fun A => subsetProb p2 A * cycleCost c2 ([a, b].filter (· ∈ A)))
        (fun A _ => mul_nonneg (subsetProb_nonneg p2
          (fun v => ⟨(hI.p_pos v).le, hI.p_le_one v⟩) A) (cycleCost_nonneg c2 hc _))
        (Finset.mem_univ Finset.univ)
      refine le_trans (le_of_eq ?_) hterm
      simp only [Finset.mem_univ, decide_true, List.filter_cons_of_pos, List.filter_nil]
      unfold subsetProb cycleCost
      simp [hc2, hp2, hab, Ne.symm hab]
      ring
  have : ρ * aPrioriOpt c2 p2 < 0 := by
    have : 0 < aPrioriOpt c2 p2 := by linarith
    nlinarith
  linarith

end twopoint

section main
open Filter Topology

theorem main_delta (α σ : ℝ) (hα : 0 ≤ α) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i ∧ ε i ≤ 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (H : ∀ (i : ℕ) (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
        IsNormalized c p d (ε i) → samplingCost α (linSampling σ) c p ≤ ρ * aPrioriOpt c p)
    (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V)
    (hI : IsDepotInstance c p d) (δ : ℝ) (hδ : 0 < δ) :
    samplingCost α (powerSampling σ) c p ≤ (1 + δ) * (ρ * aPrioriOpt c p) := by
  have hc := c_nonneg hI
  set N := Fintype.card V with hNdef
  have hN : 1 ≤ N := Fintype.card_pos_iff.2 ⟨d⟩
  set lam : ℝ := Real.log (1 + δ) / N with hlamdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam : 0 < lam := div_pos (Real.log_pos (by linarith)) hNpos
  have hlamN : (1 + lam) ^ N ≤ 1 + δ := by
    calc (1 + lam) ^ N ≤ (Real.exp lam) ^ N :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp lam]) N
      _ = Real.exp (N * lam) := by rw [← Real.exp_nat_mul]
      _ = 1 + δ := by
          rw [hlamdef, mul_div_cancel₀ _ hNpos.ne', Real.exp_log (by linarith)]
  -- Lemma 32 for each customer
  have h32 : ∀ v : {v : V // v ≠ d}, ∃ εp : ℝ, 0 < εp ∧ εp < 1 ∧ ∀ e : ℝ, 0 < e → e ≤ εp →
      ∃ k : ℕ, (1 - (1 - e) ^ k ≤ p v ∧ p v ≤ e * k) ∧
        (1 - p v) ^ σ ≤ (1 - σ * e) ^ k ∧
        1 - (1 - p v) ^ σ ≤ (1 + lam) * (1 - (1 - σ * e) ^ k) ∧
        (p v < 1 → (1 - e) ^ k ≤ (1 + lam) * (1 - p v)) ∧
        (p v = 1 → (1 - e) ^ k ≤ lam) :=
    fun v => lemma_32 σ lam (p v) hσ0 hσ1 hlam (hI.p_pos v) (hI.p_le_one v)
  choose εp hεp0 hεp1 hεpk using h32
  obtain ⟨η, hη0, hη1, hηle⟩ : ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ v, η ≤ εp v := by
    by_cases hne : Nonempty {v : V // v ≠ d}
    · refine ⟨Finset.univ.inf' Finset.univ_nonempty εp, ?_, ?_, fun v => Finset.inf'_le _ (Finset.mem_univ v)⟩
      · rw [Finset.lt_inf'_iff]; intro v _; exact hεp0 v
      · obtain ⟨v0⟩ := hne
        exact lt_of_le_of_lt (Finset.inf'_le _ (Finset.mem_univ v0)) (hεp1 v0)
    · exact ⟨1 / 2, by norm_num, by norm_num, fun v => (hne ⟨v⟩).elim⟩
  obtain ⟨i, hi⟩ : ∃ i, ε i < η := (hlim.eventually (gt_mem_nhds hη0)).exists
  set e := ε i with hedef
  have he0 : 0 < e := (hε i).1
  have he1 : e < 1 := lt_trans hi hη1
  have hk : ∀ v : {v : V // v ≠ d}, ∃ k : ℕ, (1 - (1 - e) ^ k ≤ p v ∧ p v ≤ e * k) ∧
        (1 - p v) ^ σ ≤ (1 - σ * e) ^ k ∧
        1 - (1 - p v) ^ σ ≤ (1 + lam) * (1 - (1 - σ * e) ^ k) ∧
        (p v < 1 → (1 - e) ^ k ≤ (1 + lam) * (1 - p v)) ∧
        (p v = 1 → (1 - e) ^ k ≤ lam) :=
    fun v => hεpk v e he0 (le_trans hi.le (hηle v))
  choose k hk using hk
  have hkpos : ∀ v, 1 ≤ k v := by
    intro v
    have h1 := (hk v).1.2
    have h2 := hI.p_pos v
    by_contra hcon
    have : k v = 0 := by omega
    rw [this] at h1; simp at h1; linarith
  -- the copy instance
  set c' : Cp d k → Cp d k → ℝ := fun x y => c (proj d k x) (proj d k y) with hc'
  set p' : Cp d k → ℝ := fun x => if x = none then 1 else e with hp'
  have hI' : IsDepotInstance c' p' none := by
    refine ⟨fun x => hI.c_self _, fun x y => hI.c_symm _ _, fun x y z => hI.c_triangle _ _ _,
      fun x => ?_, fun x => ?_, by simp [hp']⟩
    · simp only [hp']; split_ifs <;> linarith
    · simp only [hp']; split_ifs <;> linarith
  have hnorm' : IsNormalized c' p' none e := ⟨hI', fun x hx => by simp [hp', hx]⟩
  have hH := H i (Cp d k) c' p' none hnorm'
  have hOPT : aPrioriOpt c' p' ≤ aPrioriOpt c p := by
    obtain ⟨T, hT, hTd, hTmin⟩ := exists_opt_tour_min c p d
    obtain ⟨R, rfl⟩ : ∃ R, T = d :: R := by
      cases T with
      | nil => simp at hTd
      | cons x R => simp at hTd; exact ⟨R, by rw [hTd]⟩
    set T' := (d :: R).flatMap (copiesL d k) with hT'def
    have hT' : IsTour T' := expand_tour d k (d :: R) hT
    have hc'0 : ∀ x y, 0 ≤ c' x y := fun x y => hc _ _
    have e1 : aPrioriOpt c' p' ≤ aPrioriCost c' p' T' := by
      unfold aPrioriOpt
      have hq01 : ∀ x, 0 ≤ p' x ∧ p' x ≤ 1 := fun x => ⟨(hI'.p_pos x).le, hI'.p_le_one x⟩
      have hbdd : BddBelow (aPrioriCost c' p' '' {T | IsTour T}) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨T0, _, rfl⟩
        exact aPrioriCost_nonneg c' hc'0 p' hq01 T0
      exact csInf_le hbdd ⟨T', hT', rfl⟩
    set pbar : V → ℝ := fun v =>
      1 - ∏ x ∈ (univ : Finset (Cp d k)).filter (fun x => proj d k x = v), (1 - p' x) with hpbar
    have e2 : aPrioriCost c' p' T' = aPrioriCost c pbar (d :: R) := by
      unfold aPrioriCost
      have : ∀ A' : Finset (Cp d k), subsetProb p' A' * cycleCost c' (T'.filter (· ∈ A')) =
          subsetProb p' A' * cycleCost c ((d :: R).filter (· ∈ A'.image (proj d k))) := by
        intro A'
        by_cases hA : none ∈ A'
        · rw [hT'def, D1 d k c hI R A' hA]
        · have hP : subsetProb p' A' = 0 := by
            unfold subsetProb
            have : ∏ x ∈ univ \ A', (1 - p' x) = 0 :=
              Finset.prod_eq_zero (i := none) (by simp [hA]) (by simp [hp'])
            rw [this, mul_zero]
          rw [hP, zero_mul, zero_mul]
      rw [Finset.sum_congr rfl (fun A' _ => this A')]
      exact pushforward_expect (proj d k) p' (fun U => cycleCost c ((d :: R).filter (· ∈ U)))
    have hpbar_d : pbar d = 1 := by
      simp only [hpbar]; rw [fiber_prod_d]; simp [hp']
    have hpbar_v : ∀ v (hv : v ≠ d), pbar v = 1 - (1 - e) ^ (k ⟨v, hv⟩) := by
      intro v hv
      simp only [hpbar]
      rw [fiber_prod_v d k _ v hv (1 - e)]
      intro x hx
      have : x ≠ none := by
        intro h; rw [h] at hx; exact hv (by simpa [proj] using hx.symm)
      simp [hp', this]
    have hpb : ∀ v, 0 < pbar v ∧ pbar v ≤ 1 := by
      intro v
      by_cases hv : v = d
      · rw [hv, hpbar_d]; norm_num
      · rw [hpbar_v v hv]
        have h0 : 0 ≤ 1 - e := by linarith
        have hkv : k ⟨v, hv⟩ ≠ 0 := by have := hkpos ⟨v, hv⟩; omega
        have h1 : (1 - e) ^ (k ⟨v, hv⟩) < 1 := pow_lt_one₀ h0 (by linarith) hkv
        have h2 : 0 ≤ (1 - e) ^ (k ⟨v, hv⟩) := pow_nonneg h0 _
        constructor <;> linarith
    have hle : ∀ v, pbar v ≤ p v := by
      intro v
      by_cases hv : v = d
      · rw [hv, hpbar_d, hI.p_depot]
      · rw [hpbar_v v hv]; exact (hk ⟨v, hv⟩).1.1
    have h33 := lemma_33 c p pbar d hI hpb hle hpbar_d (d :: R) hT hTmin
    calc aPrioriOpt c' p' ≤ aPrioriCost c' p' T' := e1
      _ = aPrioriCost c pbar (d :: R) := e2
      _ ≤ aPrioriCost c p (d :: R) := h33.2.1
      _ = aPrioriOpt c p := h33.2.2
  have hS : samplingCost α (powerSampling σ) c p ≤
      (1 + δ) * samplingCost α (linSampling σ) c' p' := by
    have hc'0 : ∀ x y, 0 ≤ c' x y := fun x y => hc _ _
    set q' : Cp d k → ℝ := fun x => linSampling σ (p' x) with hq'
    have hq'none : q' none = 1 := by simp [hq', hp', linSampling]
    have hq'some : ∀ x : Cp d k, x ≠ none → q' x = σ * e := by
      intro x hx
      simp only [hq', hp', if_neg hx, linSampling]
      rw [if_neg (by linarith)]
    have hq'01 : ∀ x, 0 ≤ q' x ∧ q' x ≤ 1 := by
      intro x
      by_cases hx : x = none
      · rw [hx, hq'none]; norm_num
      · rw [hq'some x hx]; constructor <;> nlinarith
    set qbar : V → ℝ := fun v =>
      1 - ∏ x ∈ (univ : Finset (Cp d k)).filter (fun x => proj d k x = v), (1 - q' x) with hqbar
    have hqbar_d : qbar d = 1 := by
      simp only [hqbar]; rw [fiber_prod_d, hq'none]; ring
    have hqbar_v : ∀ v (hv : v ≠ d), qbar v = 1 - (1 - σ * e) ^ (k ⟨v, hv⟩) := by
      intro v hv
      simp only [hqbar]
      rw [fiber_prod_v d k _ v hv (1 - σ * e)]
      intro x hx
      have : x ≠ none := by
        intro h; rw [h] at hx; exact hv (by simpa [proj] using hx.symm)
      rw [hq'some x this]
    have hqbar01 : ∀ v, 0 ≤ qbar v ∧ qbar v ≤ 1 := by
      intro v
      by_cases hv : v = d
      · rw [hv, hqbar_d]; norm_num
      · rw [hqbar_v v hv]
        have h0 : 0 ≤ 1 - σ * e := by nlinarith
        have h1 : (1 - σ * e) ^ (k ⟨v, hv⟩) ≤ 1 := pow_le_one₀ h0 (by nlinarith)
        have h2 : 0 ≤ (1 - σ * e) ^ (k ⟨v, hv⟩) := pow_nonneg h0 _
        constructor <;> linarith
    -- the comparison function
    set Hf : Finset V → ℝ := fun U => α * tspOpt c U + 2 * (distToSet c d U +
      ∑ v : {v : V // v ≠ d}, (k v : ℝ) * e * distToSet c v U) with hHf
    have hHf0 : ∀ U, 0 ≤ Hf U := by
      intro U
      apply add_nonneg (mul_nonneg hα (tspOpt_nonneg c hc U))
      apply mul_nonneg (by norm_num)
      apply add_nonneg (distToSet_nonneg c hc d U)
      apply Finset.sum_nonneg; intro v _
      exact mul_nonneg (mul_nonneg (by positivity) he0.le) (distToSet_nonneg c hc _ U)
    -- lower bound for the copy instance
    have hlow : ∑ U : Finset V, subsetProb qbar U * Hf U ≤
        samplingCost α (linSampling σ) c' p' := by
      have := pushforward_expect (proj d k) q' Hf
      rw [← this]
      unfold samplingCost
      apply Finset.sum_le_sum; intro S' _
      apply mul_le_mul_of_nonneg_left _ (subsetProb_nonneg q' hq'01 S')
      simp only [hHf]
      have hts := D2 d k c hI S'
      have hsum : ∑ x : Cp d k, p' x * distToSet c' x S' =
          distToSet c d (S'.image (proj d k)) + ∑ v : {v : V // v ≠ d},
            (k v : ℝ) * e * distToSet c v (S'.image (proj d k)) := by
        rw [Fintype.sum_option, Fintype.sum_sigma]
        congr 1
        · simp only [hp', if_pos rfl, one_mul]
          rw [hc', D3 d k c none S']; rfl
        · apply Finset.sum_congr rfl; intro v _
          have : ∀ j : Fin (k v), p' (some ⟨v, j⟩) * distToSet c' (some ⟨v, j⟩) S' =
              e * distToSet c v (S'.image (proj d k)) := by
            intro j
            simp only [hp', reduceCtorEq, if_false]
            rw [hc', D3 d k c (some ⟨v, j⟩) S']; rfl
          rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          ring
      rw [hsum]
      have := mul_le_mul_of_nonneg_left hts hα
      linarith
    -- upper bound for the original instance
    have hup : samplingCost α (powerSampling σ) c p ≤
        (1 + δ) * ∑ U : Finset V, subsetProb qbar U * Hf U := by
      unfold samplingCost
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro U _
      set f : V → ℝ := fun v => powerSampling σ (p v) with hf
      have hf1 : f d = 1 := by
        simp only [hf, powerSampling, hI.p_depot, sub_self]
        rw [Real.zero_rpow hσ0.ne']; ring
      have hf01 : ∀ v, 0 ≤ f v ∧ 0 ≤ 1 - f v := by
        intro v
        simp only [hf, powerSampling]
        have h0 : 0 ≤ 1 - p v := by linarith [hI.p_le_one v]
        have h1 : (1 - p v) ^ σ ≤ 1 :=
          Real.rpow_le_one h0 (by linarith [hI.p_pos v]) hσ0.le
        have h2 : 0 ≤ (1 - p v) ^ σ := Real.rpow_nonneg h0 _
        constructor <;> linarith
      -- G ≤ Hf
      have hG : α * tspOpt c U + 2 * ∑ v, p v * distToSet c v U ≤ Hf U := by
        simp only [hHf]
        have hsplit : ∑ v, p v * distToSet c v U = p d * distToSet c d U +
            ∑ v : {v : V // v ≠ d}, p v * distToSet c v U := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ d)]
          congr 1
          rw [Finset.sum_subtype (univ.erase d) (p := fun v => v ≠ d)]
          intro v; simp
        rw [hsplit, hI.p_depot, one_mul]
        have : ∑ v : {v : V // v ≠ d}, p v * distToSet c v U ≤
            ∑ v : {v : V // v ≠ d}, (k v : ℝ) * e * distToSet c v U := by
          apply Finset.sum_le_sum; intro v _
          apply mul_le_mul_of_nonneg_right _ (distToSet_nonneg c hc _ U)
          have := (hk v).1.2; linarith
        linarith
      -- the probabilities
      have hP : subsetProb f U ≤ (1 + δ) * subsetProb qbar U := by
        by_cases hdU : d ∈ U
        · unfold subsetProb
          have hA : ∏ v ∈ U, f v ≤ ∏ v ∈ U, ((1 + lam) * qbar v) := by
            apply Finset.prod_le_prod (fun v _ => (hf01 v).1)
            intro v _
            by_cases hv : v = d
            · rw [hv, hf1, hqbar_d]; linarith
            · have := (hk ⟨v, hv⟩).2.2.1
              rw [hqbar_v v hv]; simp only [hf, powerSampling]; exact this
          have hB : ∏ v ∈ univ \ U, (1 - f v) ≤ ∏ v ∈ univ \ U, (1 - qbar v) := by
            apply Finset.prod_le_prod (fun v _ => (hf01 v).2)
            intro v hv
            have hvd : v ≠ d := by
              intro h; simp at hv; exact hv (h ▸ hdU)
            have := (hk ⟨v, hvd⟩).2.1
            rw [hqbar_v v hvd]; simp only [hf, powerSampling]
            linarith
          rw [Finset.prod_mul_distrib, Finset.prod_const] at hA
          have hpow : (1 + lam) ^ U.card ≤ 1 + δ := by
            calc (1 + lam) ^ U.card ≤ (1 + lam) ^ N :=
                  pow_le_pow_right₀ (by linarith) (by rw [hNdef]; exact Finset.card_le_univ U)
              _ ≤ 1 + δ := hlamN
          have hQA : 0 ≤ ∏ v ∈ U, qbar v := Finset.prod_nonneg (fun v _ => (hqbar01 v).1)
          have hQB : 0 ≤ ∏ v ∈ univ \ U, (1 - qbar v) :=
            Finset.prod_nonneg (fun v _ => by linarith [(hqbar01 v).2])
          have hFA : 0 ≤ ∏ v ∈ U, f v := Finset.prod_nonneg (fun v _ => (hf01 v).1)
          calc (∏ v ∈ U, f v) * ∏ v ∈ univ \ U, (1 - f v)
              ≤ ((1 + lam) ^ U.card * ∏ v ∈ U, qbar v) * ∏ v ∈ univ \ U, (1 - qbar v) :=
                mul_le_mul hA hB (Finset.prod_nonneg (fun v _ => (hf01 v).2))
                  (by positivity)
            _ ≤ ((1 + δ) * ∏ v ∈ U, qbar v) * ∏ v ∈ univ \ U, (1 - qbar v) := by
                apply mul_le_mul_of_nonneg_right _ hQB
                exact mul_le_mul_of_nonneg_right hpow hQA
            _ = (1 + δ) * ((∏ v ∈ U, qbar v) * ∏ v ∈ univ \ U, (1 - qbar v)) := by ring
        · have : subsetProb f U = 0 := by
            unfold subsetProb
            have : ∏ v ∈ univ \ U, (1 - f v) = 0 :=
              Finset.prod_eq_zero (i := d) (by simp [hdU]) (by rw [hf1]; ring)
            rw [this, mul_zero]
          rw [this]
          exact mul_nonneg (by linarith) (subsetProb_nonneg qbar hqbar01 U)
      have hPf0 : 0 ≤ subsetProb f U :=
        subsetProb_nonneg f (fun v => ⟨(hf01 v).1, by linarith [(hf01 v).2]⟩) U
      calc subsetProb f U * (α * tspOpt c U + 2 * ∑ v, p v * distToSet c v U)
          ≤ subsetProb f U * Hf U := mul_le_mul_of_nonneg_left hG hPf0
        _ ≤ ((1 + δ) * subsetProb qbar U) * Hf U := mul_le_mul_of_nonneg_right hP (hHf0 U)
        _ = (1 + δ) * (subsetProb qbar U * Hf U) := by ring
    calc samplingCost α (powerSampling σ) c p ≤ (1 + δ) * ∑ U : Finset V, subsetProb qbar U * Hf U :=
          hup
      _ ≤ (1 + δ) * samplingCost α (linSampling σ) c' p' :=
          mul_le_mul_of_nonneg_left hlow (by linarith)
  calc samplingCost α (powerSampling σ) c p ≤ (1 + δ) * samplingCost α (linSampling σ) c' p' := hS
    _ ≤ (1 + δ) * (ρ * aPrioriOpt c' p') := mul_le_mul_of_nonneg_left hH (by linarith)
    _ ≤ (1 + δ) * (ρ * aPrioriOpt c p) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hOPT hρ) (by linarith)

end main

end APTSPL9

open APTSPL9 Filter Topology in
theorem solution (α σ : ℝ) (hα : 0 ≤ α) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i ∧ ε i ≤ 1)
    (hlim : Filter.Tendsto ε Filter.atTop (nhds 0)) (ρ : ℝ) :
    (∀ (i : ℕ) (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
        IsNormalized c p d (ε i) → samplingCost α (linSampling σ) c p ≤ ρ * aPrioriOpt c p) →
      ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
        IsDepotInstance c p d → samplingCost α (powerSampling σ) c p ≤ ρ * aPrioriOpt c p := by
  intro H V _ _ c p d hI
  have hρ : 0 ≤ ρ := two_point α σ hα hσ0 hσ1 (ε 0) (hε 0).1 (hε 0).2 ρ (H 0)
  have hall : ∀ δ : ℝ, 0 < δ →
      samplingCost α (powerSampling σ) c p ≤ (1 + δ) * (ρ * aPrioriOpt c p) :=
    fun δ hδ => main_delta α σ hα hσ0 hσ1 ε hε hlim ρ hρ H V c p d hI δ hδ
  set X := samplingCost α (powerSampling σ) c p
  set Y := ρ * aPrioriOpt c p
  by_contra hcon
  push Not at hcon
  by_cases hY : Y ≤ 0
  · have := hall 1 one_pos; nlinarith
  · push Not at hY
    have := hall ((X - Y) / (2 * Y)) (by apply div_pos <;> linarith)
    have e : (1 + (X - Y) / (2 * Y)) * Y = Y + (X - Y) / 2 := by field_simp
    rw [e] at this; linarith
