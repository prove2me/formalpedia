-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Trivial
-- name    : BCFGJPSSV26_Greedy_Reduction_Trivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:56:16.293673+00:00
-- url     : https://prove2.me/theorems/beaf65b8-c55a-4844-8838-de7141df64d1
-- title:
--   BCFGJPSSV26.Greedy.Reduction.Trivial — The trivial solution
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Reduction.Trivial` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Every client's nearest facility, the least index on ties (`BCFGJPSSV26.Greedy.trivialSol`). It
--   costs at most the optimum (`BCFGJPSSV26.Greedy.cost_trivialSol_le`), since each client pays its
--   distance to the nearest facility, and if the optimum is `0` it has at most `k` facilities
--   (`BCFGJPSSV26.Greedy.trivialSol_length_le_of_opt_eq_zero`): distance `0` is an equivalence
--   relation, the clients served at distance `0` by the same optimal facility are at distance `0`
--   from each other, and clients at distance `0` from each other have the same nearest facility.
--   The algorithm outputs it whenever it is small enough, which covers
--   `opt = 0`, `n ≤ 1` and `k ≥ m`.
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Trivial`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Reduction/Trivial.lean

module

public import Definitions.Def_BCFGJPSSV26_Basic_Raw
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDups

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Reduction.Trivial` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The trivial solution

Every client's nearest facility, the least index on ties (`BCFGJPSSV26.Greedy.trivialSol`). It
costs at most the optimum (`BCFGJPSSV26.Greedy.cost_trivialSol_le`), since each client pays its
distance to the nearest facility, and if the optimum is `0` it has at most `k` facilities
(`BCFGJPSSV26.Greedy.trivialSol_length_le_of_opt_eq_zero`): distance `0` is an equivalence
relation, the clients served at distance `0` by the same optimal facility are at distance `0`
from each other, and clients at distance `0` from each other have the same nearest facility.
The algorithm outputs it whenever it is small enough, which covers
`opt = 0`, `n ≤ 1` and `k ≥ m`.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- The nearest facility to client `j`: the first `i < m` with the least `d(j, i)`. -/
def nearest (x : Raw) (j : ℕ) : ℕ :=
  (List.range x.m).foldl (fun b i ↦ if x.fdist j i < x.fdist j b then i else b) 0

/-- **The trivial solution**: the nearest facilities of the clients, without repetitions. -/
def trivialSol (x : Raw) : List ℕ := ((List.range x.n).map (nearest x)).eraseDups

/-! ### The first minimizer -/

/-- The fold of `nearest` returns the start or an element of the list. -/
theorem foldl_argmin_mem (f : ℕ → ℚ) (l : List ℕ) (b : ℕ) :
    l.foldl (fun b i ↦ if f i < f b then i else b) b ∈ b :: l := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases hab : f a < f b
    · rw [if_pos hab]
      rcases List.mem_cons.1 (ih a) with h | h <;> simp [h]
    · rw [if_neg hab]
      rcases List.mem_cons.1 (ih b) with h | h <;> simp [h]

/-- The fold of `nearest` returns a minimizer over the start and the list. -/
theorem foldl_argmin_le (f : ℕ → ℚ) (l : List ℕ) (b : ℕ) :
    f (l.foldl (fun b i ↦ if f i < f b then i else b) b) ≤ f b ∧
      ∀ i ∈ l, f (l.foldl (fun b i ↦ if f i < f b then i else b) b) ≤ f i := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons]
    by_cases hab : f a < f b
    · rw [if_pos hab]
      obtain ⟨h1, h2⟩ := ih a
      refine ⟨h1.trans hab.le, fun i hi ↦ ?_⟩
      rcases List.mem_cons.1 hi with rfl | hi
      · exact h1
      · exact h2 i hi
    · rw [if_neg hab]
      obtain ⟨h1, h2⟩ := ih b
      refine ⟨h1, fun i hi ↦ ?_⟩
      rcases List.mem_cons.1 hi with rfl | hi
      · exact h1.trans (not_lt.1 hab)
      · exact h2 i hi

/-- The fold of `nearest` depends only on the values on the start and the list. -/
theorem foldl_argmin_congr {f g : ℕ → ℚ} (l : List ℕ) (b : ℕ)
    (h : ∀ i ∈ b :: l, f i = g i) :
    l.foldl (fun b i ↦ if f i < f b then i else b) b =
      l.foldl (fun b i ↦ if g i < g b then i else b) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldl_cons, List.foldl_cons]
    have ha : f a = g a := h a (by simp)
    have hb : f b = g b := h b (by simp)
    have he : (if f a < f b then a else b) = if g a < g b then a else b := by
      rw [ha, hb]
    rw [he]
    refine ih _ fun i hi ↦ h i ?_
    rcases List.mem_cons.1 hi with rfl | hi
    · split_ifs <;> simp
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi)

variable {I : Instance}

theorem nearest_lt (hm : 1 ≤ I.m) (j : ℕ) : nearest (toRaw I) j < I.m := by
  have h := foldl_argmin_mem ((toRaw I).fdist j) (List.range (toRaw I).m) 0
  unfold nearest
  rcases List.mem_cons.1 h with h | h
  · rw [h]
    exact hm
  · simpa using h

/-- The nearest facility is nearest. -/
theorem nearest_le (hm : 1 ≤ I.m) (j : Fin I.n) (i : Fin I.m) :
    I.d (.inl j) (.inr ⟨nearest (toRaw I) j, nearest_lt hm j⟩) ≤ I.d (.inl j) (.inr i) := by
  have h := (foldl_argmin_le ((toRaw I).fdist j) (List.range (toRaw I).m) 0).2 i
    (by simp)
  rw [← Raw.fdist_toRaw (.inl j), ← Raw.fdist_toRaw (.inl j)]
  exact h

theorem mem_trivialSol {x : Raw} {i : ℕ} :
    i ∈ trivialSol x ↔ ∃ j < x.n, nearest x j = i := by
  simp [trivialSol, List.mem_eraseDups]

theorem trivialSol_eq_nil_iff : trivialSol (toRaw I) = [] ↔ I.n = 0 := by
  constructor
  · intro h
    by_contra hn
    have : nearest (toRaw I) 0 ∈ trivialSol (toRaw I) :=
      mem_trivialSol.2 ⟨0, by simp; omega, rfl⟩
    rw [h] at this
    simp at this
  · intro h
    simp [trivialSol, Raw.n, toRaw, h]

theorem isCenterList_trivialSol (hI : I.Valid) (hn : 1 ≤ I.n) :
    I.IsCenterList (trivialSol (toRaw I)) := by
  refine ⟨fun h ↦ ?_, List.nodup_eraseDups _, fun i hi ↦ ?_⟩
  · have := trivialSol_eq_nil_iff.1 h
    omega
  · obtain ⟨j, -, rfl⟩ := mem_trivialSol.1 hi
    exact nearest_lt hI.one_le_m j

theorem trivialSol_length_le_n : (trivialSol (toRaw I)).length ≤ I.n := by
  have := (List.eraseDups_sublist ((List.range (toRaw I).n).map (nearest (toRaw I)))).length_le
  simpa [trivialSol] using this

theorem trivialSol_length_le_m (hI : I.Valid) : (trivialSol (toRaw I)).length ≤ I.m := by
  have hnd : (trivialSol (toRaw I)).Nodup := List.nodup_eraseDups _
  have hsub : (trivialSol (toRaw I)).toFinset ⊆ Finset.range I.m := fun i hi ↦ by
    obtain ⟨j, -, rfl⟩ := mem_trivialSol.1 (List.mem_toFinset.1 hi)
    exact Finset.mem_range.2 (nearest_lt hI.one_le_m j)
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, Finset.card_range] at this

/-- **The trivial solution costs at most the optimum.** -/
theorem cost_trivialSol_le (hI : I.Valid) (hn : 1 ≤ I.n) :
    I.cost (I.centers (trivialSol (toRaw I))) ≤ I.opt I.k := by
  have hm := hI.one_le_m
  have hT := isCenterList_trivialSol hI hn
  have : Nonempty {S : Finset (Fin I.m) // S.Nonempty ∧ S.card ≤ I.k} :=
    ⟨⟨{⟨0, hm⟩}, by simp, by simpa using hI.one_le_k⟩⟩
  refine le_ciInf fun ⟨S, hS, _⟩ ↦ ?_
  rw [← Instance.costF_eq_cost hS,
    ← Instance.costF_eq_cost (Instance.centers_nonempty hT.1 hT.2.2)]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  obtain ⟨i, -, h⟩ := Instance.exists_dSet_eq hS (.inl j)
  rw [h]
  have hmem : (⟨nearest (toRaw I) j, nearest_lt hm j⟩ : Fin I.m) ∈
      I.centers (trivialSol (toRaw I)) :=
    Instance.mem_centers.2 (mem_trivialSol.2 ⟨j, j.2, rfl⟩)
  refine (Instance.dSet_le hmem _).trans ?_
  unfold Instance.dd
  exact_mod_cast nearest_le hm j i

/-- Clients at distance `0` from a facility `o` have the nearest facility of `o`. -/
theorem nearest_eq_of_d_eq_zero (hI : I.Valid) {j : Fin I.n} {o : Fin I.m}
    (h : I.d (.inl j) (.inr o) = 0) : nearest (toRaw I) j = nearest (toRaw I) (I.n + o) := by
  unfold nearest
  refine foldl_argmin_congr _ _ fun i hi ↦ ?_
  have hi' : i < I.m := by
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hI.one_le_m
    · simpa using hi
  have h1 := Raw.fdist_toRaw (.inl j) ⟨i, hi'⟩
  have h2 := Raw.fdist_toRaw (.inr o) ⟨i, hi'⟩
  simp only [Instance.ptIdx_inl, Instance.ptIdx_inr] at h1 h2
  rw [h1, h2]
  have t1 := hI.triangle (.inl j) (.inr o) (.inr ⟨i, hi'⟩)
  have t2 := hI.triangle (.inr o) (.inl j) (.inr ⟨i, hi'⟩)
  rw [hI.comm (.inr o) (.inl j)] at t2
  linarith

/-- **If the optimum is `0`, the trivial solution has at most `k` facilities.** -/
theorem trivialSol_length_le_of_opt_eq_zero (hI : I.Valid) (h : I.opt I.k = 0) :
    (trivialSol (toRaw I)).length ≤ I.k := by
  rcases le_or_gt I.k I.m with hkm | hkm
  swap
  · exact (trivialSol_length_le_m hI).trans hkm.le
  obtain ⟨O, hO⟩ := Instance.exists_isOpt hI hkm
  have hOne := hO.nonempty hI
  have h0 : ∀ j : Fin I.n, ∃ o ∈ O, I.d (.inl j) (.inr o) = 0 := by
    intro j
    have hsum : I.costF O = 0 := hO.cost.trans h
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦
      Instance.dSet_nonneg hI (.inl j) O).1 hsum j (Finset.mem_univ j)
    obtain ⟨o, ho, he⟩ := Instance.exists_dSet_eq hOne (.inl j)
    refine ⟨o, ho, ?_⟩
    have : I.dd (.inl j) (.inr o) = 0 := he ▸ hj
    unfold Instance.dd at this
    exact_mod_cast this
  have hnd : (trivialSol (toRaw I)).Nodup := List.nodup_eraseDups _
  have hsub : (trivialSol (toRaw I)).toFinset ⊆
      O.image fun o : Fin I.m ↦ nearest (toRaw I) (I.n + o) := fun i hi ↦ by
    obtain ⟨j, hj, rfl⟩ := mem_trivialSol.1 (List.mem_toFinset.1 hi)
    obtain ⟨o, ho, hd⟩ := h0 ⟨j, hj⟩
    exact Finset.mem_image.2 ⟨o, ho, (nearest_eq_of_d_eq_zero hI hd).symm⟩
  have := (Finset.card_le_card hsub).trans Finset.card_image_le
  rwa [List.toFinset_card_of_nodup hnd, hO.card] at this

/-- If the trivial solution has more than `k` facilities, the optimum is positive, `n ≥ 2` and
`k < min (n, m)`. -/
theorem of_k_lt_length (hI : I.Valid) (h : I.k < (trivialSol (toRaw I)).length) :
    0 < I.opt I.k ∧ 2 ≤ I.n ∧ I.k < I.n ∧ I.k < I.m := by
  have hn := trivialSol_length_le_n (I := I)
  have hm := trivialSol_length_le_m hI
  have hk := hI.one_le_k
  refine ⟨lt_of_le_of_ne (Instance.opt_nonneg' hI _) fun h0 ↦ ?_, by omega, by omega, by omega⟩
  have := trivialSol_length_le_of_opt_eq_zero hI h0.symm
  omega

end BCFGJPSSV26.Greedy


