-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMain
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:05:36.018745+00:00
-- url     : https://prove2.me/theorems/a868ffb1-d165-4a02-9a34-68a8185fd74a
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxMain — Polynomial time of the trivial solution and of the guesses
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxMain` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   With `n` and `m` in binary (`BCFGJPSSV26.encRaw`), the loops of `BCFGJPSSV26.Greedy.trivialSol`
--   and `BCFGJPSSV26.Greedy.guesses` over all clients and all facilities may be exponentially long.
--   But a client beyond the table has distance `0` to every facility, and so has a facility beyond the
--   row of a client: such clients have the nearest facility `0`, such distances are not guesses, and
--   the nearest facility of a client is already found among the facilities of its row and the first
--   facility beyond it. So both are computed by loops over the table
--   (`BCFGJPSSV26.Greedy.PT.trivialSol_eq`, `BCFGJPSSV26.Greedy.PT.guesses_eq`).
--
--   **Contents.** The module is published as a whole: 23 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMain`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxMain.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxBasic
public import Definitions.Def_BCFGJPSSV26_Greedy_Reduction_Scale
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_EraseDupsBy
public import Mathlib.Data.List.GetD
public import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_List_EraseDupsBy

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxMain` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the trivial solution and of the guesses

With `n` and `m` in binary (`BCFGJPSSV26.encRaw`), the loops of `BCFGJPSSV26.Greedy.trivialSol`
and `BCFGJPSSV26.Greedy.guesses` over all clients and all facilities may be exponentially long.
But a client beyond the table has distance `0` to every facility, and so has a facility beyond the
row of a client: such clients have the nearest facility `0`, such distances are not guesses, and
the nearest facility of a client is already found among the facilities of its row and the first
facility beyond it. So both are computed by loops over the table
(`BCFGJPSSV26.Greedy.PT.trivialSol_eq`, `BCFGJPSSV26.Greedy.PT.guesses_eq`).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### Distances beyond the table -/

theorem fdist_out_row (x : Raw) (j i : ℕ) (h : (x.table.getD j []).length - x.n ≤ i) :
    x.fdist j i = 0 := by
  unfold Raw.fdist Raw.dist
  exact List.getD_eq_default _ _ (by omega)

theorem fdist_out (x : Raw) (j i : ℕ) (h : x.table.length ≤ j) : x.fdist j i = 0 := by
  unfold Raw.fdist Raw.dist
  rw [List.getD_eq_default _ _ h]
  rfl

/-- The step of the search for the nearest facility. -/
def nstep (v : ℕ → ℚ) (b i : ℕ) : ℕ := if v i < v b then i else b

theorem foldl_nstep_le (v : ℕ → ℚ) (l : List ℕ) (b : ℕ) :
    v (l.foldl (nstep v) b) ≤ v b ∧ ∀ i ∈ l, v (l.foldl (nstep v) b) ≤ v i := by
  induction l generalizing b with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (nstep v b i)
    have h3 : v (nstep v b i) ≤ v b ∧ v (nstep v b i) ≤ v i := by
      unfold nstep
      split_ifs with h
      · exact ⟨h.le, le_rfl⟩
      · exact ⟨le_rfl, not_lt.1 h⟩
    refine ⟨h1.trans h3.1, fun i' hi' ↦ ?_⟩
    rcases List.mem_cons.1 hi' with rfl | hi'
    · exact h1.trans h3.2
    · exact h2 i' hi'

theorem foldl_nstep_zero (v : ℕ → ℚ) (l : List ℕ) (b : ℕ) (hb : v b ≤ 0)
    (hl : ∀ i ∈ l, v i = 0) : l.foldl (nstep v) b = b := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons]
    have : nstep v b i = b := by
      unfold nstep
      rw [hl i (List.mem_cons_self ..)]
      exact if_neg (not_lt.2 hb)
    rw [this]
    exact ih fun i' hi' ↦ hl i' (List.mem_cons_of_mem _ hi')

/-- **The nearest facility is found among the facilities of the row** and the first facility
beyond it. -/
theorem foldl_nstep_cut (v : ℕ → ℚ) (m s : ℕ) (hv : ∀ i, s ≤ i → v i = 0) :
    (List.range m).foldl (nstep v) 0 = (List.range (min (s + 1) m)).foldl (nstep v) 0 := by
  rcases Nat.lt_or_ge s m with h | h
  swap
  · rw [show min (s + 1) m = m by omega]
  have hm : m = min (s + 1) m + (m - min (s + 1) m) := by omega
  conv_lhs => rw [hm, List.range_add, List.foldl_append]
  refine foldl_nstep_zero v _ _ ?_ ?_
  · have := (foldl_nstep_le v (List.range (min (s + 1) m)) 0).2 s
      (List.mem_range.2 (by omega))
    rw [hv s le_rfl] at this
    exact this
  · intro i hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hi
    rw [List.mem_range] at hi'
    exact hv _ (by omega)

theorem nearest_eq (x : Raw) (j : ℕ) : nearest x j =
    (List.range (min ((x.table.getD j []).length - x.n + 1) x.m)).foldl (nstep (x.fdist j)) 0 :=
  foldl_nstep_cut (x.fdist j) x.m _ fun i hi ↦ fdist_out_row x j i hi

theorem nearest_out (x : Raw) (j : ℕ) (h : x.table.length ≤ j) : nearest x j = 0 := by
  unfold nearest
  exact foldl_nstep_zero (x.fdist j) _ 0 (by rw [fdist_out x j 0 h]) fun i _ ↦ fdist_out x j i h

theorem map_nearest (x : Raw) : (List.range x.n).map (nearest x) =
    (List.range (min x.table.length x.n)).map (nearest x) ++
      List.replicate (x.n - min x.table.length x.n) 0 := by
  have hn : x.n = min x.table.length x.n + (x.n - min x.table.length x.n) := by omega
  conv_lhs => rw [hn, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.eq_replicate_iff.2 ⟨by simp, fun b hb ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
  rw [List.mem_range] at hi
  refine nearest_out x _ ?_
  change x.table.length ≤ min x.table.length x.n + i
  omega

theorem eraseDups_replicate_zero (l : List ℕ) (k : ℕ) :
    (l ++ List.replicate k 0).eraseDups = (l ++ if k = 0 then [] else [0]).eraseDups := by
  rcases k with _ | k
  · simp
  · rw [List.eraseDups_append, List.eraseDups_append, if_neg (by omega)]
    congr 1
    simp only [List.removeAll, List.filter_replicate, List.filter_cons, List.filter_nil]
    split_ifs <;> simp [List.replicate_succ, List.eraseDups_cons]

/-- **The trivial solution, by a loop over the table.** -/
theorem trivialSol_eq (x : Raw) : trivialSol x =
    ((List.range (min x.table.length x.n)).map (fun j ↦
      (List.range (min ((x.table.getD j []).length - x.n + 1) x.m)).foldl
        (nstep (x.fdist j)) 0) ++
      if x.n - min x.table.length x.n = 0 then [] else [0]).eraseDups := by
  unfold trivialSol
  rw [map_nearest, eraseDups_replicate_zero, show nearest x = _ from funext (nearest_eq x)]

theorem length_trivialSol_le (x : Raw) : (trivialSol x).length ≤ x.table.length + 1 := by
  rw [trivialSol_eq]
  refine (List.eraseDupsBy_sublist _).length_le.trans ?_
  simp only [List.length_append, List.length_map, List.length_range]
  split_ifs <;> simp

/-- **The guesses, by a loop over the table.** -/
theorem guesses_eq (x : Raw) : guesses x =
    (List.range (min x.table.length x.n)).flatMap fun j ↦
      ((List.range (min ((x.table.getD j []).length - x.n) x.m)).map (x.fdist j)).filter
        fun q ↦ decide (0 < q) := by
  unfold guesses
  rw [List.filter_flatMap]
  have hn : x.n = min x.table.length x.n + (x.n - min x.table.length x.n) := by omega
  conv_lhs => rw [hn, List.range_add, List.flatMap_append]
  have h2 : (List.map (fun y ↦ min x.table.length x.n + y)
      (List.range (x.n - min x.table.length x.n))).flatMap (fun j ↦
        ((List.range x.m).map (x.fdist j)).filter fun q ↦ decide (0 < q)) = [] := by
    refine List.flatMap_eq_nil_iff.2 fun j hj ↦ ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
    rw [List.mem_range] at hi
    have : x.table.length ≤ min x.table.length x.n + i := by omega
    refine List.filter_eq_nil_iff.2 fun q hq ↦ ?_
    obtain ⟨i', -, rfl⟩ := List.mem_map.1 hq
    rw [fdist_out x _ i' this]
    simp
  rw [h2, List.append_nil]
  refine List.flatMap_congr fun j _ ↦ ?_
  set s := (x.table.getD j []).length - x.n
  have hm : x.m = min s x.m + (x.m - min s x.m) := by omega
  conv_lhs => rw [hm, List.range_add, List.map_append, List.filter_append]
  have h3 : ((List.map (fun y ↦ min s x.m + y) (List.range (x.m - min s x.m))).map
      (x.fdist j)).filter (fun q ↦ decide (0 < q)) = [] := by
    refine List.filter_eq_nil_iff.2 fun q hq ↦ ?_
    obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hq
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hi'
    rw [List.mem_range] at hi
    rw [fdist_out_row x j _ (by omega)]
    simp
  rw [h3, List.append_nil]

/-! ### Certificates -/

variable {α : Type} {input : α ↪ List Bool}

theorem rawNB {X : α → Raw} (hX : ComputableInPolyTime X input encRaw) :
    ComputableInPolyTime (fun a ↦ (X a).n) input encNat := (fst _ _).comp hX

theorem rawMB {X : α → Raw} (hX : ComputableInPolyTime X input encRaw) :
    ComputableInPolyTime (fun a ↦ (X a).m) input encNat := ((fst _ _).comp (snd _ _)).comp hX

theorem rawTL {X : α → Raw} (hX : ComputableInPolyTime X input encRaw) :
    ComputableInPolyTime (fun a ↦ (X a).table) input (encList (encList encRat)) :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp hX

theorem rowsU {X : α → Raw} (hX : ComputableInPolyTime X input encRaw) :
    ComputableInPolyTime (fun a ↦ min (X a).table.length (X a).n) input encUnary :=
  binary_min_unary' ((length_list _).comp (rawTL hX)) (rawNB hX)

theorem rowLenU {X : α → Raw} {j : α → ℕ} (hX : ComputableInPolyTime X input encRaw)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ ((X a).table.getD (j a) []).length) input encUnary :=
  (length_list _).comp (listGetD_binary (encA := encList encRat) [] (rawTL hX) hj)

theorem fdistQ {X : α → Raw} {j i : α → ℕ} (hX : ComputableInPolyTime X input encRaw)
    (hj : ComputableInPolyTime j input encNat) (hi : ComputableInPolyTime i input encNat) :
    ComputableInPolyTime (fun a ↦ (X a).fdist (j a) (i a)) input encRat :=
  listGetD_binary (encA := encRat) 0 (listGetD_binary (encA := encList encRat) [] (rawTL hX) hj)
    (binAdd (rawNB hX) hi)

theorem nearCntU {X : α → Raw} {j : α → ℕ} (hX : ComputableInPolyTime X input encRaw)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ min (((X a).table.getD (j a) []).length - (X a).n + 1) (X a).m)
      input encUnary := by
  have hρ := rowLenU hX hj
  exact binary_min_unary' (binary_to_unary_bounded (binAdd (binary_sub' (toBin hρ) (rawNB hX))
    (const 1)) (unary_add' hρ (const 1)) fun a ↦ by omega) (rawMB hX)

theorem nearestB {X : α → Raw} {j : α → ℕ} (hX : ComputableInPolyTime X input encRaw)
    (hj : ComputableInPolyTime j input encNat) :
    ComputableInPolyTime (fun a ↦ (List.range (min (((X a).table.getD (j a) []).length - (X a).n +
      1) (X a).m)).foldl (nstep ((X a).fdist (j a))) 0) input encNat := by
  have hl := unary_range' (nearCntU hX hj)
  have hstep : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ nstep ((X q.1.1).fdist (j q.1.1))
      q.1.2 q.2) (encPair (encPair input encNat) encUnary) encNat := by
    unfold nstep
    have hX' : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ X q.1.1)
        (encPair (encPair input encNat) encUnary) encRaw := hX.comp ((fst _ _).comp (fst _ _))
    exact itep (rat_lt' (fdistQ hX' (hj.comp ((fst _ _).comp (fst _ _))) (toBin (snd _ _)))
      (fdistQ hX' (hj.comp ((fst _ _).comp (fst _ _))) ((snd _ _).comp (fst _ _))))
      (toBin (snd _ _)) ((snd _ _).comp (fst _ _))
  refine foldlWithInput_of_bounded_growth (step := fun a b i ↦ nstep ((X a).fdist (j a)) b i)
    (const 0) ⟨hl, hstep, inferInstance, inferInstance⟩
    (growth := fun a ↦ (encList encUnary (List.range (min (((X a).table.getD (j a) []).length -
      (X a).n + 1) (X a).m))).length) ⟨hl.polyBounded_length, ?_⟩
  intro a b i hi
  have h := SizedListEncoding.length_elem_le (encA := encUnary) (encL := encList encUnary) _ i hi
  have h2 := len_encNat_le_self i
  simp only [encUnary_apply, List.length_replicate] at h
  unfold nstep
  split_ifs <;> omega

theorem trivialSolL {X : α → Raw} (hX : ComputableInPolyTime X input encRaw) :
    ComputableInPolyTime (fun a ↦ trivialSol (X a)) input (encList encNat) := by
  simp only [trivialSol_eq]
  have hl := listAppend' (mapWithInput (f := fun a j ↦ (List.range (min (((X a).table.getD j
      []).length - (X a).n + 1) (X a).m)).foldl (nstep ((X a).fdist j)) 0)
    (unary_range' (rowsU hX)) (nearestB (hX.comp (fst _ _)) (toBin (snd _ _))))
    (itep (decide_eq' (binary_sub' (rawNB hX) (toBin (rowsU hX))) (const 0)) (const [])
      (const [0]))
  exact eraseDupsByWithInput (r := fun _ i j ↦ i == j) hl (beq ((snd _ _).comp (fst _ _))
    (snd _ _))

theorem guessesL {X : α → Raw} (hX : ComputableInPolyTime X input encRaw) :
    ComputableInPolyTime (fun a ↦ guesses (X a)) input (encList encRat) := by
  simp only [guesses_eq]
  have hX' := hX.comp (fst input encUnary)
  have hρ := rowLenU hX' (toBin (snd _ _))
  have hc : ComputableInPolyTime (fun q : α × ℕ ↦
      min (((X q.1).table.getD q.2 []).length - (X q.1).n) (X q.1).m) (encPair input encUnary)
      encUnary :=
    binary_min_unary' (binary_to_unary_bounded (binary_sub' (toBin hρ) (rawNB hX')) hρ
      fun _ ↦ Nat.sub_le _ _) (rawMB hX')
  refine flatMapWithInput (f := fun a j ↦ ((List.range (min (((X a).table.getD j []).length -
    (X a).n) (X a).m)).map ((X a).fdist j)).filter fun q ↦ decide (0 < q))
    (unary_range' (rowsU hX)) ?_
  exact filterWithInput (test := fun _ q ↦ decide (0 < q))
    (mapWithInput (f := fun (q : α × ℕ) i ↦ (X q.1).fdist q.2 i) (unary_range' hc)
      (fdistQ (hX'.comp (fst _ _)) (toBin ((snd _ _).comp (fst _ _))) (toBin (snd _ _))))
    (rat_lt' (const 0) (snd _ _))

end BCFGJPSSV26.Greedy.PT


