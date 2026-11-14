-- Prove2me | Definitions.Def_BCFGJPSSV26_Basic_Raw
-- name    : BCFGJPSSV26_Basic_Raw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:55:23.319351+00:00
-- url     : https://prove2.me/theorems/f14db2b9-a0b4-4f3a-8f04-ed1db3626c59
-- title:
--   BCFGJPSSV26.Basic.Raw — Instances as the algorithms read them
-- statement:
--   This is module `BCFGJPSSV26.Basic.Raw` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Algorithms read an instance as its encoding gives it: the tuple `(n, m, k, table)`
--   (`BCFGJPSSV26.Raw`, `BCFGJPSSV26.toRaw`), whose encoding `BCFGJPSSV26.encRaw` is that of the
--   instance (`BCFGJPSSV26.encInstance_eq`, by definition). Points are numbers: client `j` is `j`,
--   facility `i` is `n + i` (`BCFGJPSSV26.Instance.ptIdx`). Everything is computed exactly, over `ℚ`,
--   and agrees with the real-valued notions of `BCFGJPSSV26/Basic/Metric.lean`:
--
--   * distances by table lookup (`BCFGJPSSV26.Raw.dist`, `BCFGJPSSV26.Raw.dist_toRaw`);
--   * the distance to a list of facilities, `dMax` for the empty list (`BCFGJPSSV26.Raw.dSetQ`,
--     `BCFGJPSSV26.Raw.dSetQ_toRaw`);
--   * costs of lists of facilities (`BCFGJPSSV26.Raw.cost`, `BCFGJPSSV26.Raw.cost_toRaw`), on lists
--     of clients too (`BCFGJPSSV26.Raw.costOn`);
--   * the nearest facility with the least index on ties (`BCFGJPSSV26.Raw.nearQ`,
--     `BCFGJPSSV26.Raw.nearQ_toRaw`) and clusters (`BCFGJPSSV26.Raw.clusterQ`).
--
--   **Exactly `k` facilities** (`BCFGJPSSV26.sanitizeK`): any list becomes a list of exactly `k`
--   distinct facilities when `k ≤ m` (`BCFGJPSSV26.sanitizeK_spec`), by keeping its facilities, once
--   each, adding the others in order, and keeping the first `k`. A list of at most `k` distinct
--   facilities only gains facilities (`BCFGJPSSV26.subset_sanitizeK`), so its cost does not rise
--   (`BCFGJPSSV26.costF_sanitizeK_le`).
--
--   **Contents.** The module is published as a whole: 49 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Basic_Raw`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Basic/Raw.lean

module

public import Definitions.Def_BCFGJPSSV26_Basic_Metric
public import Definitions.Def_BCFGJPSSV26_Combine_Algorithm

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Basic.Raw` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Instances as the algorithms read them

Algorithms read an instance as its encoding gives it: the tuple `(n, m, k, table)`
(`BCFGJPSSV26.Raw`, `BCFGJPSSV26.toRaw`), whose encoding `BCFGJPSSV26.encRaw` is that of the
instance (`BCFGJPSSV26.encInstance_eq`, by definition). Points are numbers: client `j` is `j`,
facility `i` is `n + i` (`BCFGJPSSV26.Instance.ptIdx`). Everything is computed exactly, over `ℚ`,
and agrees with the real-valued notions of `BCFGJPSSV26/Basic/Metric.lean`:

* distances by table lookup (`BCFGJPSSV26.Raw.dist`, `BCFGJPSSV26.Raw.dist_toRaw`);
* the distance to a list of facilities, `dMax` for the empty list (`BCFGJPSSV26.Raw.dSetQ`,
  `BCFGJPSSV26.Raw.dSetQ_toRaw`);
* costs of lists of facilities (`BCFGJPSSV26.Raw.cost`, `BCFGJPSSV26.Raw.cost_toRaw`), on lists
  of clients too (`BCFGJPSSV26.Raw.costOn`);
* the nearest facility with the least index on ties (`BCFGJPSSV26.Raw.nearQ`,
  `BCFGJPSSV26.Raw.nearQ_toRaw`) and clusters (`BCFGJPSSV26.Raw.clusterQ`).

**Exactly `k` facilities** (`BCFGJPSSV26.sanitizeK`): any list becomes a list of exactly `k`
distinct facilities when `k ≤ m` (`BCFGJPSSV26.sanitizeK_spec`), by keeping its facilities, once
each, adding the others in order, and keeping the first `k`. A list of at most `k` distinct
facilities only gains facilities (`BCFGJPSSV26.subset_sanitizeK`), so its cost does not rise
(`BCFGJPSSV26.costF_sanitizeK_le`).
-/

@[expose] public section

namespace BCFGJPSSV26

open Encoding Finset

/-! ### The tuple -/

/-- An instance as the algorithms read it: `n`, `m`, `k` and the table of distances. -/
abbrev Raw : Type := ℕ × ℕ × ℕ × List (List ℚ)

/-- The tuple of an instance. -/
def toRaw (I : Instance) : Raw := (I.n, I.m, I.k, distTable I)

/-- The encoding of the tuple, that of `encInstance`. -/
abbrev encRaw : Raw ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encList (encList encRat))))

/-- **The encoding of an instance is that of its tuple.** -/
theorem encInstance_eq (I : Instance) : encInstance I = encRaw (toRaw I) := rfl

namespace Raw

/-- The number of clients. -/
def n (x : Raw) : ℕ := x.1

/-- The number of facilities. -/
def m (x : Raw) : ℕ := x.2.1

/-- The number of centers. -/
def k (x : Raw) : ℕ := x.2.2.1

/-- The table of distances. -/
def table (x : Raw) : List (List ℚ) := x.2.2.2

@[simp] theorem n_toRaw (I : Instance) : (toRaw I).n = I.n := rfl
@[simp] theorem m_toRaw (I : Instance) : (toRaw I).m = I.m := rfl
@[simp] theorem k_toRaw (I : Instance) : (toRaw I).k = I.k := rfl
@[simp] theorem table_toRaw (I : Instance) : (toRaw I).table = distTable I := rfl

/-- The distance between the points numbered `a` and `b` (clients `0, …, n - 1`, then the
facilities), by table lookup; `0` outside the table. -/
def dist (x : Raw) (a b : ℕ) : ℚ := (x.table.getD a []).getD b 0

/-- The distance from the point numbered `a` to facility `i`. -/
def fdist (x : Raw) (a i : ℕ) : ℚ := x.dist a (x.n + i)

/-- A distance larger than every distance: `1` plus the sum of the table. -/
def dMaxQ (x : Raw) : ℚ := 1 + (x.table.map List.sum).sum

/-- The distance from the point numbered `a` to the nearest facility of `S`, and `dMaxQ` if `S` is
empty. -/
def dSetQ (x : Raw) (a : ℕ) (S : List ℕ) : ℚ :=
  if S = [] then x.dMaxQ else Combine.minQ (S.map (x.fdist a))

/-- The cost of a list of facilities. -/
def cost (x : Raw) (S : List ℕ) : ℚ := Combine.costQ x.n x.table S

/-- The cost of the clients of `D` in the list `S` of facilities. -/
def costOn (x : Raw) (S D : List ℕ) : ℚ := (D.map fun j ↦ x.dSetQ j S).sum

/-- Whether facility `i` is at least as near to `a` as facility `i'`, ties broken by the least
index: the order of the pairs `(d(a, i), i)`. -/
def nearLE (x : Raw) (a i i' : ℕ) : Bool :=
  decide (x.fdist a i < x.fdist a i' ∨ (x.fdist a i = x.fdist a i' ∧ i ≤ i'))

/-- The **nearest facility** of `S` to the point numbered `a`, the least index on ties; `0` if `S`
is empty. -/
def nearQ (x : Raw) (a : ℕ) (S : List ℕ) : ℕ :=
  (S.find? fun i ↦ S.all fun i' ↦ x.nearLE a i i').getD 0

/-- The **cluster** of `c` in `S`: the clients whose nearest facility of `S` is `c`, in order. -/
def clusterQ (x : Raw) (S : List ℕ) (c : ℕ) : List ℕ :=
  (List.range x.n).filter fun j ↦ decide (x.nearQ j S = c)

end Raw

/-! ### Points as numbers -/

namespace Instance

variable {I : Instance}

variable (I) in
/-- The number of a point: client `j` is `j`, facility `i` is `n + i`. -/
def ptIdx (a : I.Pt) : ℕ := Sum.elim (fun j ↦ j.1) (fun i ↦ I.n + i.1) a

theorem ptIdx_eq (a : I.Pt) : I.ptIdx a = (finSumFinEquiv a : ℕ) := by
  cases a <;> simp [ptIdx]

@[simp] theorem ptIdx_inl (j : Fin I.n) : I.ptIdx (.inl j) = j := rfl
@[simp] theorem ptIdx_inr (i : Fin I.m) : I.ptIdx (.inr i) = I.n + i := rfl

/-! ### Lists of facilities -/

theorem mem_centers {S : List ℕ} {i : Fin I.m} : i ∈ I.centers S ↔ i.1 ∈ S := by
  simp [Instance.centers]

theorem centers_nonempty {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) :
    (I.centers S).Nonempty := by
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil S hS
  exact ⟨⟨i, hm i hi⟩, mem_centers.2 hi⟩

theorem centers_mono {S T : List ℕ} (h : ∀ i ∈ S, i ∈ T) : I.centers S ⊆ I.centers T :=
  fun _ hi ↦ mem_centers.2 (h _ (mem_centers.1 hi))

theorem map_val_centers {S : List ℕ} (hm : ∀ i ∈ S, i < I.m) :
    (I.centers S).map Fin.valEmbedding = S.toFinset := by
  ext i
  simp only [mem_map, Fin.valEmbedding_apply, List.mem_toFinset, mem_centers]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hi
    exact ⟨⟨i, hm i hi⟩, hi, rfl⟩

/-- A list of distinct facilities has as many facilities as entries. -/
theorem card_centers {S : List ℕ} (hS : S.Nodup) (hm : ∀ i ∈ S, i < I.m) :
    (I.centers S).card = S.length := by
  rw [← card_map Fin.valEmbedding, map_val_centers hm, List.toFinset_card_of_nodup hS]

/-- A list has at least as many entries as facilities. -/
theorem card_centers_le (S : List ℕ) : (I.centers S).card ≤ S.length := by
  classical
  calc (I.centers S).card = ((I.centers S).map Fin.valEmbedding).card := (card_map _).symm
    _ ≤ S.toFinset.card := card_le_card fun i hi ↦ by
        obtain ⟨a, ha, rfl⟩ := mem_map.1 hi
        exact List.mem_toFinset.2 (mem_centers.1 ha)
    _ ≤ S.length := List.toFinset_card_le S

end Instance

/-! ### Exact distances and costs -/

namespace Raw

variable {I : Instance}

theorem distTable_getD (I : Instance) (a b : Fin (I.n + I.m)) :
    ((distTable I).getD a.1 []).getD b.1 0 =
      I.d (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
  have ha : a.1 < (distTable I).length := by simp [distTable]
  rw [List.getD_eq_getElem?_getD (l := distTable I), List.getElem?_eq_getElem ha,
    Option.getD_some]
  have hb : b.1 < ((distTable I)[a.1]).length := by simp [distTable]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  simp [distTable]

/-- **Distances by table lookup.** -/
theorem dist_toRaw (a b : I.Pt) : (toRaw I).dist (I.ptIdx a) (I.ptIdx b) = I.d a b := by
  rw [Instance.ptIdx_eq, Instance.ptIdx_eq, dist, table_toRaw, distTable_getD]
  simp

theorem fdist_toRaw (a : I.Pt) (i : Fin I.m) :
    (toRaw I).fdist (I.ptIdx a) i = I.d a (.inr i) := by
  rw [fdist, n_toRaw, ← Instance.ptIdx_inr, dist_toRaw]

theorem dMaxQ_toRaw (I : Instance) : ((toRaw I).dMaxQ : ℝ) = I.dMax := by
  have h : ((distTable I).map List.sum).sum =
      ∑ a : Fin (I.n + I.m), ∑ b : Fin (I.n + I.m),
        I.d (finSumFinEquiv.symm a) (finSumFinEquiv.symm b) := by
    simp only [distTable, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  rw [dMaxQ, table_toRaw, h, Instance.dMax]
  push_cast
  congr 1
  rw [← (finSumFinEquiv (m := I.n) (n := I.m)).symm.sum_comp]
  refine sum_congr rfl fun a _ ↦ ?_
  rw [← (finSumFinEquiv (m := I.n) (n := I.m)).symm.sum_comp]
  rfl

theorem minQ_toRaw {a : I.Pt} {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) :
    (Combine.minQ (S.map ((toRaw I).fdist (I.ptIdx a))) : ℝ) = I.dSet a (I.centers S) := by
  have hl : S.map ((toRaw I).fdist (I.ptIdx a)) ≠ [] := by simpa using hS
  obtain ⟨hmem, hle⟩ := Combine.minQ_spec hl
  obtain ⟨i₀, hi₀, hq⟩ := List.mem_map.1 hmem
  have hc₀ : (⟨i₀, hm i₀ hi₀⟩ : Fin I.m) ∈ I.centers S := Instance.mem_centers.2 hi₀
  refine le_antisymm ?_ ?_
  · refine Instance.le_dSet ⟨_, hc₀⟩ fun i hi ↦ ?_
    have := hle _ (List.mem_map.2 ⟨i.1, Instance.mem_centers.1 hi, rfl⟩)
    rw [fdist_toRaw] at this
    unfold Instance.dd
    exact_mod_cast this
  · refine (Instance.dSet_le hc₀ a).trans (le_of_eq ?_)
    have h := fdist_toRaw (I := I) a ⟨i₀, hm i₀ hi₀⟩
    rw [← hq]
    unfold Instance.dd
    rw [← h]

/-- **The exact distance to a list of facilities** is the distance to its set of facilities. -/
theorem dSetQ_toRaw (a : I.Pt) {S : List ℕ} (hm : ∀ i ∈ S, i < I.m) :
    ((toRaw I).dSetQ (I.ptIdx a) S : ℝ) = I.dSet a (I.centers S) := by
  rcases eq_or_ne S [] with rfl | hS
  · have : I.centers [] = ∅ := by ext i; simp [Instance.centers]
    rw [dSetQ, if_pos rfl, this, Instance.dSet_empty, dMaxQ_toRaw]
  · rw [dSetQ, if_neg hS, minQ_toRaw hS hm]

/-- **The exact cost of a list of facilities** is its cost. -/
theorem cost_toRaw {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) :
    ((toRaw I).cost S : ℝ) = I.costF (I.centers S) := by
  rw [Instance.costF_eq_cost (Instance.centers_nonempty hS hm), ← Combine.costQ_eq I hS hm]
  rfl

/-- The exact cost on a list of distinct clients. -/
theorem costOn_toRaw {S D : List ℕ} (hm : ∀ i ∈ S, i < I.m) (hD : D.Nodup)
    (hn : ∀ j ∈ D, j < I.n) :
    ((toRaw I).costOn S D : ℝ) =
      I.costOn (I.centers S) ((Finset.univ : Finset (Fin I.n)).filter fun j ↦ j.1 ∈ D) := by
  have hf : ∀ j : Fin I.n, I.dSet (.inl j) (I.centers S) = ((toRaw I).dSetQ j S : ℝ) :=
    fun j ↦ (dSetQ_toRaw (.inl j) hm).symm
  have hmap : ((Finset.univ : Finset (Fin I.n)).filter fun j ↦ j.1 ∈ D).map Fin.valEmbedding =
      D.toFinset := by
    ext j
    simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply,
      List.mem_toFinset]
    exact ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ha, fun h ↦ ⟨⟨j, hn j h⟩, h, rfl⟩⟩
  unfold Instance.costOn costOn
  rw [Rat.cast_list_sum, List.map_map]
  simp_rw [hf]
  rw [← List.sum_toFinset _ hD, ← hmap, Finset.sum_map]
  rfl

theorem nearLE_toRaw (a : I.Pt) (i i' : Fin I.m) :
    (toRaw I).nearLE (I.ptIdx a) i i' = true ↔
      I.dd a (.inr i) < I.dd a (.inr i') ∨ (I.dd a (.inr i) = I.dd a (.inr i') ∧ i ≤ i') := by
  simp only [nearLE, decide_eq_true_eq, fdist_toRaw, Instance.dd, Rat.cast_lt, Rat.cast_inj,
    Fin.le_def]

/-- **The exact nearest facility** is the nearest facility. -/
theorem nearQ_toRaw (a : I.Pt) {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) :
    (toRaw I).nearQ (I.ptIdx a) S = (I.near (I.centers S) (Instance.centers_nonempty hS hm) a).1 :=
  by
  set hne := Instance.centers_nonempty hS hm
  set c := I.near (I.centers S) hne a
  have hcS : c.1 ∈ S := Instance.mem_centers.1 (Instance.near_mem hne a)
  -- the nearest facility is below all others in the order of `nearLE`
  have hc : ∀ i' ∈ S, (toRaw I).nearLE (I.ptIdx a) c i' = true := by
    intro i' hi'
    have h := (nearLE_toRaw a c ⟨i', hm i' hi'⟩).2
    refine h ?_
    have hle := Instance.dSet_le (Instance.mem_centers.2 (show (⟨i', hm i' hi'⟩ : Fin I.m).1 ∈ S
      from hi')) a
    rw [← Instance.dd_near hne a] at hle
    rcases hle.lt_or_eq with hlt | heq
    · exact .inl hlt
    · refine .inr ⟨heq, Instance.near_le hne (Instance.mem_centers.2 hi') ?_⟩
      rw [← heq, Instance.dd_near]
  have hsome : (S.find? fun i ↦ S.all fun i' ↦ (toRaw I).nearLE (I.ptIdx a) i i').isSome := by
    rw [List.find?_isSome]
    exact ⟨c.1, hcS, List.all_eq_true.2 hc⟩
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hsome
  have hiS := List.mem_of_find?_eq_some hi
  have hp : ∀ i' ∈ S, (toRaw I).nearLE (I.ptIdx a) i i' = true :=
    List.all_eq_true.1 (List.find?_some (p := fun i ↦ S.all fun i' ↦
      (toRaw I).nearLE (I.ptIdx a) i i') hi)
  unfold nearQ
  rw [hi, Option.getD_some]
  -- `i` and the nearest facility are below each other
  have h1 := (nearLE_toRaw a ⟨i, hm i hiS⟩ c).1 (hp c.1 hcS)
  have h2 := (nearLE_toRaw a c ⟨i, hm i hiS⟩).1 (hc i hiS)
  have : (⟨i, hm i hiS⟩ : Fin I.m) = c := by
    rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
    · exact absurd (h1.trans h2) (lt_irrefl _)
    · exact absurd h1 (by rw [h2]; exact lt_irrefl _)
    · exact absurd h2 (by rw [h1]; exact lt_irrefl _)
    · exact le_antisymm h1' h2'
  rw [← this]

theorem mem_clusterQ {S : List ℕ} (hS : S ≠ []) (hm : ∀ i ∈ S, i < I.m) {c : Fin I.m}
    {j : Fin I.n} : j.1 ∈ (toRaw I).clusterQ S c ↔ j ∈ I.cluster (I.centers S) c := by
  rw [clusterQ, List.mem_filter, Instance.mem_cluster (Instance.centers_nonempty hS hm)]
  simp only [List.mem_range, n_toRaw, j.2, true_and, decide_eq_true_eq]
  rw [← Instance.ptIdx_inl, nearQ_toRaw _ hS hm, Fin.val_inj]

end Raw

/-! ### Exactly `k` facilities -/

/-- **Exactly `k` facilities**: the facilities of `X` (entries `< m`), once each, then the other
facilities in order, cut at `k`. -/
def sanitizeK (m k : ℕ) (X : List ℕ) : List ℕ :=
  ((X.filter fun i ↦ decide (i < m)).dedup ++
    (List.range m).filter fun i ↦ decide (i ∉ X)).take k

theorem perm_sanitizeFull (m : ℕ) (X : List ℕ) :
    ((X.filter fun i ↦ decide (i < m)).dedup ++
      (List.range m).filter fun i ↦ decide (i ∉ X)).Perm (List.range m) := by
  have hnd : ((X.filter fun i ↦ decide (i < m)).dedup ++
      (List.range m).filter fun i ↦ decide (i ∉ X)).Nodup := by
    refine List.nodup_append.2 ⟨List.nodup_dedup _, (List.nodup_range).filter _, ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [List.mem_dedup, List.mem_filter, decide_eq_true_eq] at ha hb
    exact hb.2 ha.1
  refine (List.perm_ext_iff_of_nodup hnd List.nodup_range).2 fun i ↦ ?_
  simp only [List.mem_append, List.mem_dedup, List.mem_filter, List.mem_range, decide_eq_true_eq]
  tauto

/-- **`sanitizeK` gives exactly `k` distinct facilities**, for `k ≤ m`, whatever `X` is. -/
theorem sanitizeK_spec {m k : ℕ} (hk : k ≤ m) (X : List ℕ) :
    (sanitizeK m k X).Nodup ∧ (sanitizeK m k X).length = k ∧ ∀ i ∈ sanitizeK m k X, i < m := by
  have hp := perm_sanitizeFull m X
  refine ⟨(hp.nodup_iff.2 List.nodup_range).sublist (List.take_sublist _ _), ?_, fun i hi ↦ ?_⟩
  · rw [sanitizeK, List.length_take, hp.length_eq, List.length_range]
    omega
  · exact List.mem_range.1 (hp.subset (List.mem_of_mem_take hi))

/-- The output of `sanitizeK` is a list of exactly `k` facilities of the instance. -/
theorem isCenterList_sanitizeK {I : Instance} (hv : I.Valid) (hk : I.k ≤ I.m) (X : List ℕ) :
    I.IsCenterList (sanitizeK I.m I.k X) ∧ (sanitizeK I.m I.k X).length = I.k := by
  obtain ⟨h1, h2, h3⟩ := sanitizeK_spec hk X
  refine ⟨⟨?_, h1, h3⟩, h2⟩
  intro h
  rw [h, List.length_nil] at h2
  have := hv.one_le_k
  omega

/-- **A list of at most `k` distinct facilities only gains facilities.** -/
theorem subset_sanitizeK {m k : ℕ} {X : List ℕ} (hX : X.Nodup) (hm : ∀ i ∈ X, i < m)
    (hXk : X.length ≤ k) : ∀ i ∈ X, i ∈ sanitizeK m k X := by
  intro i hi
  have hf : (X.filter fun i ↦ decide (i < m)) = X :=
    List.filter_eq_self.2 fun a ha ↦ decide_eq_true (hm a ha)
  rw [sanitizeK, hf, hX.dedup, List.take_append, List.take_of_length_le hXk]
  exact List.mem_append_left _ hi

/-- **`sanitizeK` keeps a list of exactly `k` distinct facilities.** -/
theorem sanitizeK_eq_self {m k : ℕ} {X : List ℕ} (hX : X.Nodup) (hm : ∀ i ∈ X, i < m)
    (hXk : X.length = k) : sanitizeK m k X = X := by
  have hf : (X.filter fun i ↦ decide (i < m)) = X :=
    List.filter_eq_self.2 fun a ha ↦ decide_eq_true (hm a ha)
  rw [sanitizeK, hf, hX.dedup, List.take_append, List.take_of_length_le hXk.le, ← hXk,
    Nat.sub_self, List.take_zero, List.append_nil]

/-- `sanitizeK` of a list of at most `k` distinct facilities costs at most as much. -/
theorem costF_sanitizeK_le {I : Instance} (hv : I.Valid) {X : List ℕ} (hX : X.Nodup)
    (hm : ∀ i ∈ X, i < I.m) (hXk : X.length ≤ I.k) :
    I.costF (I.centers (sanitizeK I.m I.k X)) ≤ I.costF (I.centers X) :=
  Instance.costF_anti hv (Instance.centers_mono (subset_sanitizeK hX hm hXk))

end BCFGJPSSV26


