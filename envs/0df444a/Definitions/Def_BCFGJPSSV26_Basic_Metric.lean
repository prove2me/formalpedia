-- Prove2me | Definitions.Def_BCFGJPSSV26_Basic_Metric
-- name    : BCFGJPSSV26_Basic_Metric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:04.27303+00:00
-- url     : https://prove2.me/theorems/542ba3b1-2148-49df-adf7-7346eb8286ad
-- title:
--   BCFGJPSSV26.Basic.Metric — The metric of an instance
-- statement:
--   This is module `BCFGJPSSV26.Basic.Metric` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The pure mathematics of an instance `I` that both parts of the paper use, over the reals:
--
--   * **Points and distances** (`BCFGJPSSV26.Instance.Pt`, `BCFGJPSSV26.Instance.dd`): the clients
--     `.inl j` and facilities `.inr i`, with real distances.
--   * **Distance to a set of facilities** (`BCFGJPSSV26.Instance.dSet`): the least distance to one of
--     its facilities. The empty set is at distance `dMax = 1 + ∑ₐ ∑_b d(a, b)`, larger than every
--     distance (`BCFGJPSSV26.Instance.dd_lt_dMax`); it plays the role of the paper's `d(a, ∅) = ∞`, so
--     that `dSet` stays monotone and `d(a, S ∪ T) = min(d(a, S), d(a, T))` holds for all sets
--     (`BCFGJPSSV26.Instance.dSet_union`).
--   * **Costs**: of a set of facilities (`BCFGJPSSV26.Instance.costF`), the same on a set of clients
--     (`BCFGJPSSV26.Instance.costOn`), and of an assignment of clients to facilities
--     (`BCFGJPSSV26.Instance.costMap`). On nonempty sets `costF` is the cost of `Model.lean`
--     (`BCFGJPSSV26.Instance.costF_eq_cost`).
--   * **Optimal sets** (`BCFGJPSSV26.Instance.IsOpt`): for `k ≤ m` some set of exactly `k` facilities
--     costs `opt k` (`BCFGJPSSV26.Instance.exists_isOpt`), and every nonempty set of at most `ℓ`
--     facilities costs at least `opt ℓ` (`BCFGJPSSV26.Instance.opt_le_costF`).
--   * **Nearest centers and clusters** (`BCFGJPSSV26.Instance.near`, `BCFGJPSSV26.Instance.cluster`):
--     the nearest facility of a nonempty set, the one of least index among the nearest ones, and the
--     clients whose nearest facility is a given one. Clusters partition the clients
--     (`BCFGJPSSV26.Instance.sum_clusters`).
--
--   **Contents.** The module is published as a whole: 56 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Basic_Metric`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Basic/Metric.lean

module

public import Definitions.Def_BCFGJPSSV26_Model
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Basic.Metric` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The metric of an instance

The pure mathematics of an instance `I` that both parts of the paper use, over the reals:

* **Points and distances** (`BCFGJPSSV26.Instance.Pt`, `BCFGJPSSV26.Instance.dd`): the clients
  `.inl j` and facilities `.inr i`, with real distances.
* **Distance to a set of facilities** (`BCFGJPSSV26.Instance.dSet`): the least distance to one of
  its facilities. The empty set is at distance `dMax = 1 + ∑ₐ ∑_b d(a, b)`, larger than every
  distance (`BCFGJPSSV26.Instance.dd_lt_dMax`); it plays the role of the paper's `d(a, ∅) = ∞`, so
  that `dSet` stays monotone and `d(a, S ∪ T) = min(d(a, S), d(a, T))` holds for all sets
  (`BCFGJPSSV26.Instance.dSet_union`).
* **Costs**: of a set of facilities (`BCFGJPSSV26.Instance.costF`), the same on a set of clients
  (`BCFGJPSSV26.Instance.costOn`), and of an assignment of clients to facilities
  (`BCFGJPSSV26.Instance.costMap`). On nonempty sets `costF` is the cost of `Model.lean`
  (`BCFGJPSSV26.Instance.costF_eq_cost`).
* **Optimal sets** (`BCFGJPSSV26.Instance.IsOpt`): for `k ≤ m` some set of exactly `k` facilities
  costs `opt k` (`BCFGJPSSV26.Instance.exists_isOpt`), and every nonempty set of at most `ℓ`
  facilities costs at least `opt ℓ` (`BCFGJPSSV26.Instance.opt_le_costF`).
* **Nearest centers and clusters** (`BCFGJPSSV26.Instance.near`, `BCFGJPSSV26.Instance.cluster`):
  the nearest facility of a nonempty set, the one of least index among the nearest ones, and the
  clients whose nearest facility is a given one. Clusters partition the clients
  (`BCFGJPSSV26.Instance.sum_clusters`).
-/

@[expose] public section

namespace BCFGJPSSV26

open Finset

namespace Instance

variable (I : Instance)

/-! ### Points and distances -/

/-- The points of an instance: the clients `.inl j` and the facilities `.inr i`. -/
abbrev Pt : Type := Fin I.n ⊕ Fin I.m

/-- The distance between two points, as a real number. -/
noncomputable def dd (a b : I.Pt) : ℝ := I.d a b

/-- A distance larger than every distance, `1 + ∑ₐ ∑_b d(a, b)`: the distance to the empty set. -/
noncomputable def dMax : ℝ := 1 + ∑ a : I.Pt, ∑ b : I.Pt, I.dd a b

variable {I}

theorem dd_nonneg (hv : I.Valid) (a b : I.Pt) : 0 ≤ I.dd a b := by
  unfold dd
  exact_mod_cast hv.nonneg a b

@[simp] theorem dd_self (hv : I.Valid) (a : I.Pt) : I.dd a a = 0 := by
  unfold dd
  exact_mod_cast hv.self a

theorem dd_comm (hv : I.Valid) (a b : I.Pt) : I.dd a b = I.dd b a := by
  unfold dd
  exact_mod_cast hv.comm a b

theorem dd_triangle (hv : I.Valid) (a b c : I.Pt) : I.dd a c ≤ I.dd a b + I.dd b c := by
  unfold dd
  exact_mod_cast hv.triangle a b c

theorem dd_lt_dMax (hv : I.Valid) (a b : I.Pt) : I.dd a b < I.dMax := by
  have h1 : I.dd a b ≤ ∑ b' : I.Pt, I.dd a b' :=
    single_le_sum (fun b' _ ↦ dd_nonneg hv a b') (mem_univ b)
  have h2 : ∑ b' : I.Pt, I.dd a b' ≤ ∑ a' : I.Pt, ∑ b' : I.Pt, I.dd a' b' :=
    single_le_sum (f := fun a' ↦ ∑ b' : I.Pt, I.dd a' b')
      (fun a' _ ↦ sum_nonneg fun b' _ ↦ dd_nonneg hv a' b') (mem_univ a)
  unfold dMax
  linarith

theorem dMax_pos (hv : I.Valid) : 0 < I.dMax := by
  have : 0 ≤ ∑ a : I.Pt, ∑ b : I.Pt, I.dd a b :=
    sum_nonneg fun a _ ↦ sum_nonneg fun b _ ↦ dd_nonneg hv a b
  unfold dMax
  linarith

/-! ### Distance to a set of facilities -/

variable (I) in
/-- The distance from `a` to the nearest facility of `S`, and `dMax` if `S` is empty. -/
noncomputable def dSet (a : I.Pt) (S : Finset (Fin I.m)) : ℝ :=
  if h : S.Nonempty then S.inf' h fun i ↦ I.dd a (.inr i) else I.dMax

theorem dSet_of_nonempty {S : Finset (Fin I.m)} (h : S.Nonempty) (a : I.Pt) :
    I.dSet a S = S.inf' h fun i ↦ I.dd a (.inr i) := by
  unfold dSet
  rw [dif_pos h]

@[simp] theorem dSet_empty (a : I.Pt) : I.dSet a ∅ = I.dMax := by
  unfold dSet
  simp

theorem dSet_le {S : Finset (Fin I.m)} {i : Fin I.m} (hi : i ∈ S) (a : I.Pt) :
    I.dSet a S ≤ I.dd a (.inr i) := by
  rw [dSet_of_nonempty ⟨i, hi⟩]
  exact inf'_le _ hi

theorem le_dSet {S : Finset (Fin I.m)} (hS : S.Nonempty) {a : I.Pt} {x : ℝ}
    (h : ∀ i ∈ S, x ≤ I.dd a (.inr i)) : x ≤ I.dSet a S := by
  rw [dSet_of_nonempty hS]
  exact le_inf' hS _ h

theorem exists_dSet_eq {S : Finset (Fin I.m)} (hS : S.Nonempty) (a : I.Pt) :
    ∃ i ∈ S, I.dSet a S = I.dd a (.inr i) := by
  rw [dSet_of_nonempty hS]
  exact exists_mem_eq_inf' hS _

theorem dSet_nonneg (hv : I.Valid) (a : I.Pt) (S : Finset (Fin I.m)) : 0 ≤ I.dSet a S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [dSet_empty]
    exact (dMax_pos hv).le
  · exact le_dSet hS fun i _ ↦ dd_nonneg hv a _

theorem dSet_le_dMax (hv : I.Valid) (a : I.Pt) (S : Finset (Fin I.m)) : I.dSet a S ≤ I.dMax := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
  · rw [dSet_empty]
  · exact (dSet_le hi a).trans (dd_lt_dMax hv a _).le

/-- **Monotonicity**: more facilities are nearer. -/
theorem dSet_anti (hv : I.Valid) {S T : Finset (Fin I.m)} (hST : S ⊆ T) (a : I.Pt) :
    I.dSet a T ≤ I.dSet a S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [dSet_empty]
    exact dSet_le_dMax hv a T
  · obtain ⟨i, hi, h⟩ := exists_dSet_eq hS a
    rw [h]
    exact dSet_le (hST hi) a

theorem dSet_union (hv : I.Valid) (a : I.Pt) (S T : Finset (Fin I.m)) :
    I.dSet a (S ∪ T) = min (I.dSet a S) (I.dSet a T) := by
  refine le_antisymm (le_min (dSet_anti hv subset_union_left a)
    (dSet_anti hv subset_union_right a)) ?_
  rcases (S ∪ T).eq_empty_or_nonempty with h | h
  · rw [union_eq_empty] at h
    rw [h.1, h.2, union_empty, dSet_empty, min_self]
  · obtain ⟨i, hi, hd⟩ := exists_dSet_eq h a
    rw [hd]
    rcases mem_union.1 hi with hi | hi
    · exact (min_le_left _ _).trans (dSet_le hi a)
    · exact (min_le_right _ _).trans (dSet_le hi a)

theorem dSet_insert (hv : I.Valid) (a : I.Pt) (S : Finset (Fin I.m)) (i : Fin I.m) :
    I.dSet a (insert i S) = min (I.dSet a S) (I.dd a (.inr i)) := by
  have hi : I.dSet a {i} = I.dd a (.inr i) := by
    rw [dSet_of_nonempty (singleton_nonempty i), inf'_singleton]
  rw [insert_eq, union_comm, dSet_union hv, hi]

theorem dSet_singleton (a : I.Pt) (i : Fin I.m) : I.dSet a {i} = I.dd a (.inr i) := by
  rw [dSet_of_nonempty (singleton_nonempty i), inf'_singleton]

/-- **The triangle inequality** for the distance to a set. -/
theorem dSet_triangle (hv : I.Valid) (a b : I.Pt) (S : Finset (Fin I.m)) :
    I.dSet a S ≤ I.dd a b + I.dSet b S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [dSet_empty]
    linarith [dd_nonneg hv a b]
  · obtain ⟨i, hi, h⟩ := exists_dSet_eq hS b
    rw [h]
    exact (dSet_le hi a).trans (dd_triangle hv a b _)

/-! ### Costs -/

variable (I) in
/-- The **cost** of a set `S` of facilities: `∑_j d(j, S)`. -/
noncomputable def costF (S : Finset (Fin I.m)) : ℝ := ∑ j, I.dSet (.inl j) S

variable (I) in
/-- The cost of the clients of `D` in a set `S` of facilities: `∑_{j ∈ D} d(j, S)`. -/
noncomputable def costOn (S : Finset (Fin I.m)) (D : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ D, I.dSet (.inl j) S

variable (I) in
/-- The cost of the clients of `D` in an assignment `μ`: `∑_{j ∈ D} d(j, μ j)`. -/
noncomputable def costMap (μ : Fin I.n → Fin I.m) (D : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ D, I.dd (.inl j) (.inr (μ j))

theorem costOn_univ (S : Finset (Fin I.m)) : I.costOn S univ = I.costF S := rfl

theorem costF_nonneg (hv : I.Valid) (S : Finset (Fin I.m)) : 0 ≤ I.costF S :=
  sum_nonneg fun _ _ ↦ dSet_nonneg hv _ S

theorem costOn_nonneg (hv : I.Valid) (S : Finset (Fin I.m)) (D : Finset (Fin I.n)) :
    0 ≤ I.costOn S D :=
  sum_nonneg fun _ _ ↦ dSet_nonneg hv _ S

theorem costF_anti (hv : I.Valid) {S T : Finset (Fin I.m)} (hST : S ⊆ T) :
    I.costF T ≤ I.costF S :=
  sum_le_sum fun _ _ ↦ dSet_anti hv hST _

theorem costOn_le_costF (hv : I.Valid) (S : Finset (Fin I.m)) (D : Finset (Fin I.n)) :
    I.costOn S D ≤ I.costF S :=
  sum_le_sum_of_subset_of_nonneg (subset_univ D) fun _ _ _ ↦ dSet_nonneg hv _ S

/-- A client pays at most its distance to the facility it is assigned to. -/
theorem costOn_le_costMap {S : Finset (Fin I.m)} {μ : Fin I.n → Fin I.m} {D : Finset (Fin I.n)}
    (hμ : ∀ j ∈ D, μ j ∈ S) : I.costOn S D ≤ I.costMap μ D :=
  sum_le_sum fun j hj ↦ dSet_le (hμ j hj) _

/-- **The cost of `Model.lean`**, on nonempty sets. -/
theorem costF_eq_cost {S : Finset (Fin I.m)} (hS : S.Nonempty) : I.costF S = I.cost S := by
  unfold costF Instance.cost
  refine sum_congr rfl fun j _ ↦ ?_
  have : Nonempty S := hS.to_subtype
  have hbdd : BddBelow (Set.range fun i : S ↦ I.dist j i) := (Set.finite_range _).bddBelow
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun ⟨i, hi⟩ ↦ ?_
    exact dSet_le hi _
  · obtain ⟨i, hi, h⟩ := exists_dSet_eq hS (.inl j)
    rw [h]
    exact ciInf_le hbdd ⟨i, hi⟩

/-! ### Optimal sets -/

theorem cost_nonneg' (hv : I.Valid) (S : Finset (Fin I.m)) : 0 ≤ I.cost S :=
  sum_nonneg fun _ _ ↦ Real.iInf_nonneg fun _ ↦ by
    unfold Instance.dist
    exact_mod_cast hv.nonneg _ _

theorem opt_nonneg' (hv : I.Valid) (ℓ : ℕ) : 0 ≤ I.opt ℓ :=
  Real.iInf_nonneg fun S ↦ cost_nonneg' hv S.1

/-- Every nonempty set of at most `ℓ` facilities costs at least `opt ℓ`. -/
theorem opt_le_costF {ℓ : ℕ} {T : Finset (Fin I.m)} (hT : T.Nonempty) (hTℓ : T.card ≤ ℓ) :
    I.opt ℓ ≤ I.costF T := by
  rw [costF_eq_cost hT]
  have hbdd : BddBelow (Set.range fun S : {S : Finset (Fin I.m) // S.Nonempty ∧ S.card ≤ ℓ} ↦
      I.cost S.1) := (Set.finite_range _).bddBelow
  exact ciInf_le hbdd ⟨T, hT, hTℓ⟩

variable (I) in
/-- An **optimal set**: exactly `k` facilities, of cost `opt k`. -/
structure IsOpt (O : Finset (Fin I.m)) : Prop where
  card : O.card = I.k
  cost : I.costF O = I.opt I.k

/-- **An optimal set of exactly `k` facilities exists** when `k ≤ m`: the optimum is a minimum
over finitely many sets, and adding facilities to reach `k` does not raise the cost. -/
theorem exists_isOpt (hv : I.Valid) (hk : I.k ≤ I.m) : ∃ O, I.IsOpt O := by
  have hne : Nonempty {S : Finset (Fin I.m) // S.Nonempty ∧ S.card ≤ I.k} :=
    ⟨⟨{⟨0, hv.one_le_m⟩}, by simp, by simpa using hv.one_le_k⟩⟩
  obtain ⟨⟨S, hS, hSk⟩, hmin⟩ := exists_eq_ciInf_of_finite (f := fun S :
    {S : Finset (Fin I.m) // S.Nonempty ∧ S.card ≤ I.k} ↦ I.cost S.1)
  have hcard : I.k ≤ (univ : Finset (Fin I.m)).card := by simpa using hk
  obtain ⟨O, hSO, -, hO⟩ := exists_subsuperset_card_eq (subset_univ S) hSk hcard
  have hOne : O.Nonempty := hS.mono hSO
  refine ⟨O, hO, le_antisymm ?_ (opt_le_costF hOne hO.le)⟩
  calc I.costF O ≤ I.costF S := costF_anti hv hSO
    _ = I.opt I.k := by rw [costF_eq_cost hS]; exact hmin

theorem IsOpt.nonempty (hv : I.Valid) {O : Finset (Fin I.m)} (hO : I.IsOpt O) : O.Nonempty := by
  rw [← card_pos, hO.card]
  exact hv.one_le_k

/-- An optimal set is at least as cheap as every nonempty set of at most `k` facilities. -/
theorem IsOpt.le_costF {O : Finset (Fin I.m)} (hO : I.IsOpt O) {T : Finset (Fin I.m)}
    (hT : T.Nonempty) (hTk : T.card ≤ I.k) : I.costF O ≤ I.costF T :=
  hO.cost ▸ opt_le_costF hT hTk

/-! ### Nearest centers and clusters -/

variable (I) in
open Classical in
/-- The **nearest facility** of a nonempty set `S` to `a`: among the nearest ones, the one of least
index. -/
noncomputable def near (S : Finset (Fin I.m)) (hS : S.Nonempty) (a : I.Pt) : Fin I.m :=
  (S.filter fun i ↦ I.dd a (.inr i) = I.dSet a S).min' (by
    obtain ⟨i, hi, h⟩ := exists_dSet_eq hS a
    exact ⟨i, mem_filter.2 ⟨hi, h.symm⟩⟩)

theorem near_spec {S : Finset (Fin I.m)} (hS : S.Nonempty) (a : I.Pt) :
    I.near S hS a ∈ S ∧ I.dd a (.inr (I.near S hS a)) = I.dSet a S := by
  classical
  have h := min'_mem (S.filter fun i ↦ I.dd a (.inr i) = I.dSet a S) (by
    obtain ⟨i, hi, h⟩ := exists_dSet_eq hS a
    exact ⟨i, mem_filter.2 ⟨hi, h.symm⟩⟩)
  unfold near
  convert mem_filter.1 h using 2

theorem near_mem {S : Finset (Fin I.m)} (hS : S.Nonempty) (a : I.Pt) : I.near S hS a ∈ S :=
  (near_spec hS a).1

theorem dd_near {S : Finset (Fin I.m)} (hS : S.Nonempty) (a : I.Pt) :
    I.dd a (.inr (I.near S hS a)) = I.dSet a S :=
  (near_spec hS a).2

/-- The tie-break: the nearest facility has the least index among the nearest ones. -/
theorem near_le {S : Finset (Fin I.m)} (hS : S.Nonempty) {a : I.Pt} {i : Fin I.m} (hi : i ∈ S)
    (h : I.dd a (.inr i) = I.dSet a S) : I.near S hS a ≤ i := by
  classical
  unfold near
  convert min'_le (S.filter fun i ↦ I.dd a (.inr i) = I.dSet a S) i (mem_filter.2 ⟨hi, h⟩)

/-- A facility strictly nearer than all others is the nearest one, whatever the tie-break. -/
theorem near_eq_of_lt {S : Finset (Fin I.m)} (hS : S.Nonempty) {a : I.Pt} {i : Fin I.m}
    (hi : i ∈ S) (h : ∀ i' ∈ S, i' ≠ i → I.dd a (.inr i) < I.dd a (.inr i')) :
    I.near S hS a = i := by
  by_contra hne
  have h1 := h _ (near_mem hS a) hne
  rw [dd_near] at h1
  exact absurd (dSet_le hi a) (not_le.2 h1)

variable (I) in
/-- The **cluster** of `c` in `S`: the clients whose nearest facility of `S` is `c` (empty if `S`
is). -/
noncomputable def cluster (S : Finset (Fin I.m)) (c : Fin I.m) : Finset (Fin I.n) :=
  if hS : S.Nonempty then univ.filter fun j ↦ I.near S hS (.inl j) = c else ∅

theorem mem_cluster {S : Finset (Fin I.m)} (hS : S.Nonempty) {c : Fin I.m} {j : Fin I.n} :
    j ∈ I.cluster S c ↔ I.near S hS (.inl j) = c := by
  unfold cluster
  rw [dif_pos hS]
  simp

theorem cluster_empty (c : Fin I.m) : I.cluster ∅ c = ∅ := by
  unfold cluster
  simp

theorem cluster_eq_empty_of_notMem {S : Finset (Fin I.m)} {c : Fin I.m} (hc : c ∉ S) :
    I.cluster S c = ∅ := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · exact cluster_empty c
  · refine eq_empty_of_forall_notMem fun j hj ↦ hc ?_
    rw [← (mem_cluster hS).1 hj]
    exact near_mem hS _

theorem disjoint_cluster (S : Finset (Fin I.m)) {c c' : Fin I.m} (h : c ≠ c') :
    Disjoint (I.cluster S c) (I.cluster S c') := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [cluster_empty]
  · refine disjoint_left.2 fun j hj hj' ↦ h ?_
    rw [← (mem_cluster hS).1 hj, (mem_cluster hS).1 hj']

theorem mem_cluster_near {S : Finset (Fin I.m)} (hS : S.Nonempty) (j : Fin I.n) :
    j ∈ I.cluster S (I.near S hS (.inl j)) :=
  (mem_cluster hS).2 rfl

theorem dSet_of_mem_cluster {S : Finset (Fin I.m)} {c : Fin I.m} {j : Fin I.n}
    (hj : j ∈ I.cluster S c) : I.dSet (.inl j) S = I.dd (.inl j) (.inr c) := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [cluster_empty] at hj
  · rw [← (mem_cluster hS).1 hj, dd_near]

/-- **Clusters partition the clients.** -/
theorem sum_clusters {M : Type*} [AddCommMonoid M] {S : Finset (Fin I.m)} (hS : S.Nonempty)
    (F : Fin I.n → M) : ∑ j, F j = ∑ c ∈ S, ∑ j ∈ I.cluster S c, F j := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := S) (g := fun j ↦ I.near S hS (.inl j))
    (fun j _ ↦ near_mem hS _)]
  refine sum_congr rfl fun c _ ↦ sum_congr ?_ fun _ _ ↦ rfl
  ext j
  simp [mem_cluster hS]

/-- The same, on a set of clients. -/
theorem sum_clusters_on {M : Type*} [AddCommMonoid M] {S : Finset (Fin I.m)} (hS : S.Nonempty)
    (D : Finset (Fin I.n)) (F : Fin I.n → M) :
    ∑ j ∈ D, F j = ∑ c ∈ S, ∑ j ∈ I.cluster S c ∩ D, F j := by
  classical
  have h := sum_clusters hS fun j ↦ if j ∈ D then F j else 0
  rw [← sum_filter, filter_mem_eq_inter, univ_inter] at h
  rw [h]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [← sum_filter]
  congr 1

theorem costF_eq_sum_clusters {S : Finset (Fin I.m)} (hS : S.Nonempty) :
    I.costF S = ∑ c ∈ S, ∑ j ∈ I.cluster S c, I.dd (.inl j) (.inr c) := by
  unfold costF
  rw [sum_clusters hS]
  exact sum_congr rfl fun c _ ↦ sum_congr rfl fun j hj ↦ dSet_of_mem_cluster hj

/-- The total size of the clusters is the number of clients. -/
theorem sum_card_cluster {S : Finset (Fin I.m)} (hS : S.Nonempty) :
    ∑ c ∈ S, (I.cluster S c).card = I.n := by
  have h := sum_clusters hS (fun _ ↦ (1 : ℕ))
  simp only [sum_const, smul_eq_mul, mul_one, card_univ, Fintype.card_fin] at h
  exact h.symm

end Instance

end BCFGJPSSV26


