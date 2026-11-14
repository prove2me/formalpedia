-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod
-- name    : BCFGJPSSV26_Stable_Alg_Submod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:11:17.053484+00:00
-- url     : https://prove2.me/theorems/df331839-fd42-4f1b-a055-280af587b6e6
-- title:
--   BCFGJPSSV26.Stable.Alg.Submod — The submodular step, exactly
-- statement:
--   This is module `BCFGJPSSV26.Stable.Alg.Submod` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The algorithm of [BCFGJPSSV26b, Section 5] for one guess `p'`, over the exact
--   table (`BCFGJPSSV26.Stable.candidate`):
--
--   1. `ρ = |Λ| + p'`, `z = |LS'| + ρ - k`; skip the guess if `ρ > s`, `z > |red|` or a ball is
--      empty.
--   2. `g = g₁ + g₂` exactly (`BCFGJPSSV26.Raw.gQ`, the sum of the `z` smallest values by sorting).
--   3. The parts: the balls of the dummies and `p'` copies of all facilities.
--   4. The sequential greedy with `N` rounds (`BCFGJPSSV26.Stable.seqGreedyQ`, the rule of
--      `BCFGJPSSV26.Stable.IsSeqGreedy`), all sums over `[N]^ρ` by the tuples of
--      `Tuples.tuples` cut at the budget `B` (complete when `N^ρ ≤ B`); `Ŷ` is the choice of one
--      element per list minimizing `g`.
--   5. `Ẑ`: the `z` red centers of least `h_c(Ŷ)`; the candidate is `(LS' \ Ẑ) ∪ Ŷ`.
--
--   **Specification** (`BCFGJPSSV26.Stable.candidate_spec`): a computed candidate is a list of at
--   most `k` distinct facilities of the form `(LS' \ Ẑ) ∪ Ŷ` with `Ŷ` meeting every ball, `Ẑ`
--   attaining `g₂(Ŷ)`, and the greedy guarantee `BCFGJPSSV26.Stable.GreedyGuarantee` (from
--   `BCFGJPSSV26.Stable.seqGreedy_bound`, `BCFGJPSSV26.Stable.gfun_isMonoF`,
--   `BCFGJPSSV26.Stable.gfun_isSubmod`, and the exact values of `g`). The guess is not skipped when
--   its conditions hold (`BCFGJPSSV26.Stable.candidate_isSome`).
--
--   **Contents.** The module is published as a whole: 67 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.candidate_spec` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Alg_Submod`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Alg/Submod.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Mixed
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_Coloring
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BuhaiPapers_Background_Tuples

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Alg.Submod` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The submodular step, exactly

The algorithm of [BCFGJPSSV26b, Section 5] for one guess `p'`, over the exact
table (`BCFGJPSSV26.Stable.candidate`):

1. `ρ = |Λ| + p'`, `z = |LS'| + ρ - k`; skip the guess if `ρ > s`, `z > |red|` or a ball is
   empty.
2. `g = g₁ + g₂` exactly (`BCFGJPSSV26.Raw.gQ`, the sum of the `z` smallest values by sorting).
3. The parts: the balls of the dummies and `p'` copies of all facilities.
4. The sequential greedy with `N` rounds (`BCFGJPSSV26.Stable.seqGreedyQ`, the rule of
   `BCFGJPSSV26.Stable.IsSeqGreedy`), all sums over `[N]^ρ` by the tuples of
   `Tuples.tuples` cut at the budget `B` (complete when `N^ρ ≤ B`); `Ŷ` is the choice of one
   element per list minimizing `g`.
5. `Ẑ`: the `z` red centers of least `h_c(Ŷ)`; the candidate is `(LS' \ Ẑ) ∪ Ŷ`.

**Specification** (`BCFGJPSSV26.Stable.candidate_spec`): a computed candidate is a list of at
most `k` distinct facilities of the form `(LS' \ Ẑ) ∪ Ŷ` with `Ŷ` meeting every ball, `Ẑ`
attaining `g₂(Ŷ)`, and the greedy guarantee `BCFGJPSSV26.Stable.GreedyGuarantee` (from
`BCFGJPSSV26.Stable.seqGreedy_bound`, `BCFGJPSSV26.Stable.gfun_isMonoF`,
`BCFGJPSSV26.Stable.gfun_isSubmod`, and the exact values of `g`). The guess is not skipped when
its conditions hold (`BCFGJPSSV26.Stable.candidate_isSome`).
-/

@[expose] public section

namespace BCFGJPSSV26

namespace Raw

open Stable

/-- `g₁` exactly. -/
def g₁Q (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (Y : List ℕ) : ℚ :=
  ((List.range x.n).map fun j ↦ min (x.dMixQ j LS' Λ) (x.dSetQ j Y)).sum

/-- `h_c` exactly. -/
def hclQ (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (blue : List ℕ) (c : ℕ) (Y : List ℕ) : ℚ :=
  x.costMixOnQ LS' Λ (x.clusterMixQ LS' Λ c) +
    (x.clusterMixQ LS' Λ c).length * x.dMixQ (x.n + c) (blue ++ Y) Λ

/-- The sum of the `z` smallest entries of a list. -/
def sumSmallestQ (z : ℕ) (l : List ℚ) : ℚ := ((l.mergeSort fun a a' ↦ decide (a ≤ a')).take z).sum

/-- `g₂` exactly. -/
def g₂Q (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (red blue : List ℕ) (z : ℕ) (Y : List ℕ) : ℚ :=
  sumSmallestQ z (red.map fun c ↦ x.hclQ LS' Λ blue c Y)

/-- `g = g₁ + g₂` exactly. -/
def gQ (x : Raw) (LS' : List ℕ) (Λ : List DumQ) (red blue : List ℕ) (z : ℕ) (Y : List ℕ) : ℚ :=
  x.g₁Q LS' Λ Y + x.g₂Q LS' Λ red blue z Y

end Raw

namespace Stable

/-- The first maximizer of `f` in `l`, `d` if `l` is empty. -/
def argmaxBy {α : Type} (f : α → ℚ) (l : List α) (d : α) : α :=
  (l.find? fun a ↦ l.all fun a' ↦ decide (f a' ≤ f a)).getD d

/-- The first minimizer of `f` in `l`, `d` if `l` is empty. -/
def argminBy {α : Type} (f : α → ℚ) (l : List α) (d : α) : α :=
  (l.find? fun a ↦ l.all fun a' ↦ decide (f a ≤ f a')).getD d

/-- `Q⁻ʲ_t(V)` for the lists `Lst` of the greedy. -/
def greedyQL (Lst : List (List ℕ)) (j t : ℕ) (V : List ℕ) : List ℕ :=
  (List.range Lst.length).filterMap fun j' ↦
    if (j' < j ∧ V.getD j' 0 ≤ t) ∨ (j < j' ∧ V.getD j' 0 < t) then
      some ((Lst.getD j' []).getD (V.getD j' 0) 0)
    else none

/-- The total gain of `f = g(∅) - g` from adding `e` to `Q⁻ʲ_t(V)`, over the tuples `Vs`. -/
def gainQ (g : List ℕ → ℚ) (Lst : List (List ℕ)) (j t : ℕ) (Vs : List (List ℕ)) (e : ℕ) : ℚ :=
  (Vs.map fun V ↦ g (greedyQL Lst j t V) - g (e :: greedyQL Lst j t V)).sum

/-- Round `t` of the greedy: each part in turn appends its best element. -/
def greedyRound (g : List ℕ → ℚ) (parts : List (List ℕ)) (Vs : List (List ℕ)) (t : ℕ)
    (Lst : List (List ℕ)) : List (List ℕ) :=
  (List.range parts.length).foldl (fun Lst j ↦
    Lst.set j (Lst.getD j [] ++ [argmaxBy (gainQ g Lst j t Vs) (parts.getD j []) 0])) Lst

/-- The choice `{L_j[V_j]}` of one element per list. -/
def pickQ (Lst : List (List ℕ)) (V : List ℕ) : List ℕ :=
  (List.range Lst.length).map fun j ↦ (Lst.getD j []).getD (V.getD j 0) 0

/-- **The sequential greedy** with `T` rounds, tuples cut at `B`. -/
def seqGreedyQ (g : List ℕ → ℚ) (parts : List (List ℕ)) (T B : ℕ) : List ℕ :=
  let Vs := Tuples.tuples B T parts.length
  let Lst := (List.range T).foldl (fun Lst t ↦ greedyRound g parts Vs t Lst)
    (List.replicate parts.length [])
  pickQ Lst (argminBy (fun V ↦ g (pickQ Lst V)) Vs [])

/-- **The candidate of the guess `p'`**, or `none` if the guess is skipped. -/
def candidate (N : ℕ) (x : Raw) (s B : ℕ) (LS' : List ℕ) (Λ : List DumQ) (col : List Bool)
    (p' : ℕ) : Option (List ℕ) :=
  let ρ := Λ.length + p'
  let red := redOf LS' col
  let blue := blueOf LS' col
  let z := (LS'.length + ρ) - x.k
  if s < ρ ∨ red.length < z ∨ Λ.any (fun l ↦ (x.ballQ l).isEmpty) then none
  else
    let g := x.gQ LS' Λ red blue z
    let Y := seqGreedyQ g (Λ.map x.ballQ ++ List.replicate p' (List.range x.m)) N B
    let Zh := (red.mergeSort fun c c' ↦
      decide (x.hclQ LS' Λ blue c Y ≤ x.hclQ LS' Λ blue c' Y)).take z
    some ((LS'.filter fun c ↦ decide (c ∉ Zh)) ++ Y).dedup

section Helpers

open Finset

/-! ### First maximizers and minimizers -/

private theorem argmaxBy_spec {α : Type} (f : α → ℚ) {l : List α} (hl : l ≠ []) (d : α) :
    argmaxBy f l d ∈ l ∧ ∀ a ∈ l, f a ≤ f (argmaxBy f l d) := by
  classical
  obtain ⟨a₀, ha₀, hmax⟩ := Finset.exists_max_image l.toFinset f
    ((List.toFinset_nonempty_iff l).2 hl)
  have hsome : (l.find? fun a ↦ l.all fun a' ↦ decide (f a' ≤ f a)).isSome := by
    rw [List.find?_isSome]
    refine ⟨a₀, List.mem_toFinset.1 ha₀, ?_⟩
    rw [List.all_eq_true]
    exact fun b hb ↦ decide_eq_true (hmax b (List.mem_toFinset.2 hb))
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hsome
  have hp := List.find?_some ha
  rw [List.all_eq_true] at hp
  unfold argmaxBy
  rw [ha, Option.getD_some]
  exact ⟨List.mem_of_find?_eq_some ha, fun b hb ↦ of_decide_eq_true (hp b hb)⟩

private theorem argminBy_spec {α : Type} (f : α → ℚ) {l : List α} (hl : l ≠ []) (d : α) :
    argminBy f l d ∈ l ∧ ∀ a ∈ l, f (argminBy f l d) ≤ f a := by
  obtain ⟨a, ha, hmem, hmin⟩ := Combine.find?_min f hl
  unfold argminBy
  rw [ha, Option.getD_some]
  exact ⟨hmem, hmin⟩

/-! ### Lists -/

private theorem getD_set_self' {α : Type*} {L : List α} {j : ℕ} (hj : j < L.length) (v d : α) :
    (L.set j v).getD j d = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hj, Option.getD_some]

private theorem getD_set_ne' {α : Type*} (L : List α) {j j' : ℕ} (h : j ≠ j') (v d : α) :
    (L.set j v).getD j' d = L.getD j' d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, ← List.getD_eq_getElem?_getD]

private theorem getD_of_prefix {α : Type*} {l₁ l₂ : List α} (h : l₁ <+: l₂) {i : ℕ}
    (hi : i < l₁.length) (d : α) : l₂.getD i d = l₁.getD i d := by
  obtain ⟨u, rfl⟩ := h
  exact List.getD_append _ _ _ _ hi

private theorem getD_lt_of {l : List ℕ} {m : ℕ} (hl : ∀ a ∈ l, a < m) (hm : 0 < m) (i : ℕ) :
    l.getD i 0 < m := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hl _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact hm

private theorem getD_ofFn_val {ρ T : ℕ} (v : Fin ρ → Fin T) {a : ℕ} (ha : a < ρ) :
    (List.ofFn fun j ↦ (v j : ℕ)).getD a 0 = v ⟨a, ha⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using ha), List.getElem_ofFn]

/-! ### The greedy lists -/

section Greedy

variable (g : List ℕ → ℚ) (parts : List (List ℕ)) (Vs : List (List ℕ))

/-- One step of a round of the greedy: part `j` appends its best element. -/
private def greedyStep (t : ℕ) (Lst : List (List ℕ)) (j : ℕ) : List (List ℕ) :=
  Lst.set j (Lst.getD j [] ++ [argmaxBy (gainQ g Lst j t Vs) (parts.getD j []) 0])

/-- The lists before round `t`. -/
private def greedyR (t : ℕ) : List (List ℕ) :=
  (List.range t).foldl (fun Lst t ↦ greedyRound g parts Vs t Lst)
    (List.replicate parts.length [])

/-- The lists in round `t`, before part `j`. -/
private def greedyS (t j : ℕ) : List (List ℕ) :=
  (List.range j).foldl (greedyStep g parts Vs t) (greedyR g parts Vs t)

private theorem greedyS_zero (t : ℕ) : greedyS g parts Vs t 0 = greedyR g parts Vs t := rfl

private theorem greedyS_succ (t j : ℕ) :
    greedyS g parts Vs t (j + 1) = greedyStep g parts Vs t (greedyS g parts Vs t j) j := by
  rw [greedyS, List.range_succ, List.foldl_append]
  rfl

private theorem greedyR_succ (t : ℕ) :
    greedyR g parts Vs (t + 1) = greedyS g parts Vs t parts.length := by
  rw [greedyR, List.range_succ, List.foldl_append]
  rfl

private theorem length_greedyS_of (t : ℕ) (h : (greedyR g parts Vs t).length = parts.length)
    (j : ℕ) :
    (greedyS g parts Vs t j).length = parts.length := by
  induction j with
  | zero => exact h
  | succ j ih => rw [greedyS_succ, greedyStep, List.length_set, ih]

private theorem length_greedyR (t : ℕ) : (greedyR g parts Vs t).length = parts.length := by
  induction t with
  | zero => simp [greedyR]
  | succ t ih => rw [greedyR_succ]; exact length_greedyS_of g parts Vs t ih _

private theorem length_greedyS (t j : ℕ) : (greedyS g parts Vs t j).length = parts.length :=
  length_greedyS_of g parts Vs t (length_greedyR g parts Vs t) j

private theorem length_getD_greedyS (t : ℕ)
    (hR : ∀ j' < parts.length, ((greedyR g parts Vs t).getD j' []).length = t) :
    ∀ j ≤ parts.length, ∀ j' < parts.length,
      ((greedyS g parts Vs t j).getD j' []).length = if j' < j then t + 1 else t := by
  intro j
  induction j with
  | zero =>
    intro _ j' hj'
    rw [greedyS_zero, hR j' hj', if_neg (by omega)]
  | succ j ih =>
    intro hj j' hj'
    rw [greedyS_succ, greedyStep]
    by_cases hjj : j = j'
    · subst hjj
      rw [getD_set_self' (by rw [length_greedyS]; omega), List.length_append,
        ih (by omega) j hj', if_neg (lt_irrefl j), if_pos (by omega)]
      rfl
    · rw [getD_set_ne' _ hjj, ih (by omega) j' hj']
      by_cases h1 : j' < j
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

private theorem length_getD_greedyR (t : ℕ) :
    ∀ j' < parts.length, ((greedyR g parts Vs t).getD j' []).length = t := by
  induction t with
  | zero =>
    intro j' hj'
    simp [greedyR, List.getD_eq_getElem?_getD]
  | succ t ih =>
    intro j' hj'
    rw [greedyR_succ, length_getD_greedyS g parts Vs t ih _ le_rfl j' hj', if_pos hj']

/-- `A` extends to `B`, list by list. -/
private def ListsPrefix (A B : List (List ℕ)) : Prop := ∀ j, A.getD j [] <+: B.getD j []

private theorem prefix_greedyStep (t : ℕ) (Lst : List (List ℕ)) (j : ℕ) :
    ListsPrefix Lst (greedyStep g parts Vs t Lst j) := by
  intro j'
  unfold greedyStep
  by_cases hjj : j = j'
  · subst hjj
    by_cases hj : j < Lst.length
    · rw [getD_set_self' hj]
      exact List.prefix_append _ _
    · rw [List.set_eq_of_length_le (by omega)]
  · rw [getD_set_ne' _ hjj]

private theorem greedyS_mono (t : ℕ) {j j' : ℕ} (h : j ≤ j') :
    ListsPrefix (greedyS g parts Vs t j) (greedyS g parts Vs t j') := by
  induction j', h using Nat.le_induction with
  | base => exact fun _ ↦ List.prefix_refl _
  | succ j' _ ih =>
    rw [greedyS_succ]
    exact fun i ↦ (ih i).trans (prefix_greedyStep g parts Vs t _ j' i)

private theorem greedyR_mono {t t' : ℕ} (h : t ≤ t') :
    ListsPrefix (greedyR g parts Vs t) (greedyR g parts Vs t') := by
  induction t', h using Nat.le_induction with
  | base => exact fun _ ↦ List.prefix_refl _
  | succ t' _ ih =>
    rw [greedyR_succ, ← greedyS_zero]
    exact fun i ↦ (ih i).trans (greedyS_mono g parts Vs t' (Nat.zero_le _) i)

private theorem greedyS_prefix_R {T t j : ℕ} (ht : t < T) (hj : j ≤ parts.length) :
    ListsPrefix (greedyS g parts Vs t j) (greedyR g parts Vs T) := by
  intro i
  refine (greedyS_mono g parts Vs t hj i).trans ?_
  rw [← greedyR_succ]
  exact greedyR_mono g parts Vs ht i

private theorem greedyR_entry {T t j : ℕ} (ht : t < T) (hj : j < parts.length) :
    ((greedyR g parts Vs T).getD j []).getD t 0 =
      argmaxBy (gainQ g (greedyS g parts Vs t j) j t Vs) (parts.getD j []) 0 := by
  have hlen := length_getD_greedyS g parts Vs t (length_getD_greedyR g parts Vs t) j hj.le j hj
  rw [if_neg (lt_irrefl j)] at hlen
  have hpre := greedyS_prefix_R g parts Vs ht (Nat.succ_le_of_lt hj) j
  rw [greedyS_succ, greedyStep, getD_set_self' (by rw [length_greedyS]; exact hj)] at hpre
  rw [getD_of_prefix hpre (by rw [List.length_append, hlen]; simp) 0,
    List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
  rfl

private theorem greedyQL_greedyS {T t j : ℕ} (ht : t < T) (hj : j < parts.length) (V : List ℕ) :
    greedyQL (greedyS g parts Vs t j) j t V = greedyQL (greedyR g parts Vs T) j t V := by
  unfold greedyQL
  rw [length_greedyS, length_greedyR]
  refine List.filterMap_congr fun j' hj' ↦ ?_
  have hj'ρ := List.mem_range.1 hj'
  have hpre := greedyS_prefix_R g parts Vs ht hj.le j'
  have hlen := length_getD_greedyS g parts Vs t (length_getD_greedyR g parts Vs t) j hj.le j'
    hj'ρ
  by_cases hc : (j' < j ∧ V.getD j' 0 ≤ t) ∨ (j < j' ∧ V.getD j' 0 < t)
  · rw [if_pos hc, if_pos hc]
    congr 1
    refine (getD_of_prefix hpre ?_ 0).symm
    rw [hlen]
    rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos h1]
      omega
    · rw [if_neg (by omega)]
      omega
  · rw [if_neg hc, if_neg hc]

private theorem gainQ_greedyS {T t j : ℕ} (ht : t < T) (hj : j < parts.length) :
    gainQ g (greedyS g parts Vs t j) j t Vs = gainQ g (greedyR g parts Vs T) j t Vs := by
  funext e
  unfold gainQ
  simp only [greedyQL_greedyS g parts Vs ht hj]

/-- **The greedy lists**: `N` entries per part, each a first maximizer of the total gain over the
part, on the final lists. -/
private theorem greedyR_spec (hp : ∀ j < parts.length, parts.getD j [] ≠ []) (T : ℕ) :
    (greedyR g parts Vs T).length = parts.length ∧
    (∀ j < parts.length, ((greedyR g parts Vs T).getD j []).length = T) ∧
    ∀ j < parts.length, ∀ t < T,
      ((greedyR g parts Vs T).getD j []).getD t 0 ∈ parts.getD j [] ∧
      ∀ e ∈ parts.getD j [], gainQ g (greedyR g parts Vs T) j t Vs e ≤
        gainQ g (greedyR g parts Vs T) j t Vs (((greedyR g parts Vs T).getD j []).getD t 0) := by
  refine ⟨length_greedyR g parts Vs T, length_getD_greedyR g parts Vs T, fun j hj t ht ↦ ?_⟩
  rw [greedyR_entry g parts Vs ht hj, gainQ_greedyS g parts Vs ht hj]
  exact argmaxBy_spec _ (hp j hj) 0

end Greedy

/-! ### Tuples -/

private theorem nodup_iterate_tupleStepFull (n : ℕ) : ∀ i, ((Tuples.tupleStepFull n)^[i] [[]]).Nodup
  | 0 => List.nodup_singleton _
  | i + 1 => by
    rw [Function.iterate_succ_apply', Tuples.tupleStepFull, List.nodup_flatMap]
    refine ⟨fun q _ ↦ List.Nodup.map (fun a b h ↦ (List.cons.inj h).1) List.nodup_range, ?_⟩
    refine (nodup_iterate_tupleStepFull n i).imp fun {q q'} hne ↦ ?_
    intro r hr hr'
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hr
    obtain ⟨b, -, hb⟩ := List.mem_map.1 hr'
    exact hne (List.cons.inj hb).2.symm

/-- **Sums over all the tuples** are sums over the functions `Fin ρ → Fin T`. -/
private theorem sum_tuples {M : Type*} [AddCommMonoid M] {B T ρ : ℕ} (h : T ^ ρ ≤ B)
    (F : List ℕ → M) :
    ((Tuples.tuples B T ρ).map F).sum = ∑ v : Fin ρ → Fin T, F (List.ofFn fun j ↦ (v j : ℕ)) := by
  classical
  have hnd : (Tuples.tuples B T ρ).Nodup := by
    rw [Tuples.tuples_eq h]
    exact nodup_iterate_tupleStepFull T ρ
  rw [← List.sum_toFinset F hnd]
  have hinj : Function.Injective fun v : Fin ρ → Fin T ↦ List.ofFn fun j ↦ (v j : ℕ) := by
    intro v w hvw
    have := List.ofFn_inj.1 hvw
    funext j
    exact Fin.ext (congrFun this j)
  have himg : (Tuples.tuples B T ρ).toFinset =
      univ.image fun v : Fin ρ → Fin T ↦ List.ofFn fun j ↦ (v j : ℕ) := by
    ext q
    rw [List.mem_toFinset, Tuples.mem_tuples h, Finset.mem_image]
    constructor
    · rintro ⟨hlen, hq⟩
      subst hlen
      exact ⟨fun j ↦ ⟨q[j.1], hq _ (List.getElem_mem _)⟩, mem_univ _, List.ofFn_getElem⟩
    · rintro ⟨v, -, rfl⟩
      refine ⟨by simp, fun x hx ↦ ?_⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact (v j).2
  rw [himg, Finset.sum_image fun v _ w _ h ↦ hinj h]

/-! ### From lists to sets of facilities -/

private theorem centers_cons {I : Instance} {a : ℕ} (ha : a < I.m) (l : List ℕ) :
    I.centers (a :: l) = insert ⟨a, ha⟩ (I.centers l) := by
  ext i
  simp only [Instance.mem_centers, List.mem_cons, mem_insert, Fin.ext_iff]

private theorem centers_greedyQL {I : Instance} {ρ T : ℕ} {L : List (List ℕ)} (hL : L.length = ρ)
    (Lst' : Fin ρ → Fin T → Fin I.m)
    (hLst' : ∀ j t, ((Lst' j t : Fin I.m) : ℕ) = (L.getD j []).getD t 0)
    (j : Fin ρ) (t : Fin T) (v : Fin ρ → Fin T) :
    I.centers (greedyQL L j t (List.ofFn fun j ↦ (v j : ℕ))) = greedyQ Lst' j t v := by
  ext i
  simp only [Instance.mem_centers, greedyQL, List.mem_filterMap, List.mem_range, greedyQ,
    mem_image, mem_union, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hai⟩
    rw [hL] at ha
    rw [getD_ofFn_val v ha] at hai
    by_cases hc : (a < j ∧ (v ⟨a, ha⟩ : ℕ) ≤ t) ∨ (j < a ∧ (v ⟨a, ha⟩ : ℕ) < t)
    · rw [if_pos hc] at hai
      refine ⟨⟨a, ha⟩, ?_, Fin.ext ?_⟩
      · simpa only [Fin.lt_def, Fin.le_def] using hc
      · rw [hLst']
        exact Option.some.inj hai
    · rw [if_neg hc] at hai
      exact absurd hai (by simp)
  · rintro ⟨j', hc, rfl⟩
    refine ⟨j'.1, hL ▸ j'.2, ?_⟩
    have hc' : (j'.1 < j ∧ (v j' : ℕ) ≤ t) ∨ (j < j'.1 ∧ (v j' : ℕ) < t) := by
      simpa only [Fin.lt_def, Fin.le_def] using hc
    rw [getD_ofFn_val v j'.2, if_pos hc', hLst']

private theorem centers_pickQ {I : Instance} {ρ T : ℕ} {L : List (List ℕ)} (hL : L.length = ρ)
    (Lst' : Fin ρ → Fin T → Fin I.m)
    (hLst' : ∀ j t, ((Lst' j t : Fin I.m) : ℕ) = (L.getD j []).getD t 0)
    (v : Fin ρ → Fin T) :
    I.centers (pickQ L (List.ofFn fun j ↦ (v j : ℕ))) = univ.image fun j ↦ Lst' j (v j) := by
  ext i
  simp only [Instance.mem_centers, pickQ, List.mem_map, List.mem_range, mem_image, mem_univ,
    true_and]
  constructor
  · rintro ⟨a, ha, hai⟩
    rw [hL] at ha
    refine ⟨⟨a, ha⟩, Fin.ext ?_⟩
    rw [hLst', ← hai, getD_ofFn_val v ha]
  · rintro ⟨j, rfl⟩
    exact ⟨j.1, hL ▸ j.2, by rw [hLst', getD_ofFn_val v j.2]⟩

private theorem greedyQL_lt {L : List (List ℕ)} {m : ℕ} (hLm : ∀ j', ∀ a ∈ L.getD j' [], a < m)
    (hm : 0 < m) (j t : ℕ) (V : List ℕ) : ∀ i ∈ greedyQL L j t V, i < m := by
  intro i hi
  simp only [greedyQL, List.mem_filterMap] at hi
  obtain ⟨a, -, ha⟩ := hi
  by_cases h : (a < j ∧ V.getD a 0 ≤ t) ∨ (j < a ∧ V.getD a 0 < t)
  · rw [if_pos h] at ha
    rw [← Option.some.inj ha]
    exact getD_lt_of (hLm a) hm _
  · rw [if_neg h] at ha
    exact absurd ha (by simp)

private theorem pickQ_lt {L : List (List ℕ)} {m : ℕ} (hLm : ∀ j', ∀ a ∈ L.getD j' [], a < m)
    (hm : 0 < m) (V : List ℕ) : ∀ i ∈ pickQ L V, i < m := by
  intro i hi
  simp only [pickQ, List.mem_map, List.mem_range] at hi
  obtain ⟨a, -, rfl⟩ := hi
  exact getD_lt_of (hLm a) hm _

/-! ### The sequential greedy, exactly -/

/-! ### The exact submodular function -/

private theorem map_val_filter_mem {n : ℕ} {D : List ℕ} (hn : ∀ j ∈ D, j < n) :
    ((univ : Finset (Fin n)).filter fun j ↦ j.1 ∈ D).map Fin.valEmbedding = D.toFinset := by
  ext j
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, List.mem_toFinset]
  exact ⟨fun ⟨a, ha, h⟩ ↦ h ▸ ha, fun h ↦ ⟨⟨j, hn j h⟩, h, rfl⟩⟩

private theorem sum_map_eq_sum_filter {n : ℕ} {D : List ℕ} (hD : D.Nodup) (hn : ∀ j ∈ D, j < n)
    (F : ℕ → ℝ) :
    (D.map F).sum = ∑ j ∈ (univ : Finset (Fin n)).filter (fun j ↦ j.1 ∈ D), F j := by
  classical
  rw [← List.sum_toFinset _ hD, ← map_val_filter_mem hn, Finset.sum_map]
  rfl

private theorem card_filter_mem {n : ℕ} {D : List ℕ} (hD : D.Nodup) (hn : ∀ j ∈ D, j < n) :
    ((univ : Finset (Fin n)).filter fun j ↦ j.1 ∈ D).card = D.length := by
  rw [← card_map Fin.valEmbedding, map_val_filter_mem hn, List.toFinset_card_of_nodup hD]

private theorem g₁Q_toRaw {I : Instance} {LS' : List ℕ} (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) {Y : List ℕ} (hY : ∀ i ∈ Y, i < I.m) :
    ((toRaw I).g₁Q LS' Λ Y : ℝ) = g₁ I (I.centers LS') (toDums I Λ) (I.centers Y) := by
  unfold Raw.g₁Q g₁
  rw [Rat.cast_list_sum, List.map_map, Raw.n_toRaw,
    sum_map_eq_sum_filter List.nodup_range (fun j hj ↦ List.mem_range.1 hj)]
  have : ((univ : Finset (Fin I.n)).filter fun j ↦ j.1 ∈ List.range I.n) = univ := by
    ext j
    simp
  rw [this]
  refine sum_congr rfl fun j _ ↦ ?_
  have h1 := Raw.dMixQ_toRaw hm hΛ (.inl j)
  have h2 := Raw.dSetQ_toRaw (.inl j) hY
  rw [Instance.ptIdx_inl] at h1 h2
  simp only [Function.comp_apply, Rat.cast_min, h1, h2]

private theorem hclQ_toRaw {I : Instance} {LS' : List ℕ} (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) {blue : List ℕ} (hb : ∀ i ∈ blue, i < I.m) {Y : List ℕ}
    (hY : ∀ i ∈ Y, i < I.m) {c : Fin I.m} (hc : c.1 ∈ LS') :
    ((toRaw I).hclQ LS' Λ blue c Y : ℝ) =
      hcl I (I.centers LS') (toDums I Λ) (I.centers blue) c (I.centers Y) := by
  have hne : LS' ≠ [] := List.ne_nil_of_mem hc
  have hDnd : ((toRaw I).clusterMixQ LS' Λ c).Nodup := List.nodup_range.filter _
  have hDn : ∀ j ∈ (toRaw I).clusterMixQ LS' Λ c, j < I.n :=
    fun j hj ↦ List.mem_range.1 (List.mem_of_mem_filter hj)
  have hDeq : ((univ : Finset (Fin I.n)).filter fun j ↦ j.1 ∈ (toRaw I).clusterMixQ LS' Λ c) =
      clusterMix I (I.centers LS') (toDums I Λ) c := by
    ext j
    simp only [mem_filter, mem_univ, true_and]
    exact Raw.mem_clusterMixQ hne hm hΛ
  have hcard : ((toRaw I).clusterMixQ LS' Λ c).length =
      (clusterMix I (I.centers LS') (toDums I Λ) c).card := by
    rw [← hDeq, card_filter_mem hDnd hDn]
  have hbY : ∀ i ∈ blue ++ Y, i < I.m := by
    intro i hi
    rcases List.mem_append.1 hi with h | h
    · exact hb i h
    · exact hY i h
  have hcen : I.centers (blue ++ Y) = I.centers blue ∪ I.centers Y := by
    ext i
    simp [Instance.mem_centers]
  have h2 := Raw.dMixQ_toRaw hbY hΛ (.inr c)
  rw [Instance.ptIdx_inr, hcen] at h2
  unfold Raw.hclQ hcl Raw.costMixOnQ costMixOn
  rw [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Raw.n_toRaw, h2, hcard, Rat.cast_list_sum,
    List.map_map, sum_map_eq_sum_filter hDnd hDn, hDeq]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  have h1 := Raw.dMixQ_toRaw hm hΛ (.inl j)
  rw [Instance.ptIdx_inl] at h1
  exact h1

private theorem sumSmallest_congr {ι : Type*} {z : ℕ} {A : Finset ι} {u v : ι → ℝ}
    (h : ∀ c ∈ A, u c = v c) : sumSmallest z A u = sumSmallest z A v :=
  le_antisymm (sumSmallest_mono fun c hc ↦ (h c hc).le) (sumSmallest_mono fun c hc ↦ (h c hc).ge)

/-- **Threshold**: a set whose values are at most all the values outside it has the least sum
among the sets of its size. -/
private theorem sum_le_sum_of_forall_le {ι : Type*} {A Zh Z : Finset ι} (v : ι → ℝ)
    (hZ : Z ⊆ A) (hcard : Zh.card = Z.card)
    (hle : ∀ a ∈ Zh, ∀ b ∈ A, b ∉ Zh → v a ≤ v b) : ∑ c ∈ Zh, v c ≤ ∑ c ∈ Z, v c := by
  classical
  rw [← sum_sdiff (inter_subset_left : Zh ∩ Z ⊆ Zh),
    ← sum_sdiff (inter_subset_right : Zh ∩ Z ⊆ Z)]
  have hc : (Zh \ (Zh ∩ Z)).card = (Z \ (Zh ∩ Z)).card := by
    rw [card_sdiff_of_subset inter_subset_left, card_sdiff_of_subset inter_subset_right, hcard]
  rcases (Zh \ (Zh ∩ Z)).eq_empty_or_nonempty with h0 | hne
  · rw [h0, card_empty] at hc
    rw [h0, card_eq_zero.1 hc.symm]
  · obtain ⟨a, ha, hmax⟩ := exists_max_image _ v hne
    have h1 : ∑ c ∈ Zh \ (Zh ∩ Z), v c ≤ (Zh \ (Zh ∩ Z)).card • v a :=
      sum_le_card_nsmul _ _ _ hmax
    have h2 : (Z \ (Zh ∩ Z)).card • v a ≤ ∑ c ∈ Z \ (Zh ∩ Z), v c := by
      refine card_nsmul_le_sum _ _ _ fun b hb ↦ ?_
      have hb' := mem_sdiff.1 hb
      exact hle a (mem_sdiff.1 ha).1 b (hZ hb'.1) fun hbZh ↦ hb'.2 (mem_inter.2 ⟨hbZh, hb'.1⟩)
    rw [hc] at h1
    linarith

/-- The `z` first entries of a list sorted by `key` attain the sum of the `z` smallest values. -/
private theorem sum_take_mergeSort {I : Instance} {l : List ℕ} (hnd : l.Nodup)
    (hm : ∀ i ∈ l, i < I.m)
    (key : ℕ → ℚ) {z : ℕ} (hz : z ≤ l.length) :
    ∑ c ∈ I.centers ((l.mergeSort fun c c' ↦ decide (key c ≤ key c')).take z), (key c.1 : ℝ) =
      sumSmallest z (I.centers l) fun c ↦ (key c.1 : ℝ) := by
  classical
  set L := l.mergeSort fun c c' ↦ decide (key c ≤ key c') with hL
  have hperm : L.Perm l := List.mergeSort_perm _ _
  have hLnd : L.Nodup := hperm.nodup_iff.2 hnd
  have hsort : L.Pairwise fun c c' ↦ decide (key c ≤ key c') = true :=
    List.pairwise_mergeSort (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b ↦ by simpa using le_total _ _) l
  have htake_m : ∀ i ∈ L.take z, i < I.m := fun i hi ↦ hm i (hperm.subset (List.mem_of_mem_take hi))
  have hsub : I.centers (L.take z) ⊆ I.centers l :=
    Instance.centers_mono fun i hi ↦ hperm.subset (List.mem_of_mem_take hi)
  have hcard : (I.centers (L.take z)).card = z := by
    rw [Instance.card_centers (hLnd.sublist (List.take_sublist _ _)) htake_m, List.length_take,
      hperm.length_eq]
    omega
  refine le_antisymm ?_ (sumSmallest_le hsub hcard _)
  obtain ⟨Z, hZA, hZc, hZs⟩ := exists_sumSmallest_eq (z := z)
    (by rw [Instance.card_centers hnd hm]; exact hz) (fun c : Fin I.m ↦ (key c.1 : ℝ))
  rw [← hZs]
  refine sum_le_sum_of_forall_le _ hZA (by rw [hcard, hZc]) fun a ha b hb hbn ↦ ?_
  have ha' := Instance.mem_centers.1 ha
  have hb' : b.1 ∈ L.drop z := by
    have : b.1 ∈ L := hperm.symm.subset (Instance.mem_centers.1 hb)
    rw [← List.take_append_drop z L, List.mem_append] at this
    exact this.resolve_left fun h ↦ hbn (Instance.mem_centers.2 h)
  have hs := hsort
  rw [← List.take_append_drop z L] at hs
  have hp := (List.pairwise_append.1 hs).2.2 _ ha' _ hb'
  simpa using hp

private theorem sumSmallestQ_map {I : Instance} {l : List ℕ} (hnd : l.Nodup) (hm : ∀ i ∈ l, i < I.m)
    (key : ℕ → ℚ) {z : ℕ} (hz : z ≤ l.length) :
    (Raw.sumSmallestQ z (l.map key) : ℝ) = sumSmallest z (I.centers l) fun c ↦ (key c.1 : ℝ) := by
  rw [← sum_take_mergeSort hnd hm key hz]
  set L := l.mergeSort fun c c' ↦ decide (key c ≤ key c') with hL
  have hperm : L.Perm l := List.mergeSort_perm _ _
  have hLnd : L.Nodup := hperm.nodup_iff.2 hnd
  have hsort : L.Pairwise fun c c' ↦ decide (key c ≤ key c') = true :=
    List.pairwise_mergeSort (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b ↦ by simpa using le_total _ _) l
  have heq : (l.map key).mergeSort (fun a a' ↦ decide (a ≤ a')) = L.map key := by
    refine List.Perm.eq_of_pairwise (le := fun a a' ↦ decide (a ≤ a') = true)
      (fun a b _ _ h1 h2 ↦ by simp only [decide_eq_true_eq] at h1 h2; exact le_antisymm h1 h2)
      (List.pairwise_mergeSort (fun a b c h1 h2 ↦ by simp only [decide_eq_true_eq] at *; linarith)
        (fun a b ↦ by simpa using le_total _ _) _)
      (List.pairwise_map.2 hsort) ?_
    exact (List.mergeSort_perm _ _).trans (hperm.map key).symm
  have htake_m : ∀ i ∈ L.take z, i < I.m := fun i hi ↦ hm i (hperm.subset (List.mem_of_mem_take hi))
  unfold Raw.sumSmallestQ
  rw [heq, ← List.map_take, Rat.cast_list_sum, List.map_map]
  exact sum_map_eq_sum_filter (hLnd.sublist (List.take_sublist _ _)) htake_m _

/-- **The exact `g`** is `g` on the facilities. -/
private theorem gQ_toRaw {I : Instance} {LS' : List ℕ} (hm : ∀ i ∈ LS', i < I.m) {Λ : List DumQ}
    (hΛ : (toRaw I).ValidDums Λ) {red blue : List ℕ} (hred : ∀ c ∈ red, c ∈ LS')
    (hrnd : red.Nodup) (hb : ∀ c ∈ blue, c < I.m) {z : ℕ} (hz : z ≤ red.length) {Y : List ℕ}
    (hY : ∀ i ∈ Y, i < I.m) :
    ((toRaw I).gQ LS' Λ red blue z Y : ℝ) =
      gfun I (I.centers LS') (toDums I Λ) (I.centers red) (I.centers blue) z (I.centers Y) := by
  have hrm : ∀ c ∈ red, c < I.m := fun c hc ↦ hm c (hred c hc)
  unfold Raw.gQ gfun Raw.g₂Q g₂
  rw [Rat.cast_add, g₁Q_toRaw hm hΛ hY, sumSmallestQ_map hrnd hrm _ hz]
  congr 1
  refine sumSmallest_congr fun c hc ↦ ?_
  exact hclQ_toRaw hm hΛ hb hY (hred _ (Instance.mem_centers.1 hc))

/-! ### Red, blue and the dummies -/

private theorem redOf_sublist : ∀ (LS' : List ℕ) (col : List Bool), (redOf LS' col).Sublist LS'
  | [], _ => by simp [redOf]
  | _ :: _, [] => by simp [redOf]
  | a :: l, b :: c => by
    have ih := redOf_sublist l c
    unfold redOf at ih ⊢
    rw [List.zip_cons_cons, List.filterMap_cons]
    cases b
    · exact ih.cons a
    · exact ih.cons_cons a

private theorem blueOf_sublist : ∀ (LS' : List ℕ) (col : List Bool), (blueOf LS' col).Sublist LS'
  | [], _ => by simp [blueOf]
  | _ :: _, [] => by simp [blueOf]
  | a :: l, b :: c => by
    have ih := blueOf_sublist l c
    unfold blueOf at ih ⊢
    rw [List.zip_cons_cons, List.filterMap_cons]
    cases b
    · exact ih.cons_cons a
    · exact ih.cons a

private theorem toDums_eq_pmap {I : Instance} : ∀ {Λ : List DumQ} (hΛ : ∀ l ∈ Λ, l.1 < I.n + I.m),
    toDums I Λ = Λ.pmap (fun l h ↦ (⟨finSumFinEquiv.symm ⟨l.1, h⟩, (l.2 : ℝ)⟩ : Dummy I)) hΛ
  | [], _ => rfl
  | l :: Λ, hΛ => by
    have hl : l.1 < I.n + I.m := hΛ l List.mem_cons_self
    have ih := toDums_eq_pmap (Λ := Λ) fun l' hl' ↦ hΛ l' (List.mem_cons_of_mem _ hl')
    unfold toDums at ih ⊢
    rw [List.filterMap_cons, dif_pos hl, List.pmap_cons, ih]

private theorem length_toDums' {I : Instance} {Λ : List DumQ} (hΛ : ∀ l ∈ Λ, l.1 < I.n + I.m) :
    (toDums I Λ).length = Λ.length := by
  rw [toDums_eq_pmap hΛ, List.length_pmap]

private theorem getElem_toDums {I : Instance} {Λ : List DumQ} (hΛ : ∀ l ∈ Λ, l.1 < I.n + I.m)
    {j : ℕ}
    (hj : j < Λ.length) :
    (toDums I Λ)[j]'(by rw [length_toDums' hΛ]; exact hj) =
      ⟨finSumFinEquiv.symm ⟨Λ[j].1, hΛ _ (List.getElem_mem _)⟩, (Λ[j].2 : ℝ)⟩ := by
  rw [List.getElem_of_eq (toDums_eq_pmap hΛ), List.getElem_pmap]

/-! ### The candidate -/

/-- The parts of the guess `p'`: the balls of the dummies, then `p'` copies of all facilities. -/
private def partsOf (I : Instance) (Λ : List DumQ) (p' : ℕ) : List (List ℕ) :=
  Λ.map (toRaw I).ballQ ++ List.replicate p' (List.range I.m)

private theorem length_partsOf (I : Instance) (Λ : List DumQ) (p' : ℕ) :
    (partsOf I Λ p').length = Λ.length + p' := by
  simp [partsOf]

private theorem getD_partsOf_lt {I : Instance} {Λ : List DumQ} {p' j : ℕ} (hj : j < Λ.length) :
    (partsOf I Λ p').getD j [] = (toRaw I).ballQ Λ[j] := by
  rw [List.getD_eq_getElem _ _ (by rw [length_partsOf]; omega)]
  simp only [partsOf]
  rw [List.getElem_append_left (by simpa using hj), List.getElem_map]

private theorem getD_partsOf_ge {I : Instance} {Λ : List DumQ} {p' j : ℕ} (h1 : Λ.length ≤ j)
    (h2 : j < Λ.length + p') : (partsOf I Λ p').getD j [] = List.range I.m := by
  rw [List.getD_eq_getElem _ _ (by rw [length_partsOf]; omega)]
  simp only [partsOf]
  rw [List.getElem_append_right (by simpa using h1), List.getElem_replicate]

variable {I : Instance}

end Helpers

variable {I : Instance}

/-- **The guess is not skipped** when its conditions hold. -/
theorem candidate_isSome {N s B : ℕ} {LS' : List ℕ} {Λ : List DumQ} {col : List Bool} {p' : ℕ}
    (hρ : Λ.length + p' ≤ s) (hz : (LS'.length + (Λ.length + p')) - I.k ≤ (redOf LS' col).length)
    (hball : ∀ l ∈ Λ, (toRaw I).ballQ l ≠ []) :
    (candidate N (toRaw I) s B LS' Λ col p').isSome := by
  have hk : (toRaw I).k = I.k := rfl
  have hcond : ¬ (s < Λ.length + p' ∨
      (redOf LS' col).length < LS'.length + (Λ.length + p') - (toRaw I).k ∨
        (Λ.any fun l ↦ ((toRaw I).ballQ l).isEmpty) = true) := by
    rintro (h | h | h)
    · omega
    · omega
    · obtain ⟨l, hl, he⟩ := List.any_eq_true.1 h
      exact hball l hl (List.isEmpty_iff.1 he)
  dsimp only [candidate]
  rw [if_neg hcond]
  rfl

end Stable

end BCFGJPSSV26


