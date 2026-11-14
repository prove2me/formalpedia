-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined
-- name    : BCFGJPSSV26_Stable_LocalSearch_Refined
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:27.830746+00:00
-- url     : https://prove2.me/theorems/fa6af032-6554-4d2a-ac04-91d52fac5978
-- title:
--   BCFGJPSSV26.Stable.LocalSearch.Refined — The refined local-search bound
-- statement:
--   This is module `BCFGJPSSV26.Stable.LocalSearch.Refined` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Theorem 3.6]: for an approximate local optimum `S`
--   with swaps of size `24 N` and threshold `1/(N k)`, a benchmark set `B`, assignments
--   `μA : clients → S` and `μB : clients → B`, and a set `D₀` of clients such that
--   `|B| + |μA(D \ D₀)| ≤ k` and the two clusterings are cross-free with respect to `D₀`
--   (`BCFGJPSSV26.Stable.CrossFreeWrt`, [BCFGJPSSV26b, Definition 3.5]),
--
--     `cost(S) ≤ cost_μB(D₀) + (cost(μA) - cost_S(D₀)) + (10/N) (cost(μA) + cost_μB(D₀))`
--
--   (`BCFGJPSSV26.Stable.refined_ls`). The paper's `O(ε)` is `10/N` here.
--
--   Proof: the intersection graph of the `A`-clusters inside `D₀` and the
--   `B`-clusters is star-like by cross-freeness, and `|B| ≤ |A'|`; apply
--   `BCFGJPSSV26.Stable.BiGraph.exists_swap_families`, test every swap `T = (S \ A'ᵢ) ∪ Bᵢ` against
--   approximate local optimality with the test assignment of the paper, sum over the swaps of a
--   family and average over the families.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.refined_ls` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/Refined.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Defs
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_StarForest

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.LocalSearch.Refined` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The refined local-search bound

[BCFGJPSSV26b, Theorem 3.6]: for an approximate local optimum `S`
with swaps of size `24 N` and threshold `1/(N k)`, a benchmark set `B`, assignments
`μA : clients → S` and `μB : clients → B`, and a set `D₀` of clients such that
`|B| + |μA(D \ D₀)| ≤ k` and the two clusterings are cross-free with respect to `D₀`
(`BCFGJPSSV26.Stable.CrossFreeWrt`, [BCFGJPSSV26b, Definition 3.5]),

  `cost(S) ≤ cost_μB(D₀) + (cost(μA) - cost_S(D₀)) + (10/N) (cost(μA) + cost_μB(D₀))`

(`BCFGJPSSV26.Stable.refined_ls`). The paper's `O(ε)` is `10/N` here.

Proof: the intersection graph of the `A`-clusters inside `D₀` and the
`B`-clusters is star-like by cross-freeness, and `|B| ≤ |A'|`; apply
`BCFGJPSSV26.Stable.BiGraph.exists_swap_families`, test every swap `T = (S \ A'ᵢ) ∪ Bᵢ` against
approximate local optimality with the test assignment of the paper, sum over the swaps of a
family and average over the families.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

variable (I) in
open Classical in
/-- **Cross-free with respect to `D₀`**: with `A'` the facilities of `S` all of whose `μA`-clients
are in `D₀`, `D̂₀ = μA⁻¹(A')`, `A_c = μA⁻¹(c)` and `B'_{c*} = μB⁻¹(c*) ∩ D̂₀`, every `A_c`,
`c ∈ A'`, and every `B'_{c*}` are disjoint or nested. -/
def CrossFreeWrt (S : Finset (Fin I.m)) (μA μB : Fin I.n → Fin I.m) (D₀ : Finset (Fin I.n)) :
    Prop :=
  ∀ c ∈ S.filter (fun c ↦ ∀ j, μA j = c → j ∈ D₀), ∀ c' : Fin I.m,
    Disjoint (univ.filter fun j ↦ μA j = c)
        (univ.filter fun j ↦ μB j = c' ∧ ∀ j', μA j' = μA j → j' ∈ D₀) ∨
      (univ.filter fun j ↦ μA j = c) ⊆
        (univ.filter fun j ↦ μB j = c' ∧ ∀ j', μA j' = μA j → j' ∈ D₀) ∨
      (univ.filter fun j ↦ μB j = c' ∧ ∀ j', μA j' = μA j → j' ∈ D₀) ⊆
        (univ.filter fun j ↦ μA j = c)

/-- Summing an indicator along the positions of a list counts. -/
private theorem sum_fin_countP {γ : Type*} (l : List γ) (p : γ → Bool) :
    (∑ i : Fin l.length, if p l[i] then (1 : ℕ) else 0) = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons, ← ih]
    change (∑ i : Fin (l.length + 1), if p (a :: l)[i] then (1 : ℕ) else 0) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ]
    rw [add_comm]
    rfl

/-- The same, in `ℝ`. -/
private theorem sum_fin_countP_real {γ : Type*} (l : List γ) (p : γ → Bool) :
    (∑ i : Fin l.length, if p l[i] then (1 : ℝ) else 0) = l.countP p := by
  rw [← sum_fin_countP l p]
  push_cast
  rfl

/-- One swap tested against approximate local optimality, with the test assignment: the clients
of `X` go to `μB`, the other clients of closed facilities to `μA`, the rest stay. -/
private theorem swap_test (hv : I.Valid) {p : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) {S : Finset (Fin I.m)}
    (hS : IsALO I p δ S) (hSne : S.Nonempty) {μA μB : Fin I.n → Fin I.m} (hA : ∀ j, μA j ∈ S)
    {Ls Rs : Finset (Fin I.m)} (hLs : Ls ⊆ S) (hcard : Rs.card ≤ Ls.card) (hp : Ls.card ≤ p)
    (X : Fin I.n → Prop) [DecidablePred X] (hX : ∀ j, X j → μB j ∈ Rs)
    (hXA : ∀ j, μA j ∈ Ls → X j) :
    ∑ j, (if X j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j)) else 0) ≤
      ∑ j, (if ¬ X j ∧ I.near S hSne (.inl j) ∈ Ls then
        I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0) + δ * I.costF S := by
  classical
  set T := (S \ Ls) ∪ Rs with hT
  have hT1 : (1 - δ) * I.costF S ≤ I.costF T := by
    rcases T.eq_empty_or_nonempty with hT0 | hT0
    · have h1 : I.costF S ≤ I.costF T := by
        rw [hT0]
        exact sum_le_sum fun j _ ↦ by
          rw [Instance.dSet_empty]
          exact Instance.dSet_le_dMax hv _ _
      nlinarith [Instance.costF_nonneg hv S]
    · refine hS.2 T hT0 ?_ ?_
      · have h1 : T.card ≤ (S \ Ls).card + Rs.card := card_union_le _ _
        have h2 : (S \ Ls).card = S.card - Ls.card := card_sdiff_of_subset hLs
        have h3 := card_le_card hLs
        have h4 := hS.1
        omega
      · refine (card_le_card fun c hc ↦ ?_).trans hp
        rw [mem_sdiff, hT, mem_union, mem_sdiff] at hc
        by_contra h
        exact hc.2 (Or.inl ⟨hc.1, h⟩)
  have hT2 : I.costF T ≤ ∑ j, (if X j then I.dd (.inl j) (.inr (μB j)) else
      if I.near S hSne (.inl j) ∈ Ls then I.dd (.inl j) (.inr (μA j)) else
        I.dSet (.inl j) S) := by
    unfold Instance.costF
    refine sum_le_sum fun j _ ↦ ?_
    split_ifs with h1 h2
    · exact Instance.dSet_le (mem_union_right _ (hX j h1)) _
    · exact Instance.dSet_le (mem_union_left _ (mem_sdiff.2 ⟨hA j, fun h ↦ h1 (hXA j h)⟩)) _
    · calc I.dSet (.inl j) T ≤ I.dd (.inl j) (.inr (I.near S hSne (.inl j))) :=
            Instance.dSet_le (mem_union_left _
              (mem_sdiff.2 ⟨Instance.near_mem hSne _, h2⟩)) _
        _ = I.dSet (.inl j) S := Instance.dd_near hSne _
  have hsplit : (∑ j, (if X j then I.dd (.inl j) (.inr (μB j)) else
      if I.near S hSne (.inl j) ∈ Ls then I.dd (.inl j) (.inr (μA j)) else
        I.dSet (.inl j) S)) = I.costF S -
      ∑ j, (if X j then I.dSet (.inl j) S - I.dd (.inl j) (.inr (μB j)) else 0) +
      ∑ j, (if ¬ X j ∧ I.near S hSne (.inl j) ∈ Ls then
        I.dd (.inl j) (.inr (μA j)) - I.dSet (.inl j) S else 0) := by
    unfold Instance.costF
    rw [← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases h1 : X j
    · simp [h1]
    · by_cases h2 : I.near S hSne (.inl j) ∈ Ls
      · simp [h1, h2]
      · simp [h1, h2]
  linarith

end BCFGJPSSV26.Stable


