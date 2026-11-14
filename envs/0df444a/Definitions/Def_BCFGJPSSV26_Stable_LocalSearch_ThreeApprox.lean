-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
-- name    : BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:11.488918+00:00
-- url     : https://prove2.me/theorems/8896798e-6a51-4066-a60c-766bc26be275
-- title:
--   BCFGJPSSV26.Stable.LocalSearch.ThreeApprox — Local search is a `3 + O(1/N)`-approximation
-- statement:
--   This is module `BCFGJPSSV26.Stable.LocalSearch.ThreeApprox` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Corollary 1.5]: an approximate local optimum `S` with swaps
--   of size `24 N` and threshold `1/(N k)`, `N ≥ 201`, costs at most `(3 + 100/N) opt k ≤ 4 opt k`
--   (`BCFGJPSSV26.Stable.costF_le_three_add`, `BCFGJPSSV26.Stable.costF_le_four_opt`).
--
--   Proof: the refined bound (`BCFGJPSSV26.Stable.refined_ls`) with `B = O` optimal, `D₀` all
--   clients, `μB = near(O, ·)` and `μA = near(S, near(O, ·))`, which are cross-free since every
--   `A`-cluster is a union of `O`-clusters (`BCFGJPSSV26.Stable.crossFree_near_near`), and
--   `cost(μA) ≤ cost(S) + 2 opt` by the triangle inequality through the optimal centers
--   (`BCFGJPSSV26.Stable.costMap_near_near_le`).
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.costF_le_four_opt`, `BCFGJPSSV26.Stable.costF_le_three_add` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/LocalSearch/ThreeApprox.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_Refined

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.LocalSearch.ThreeApprox` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Local search is a `3 + O(1/N)`-approximation

[BCFGJPSSV26b, Corollary 1.5]: an approximate local optimum `S` with swaps
of size `24 N` and threshold `1/(N k)`, `N ≥ 201`, costs at most `(3 + 100/N) opt k ≤ 4 opt k`
(`BCFGJPSSV26.Stable.costF_le_three_add`, `BCFGJPSSV26.Stable.costF_le_four_opt`).

Proof: the refined bound (`BCFGJPSSV26.Stable.refined_ls`) with `B = O` optimal, `D₀` all
clients, `μB = near(O, ·)` and `μA = near(S, near(O, ·))`, which are cross-free since every
`A`-cluster is a union of `O`-clusters (`BCFGJPSSV26.Stable.crossFree_near_near`), and
`cost(μA) ≤ cost(S) + 2 opt` by the triangle inequality through the optimal centers
(`BCFGJPSSV26.Stable.costMap_near_near_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

/-- `μA = near(S, near(O, ·))` and `μB = near(O, ·)` are cross-free with respect to all clients:
every `A`-cluster is a union of `O`-clusters. -/
theorem crossFree_near_near {S O : Finset (Fin I.m)} (hS : S.Nonempty) (hO : O.Nonempty) :
    CrossFreeWrt I S (fun j ↦ I.near S hS (.inr (I.near O hO (.inl j))))
      (fun j ↦ I.near O hO (.inl j)) univ := by
  intro c _ c'
  by_cases h : I.near S hS (.inr c') = c
  · refine Or.inr (Or.inr fun j hj ↦ ?_)
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    rw [hj.1, h]
  · refine Or.inl (disjoint_left.2 fun j hj hj' ↦ h ?_)
    simp only [mem_filter, mem_univ, true_and] at hj hj'
    rw [← hj'.1]
    exact hj

/-- `cost(near(S, near(O, ·))) ≤ cost(S) + 2 cost(O)`: a client `j` with optimal center `o` pays
at most `d(j, o) + d(o, S)`, and `∑_j d(o_j, S) ≤ cost(O) + cost(S)`. -/
theorem costMap_near_near_le (hv : I.Valid) {S O : Finset (Fin I.m)} (hS : S.Nonempty)
    (hO : O.Nonempty) :
    I.costMap (fun j ↦ I.near S hS (.inr (I.near O hO (.inl j)))) univ ≤
      I.costF S + 2 * I.costF O := by
  unfold Instance.costMap Instance.costF
  rw [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun j _ ↦ ?_
  set o := I.near O hO (.inl j)
  have h1 := Instance.dd_triangle hv (.inl j) (.inr o) (.inr (I.near S hS (.inr o)))
  have h2 : I.dd (.inl j) (.inr o) = I.dSet (.inl j) O := Instance.dd_near hO _
  have h3 : I.dd (.inr o) (.inr (I.near S hS (.inr o))) = I.dSet (.inr o) S :=
    Instance.dd_near hS _
  have h4 := Instance.dSet_triangle hv (.inr o) (.inl j) S
  rw [Instance.dd_comm hv, h2] at h4
  linarith

end BCFGJPSSV26.Stable


