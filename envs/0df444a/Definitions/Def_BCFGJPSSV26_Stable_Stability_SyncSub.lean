-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub
-- name    : BCFGJPSSV26_Stable_Stability_SyncSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:00:39.760737+00:00
-- url     : https://prove2.me/theorems/b30efc52-5f2f-434f-ab1f-c984e85f03ec
-- title:
--   BCFGJPSSV26.Stable.Stability.SyncSub — Substitutes for synced and close clusters
-- statement:
--   This is module `BCFGJPSSV26.Stable.Stability.SyncSub` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   * [BCFGJPSSV26b, Proposition 4.3] (`BCFGJPSSV26.Stable.Hyp.syncSub`): the synced clusters, sent
--     to their partners, cost at most `(1 + 4ε) ∑_{O_sync} cost_OPT(C*) + 5 ε cost(S)`. The proof
--     adapts that of [CGLSS25, Lemma 4.4] to `ε`-synced clusters and approximate local optima: it
--     swaps the partner `c'` for `c*` (one swap, allowed by approximate local optimality): the
--     clients of `C* ∩ C_{c'}` move to `c*`, those of `C_{c'} \ C*` too at cost at most
--     `d(j, S) + d(c', c*)`, with `d(c', c*)` at most the average of `d(·, S) + d(·, c*)` over
--     `C* ∩ C_{c'}`; the error `cost(S)/(N k)` per swap sums to `ε cost(S)` over the `k` swaps.
--   * [BCFGJPSSV26b, Proposition 4.4] (`BCFGJPSSV26.Stable.Hyp.closeSub`): a close cluster sent to
--     the nearest local-search center of its center costs at most
--     `(1 + η) cost_OPT(C*) + 2 ε cost_S(C*)`, by the triangle inequality through `c*`.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Hyp.closeSub`, `BCFGJPSSV26.Stable.Hyp.syncSub` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Stability_SyncSub`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Stability/SyncSub.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Stability.SyncSub` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Substitutes for synced and close clusters

* [BCFGJPSSV26b, Proposition 4.3] (`BCFGJPSSV26.Stable.Hyp.syncSub`): the synced clusters, sent
  to their partners, cost at most `(1 + 4ε) ∑_{O_sync} cost_OPT(C*) + 5 ε cost(S)`. The proof
  adapts that of [CGLSS25, Lemma 4.4] to `ε`-synced clusters and approximate local optima: it
  swaps the partner `c'` for `c*` (one swap, allowed by approximate local optimality): the
  clients of `C* ∩ C_{c'}` move to `c*`, those of `C_{c'} \ C*` too at cost at most
  `d(j, S) + d(c', c*)`, with `d(c', c*)` at most the average of `d(·, S) + d(·, c*)` over
  `C* ∩ C_{c'}`; the error `cost(S)/(N k)` per swap sums to `ε cost(S)` over the `k` swaps.
* [BCFGJPSSV26b, Proposition 4.4] (`BCFGJPSSV26.Stable.Hyp.closeSub`): a close cluster sent to
  the nearest local-search center of its center costs at most
  `(1 + η) cost_OPT(C*) + 2 ε cost_S(C*)`, by the triangle inequality through `c*`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

/-- The optimal clusters are disjoint, so their local-search costs add up to at most
`cost(S)`. -/
private theorem sum_costS_C_le (A : Finset (Fin X.I.m)) :
    ∑ c ∈ A, X.costS (X.C c) ≤ X.I.costF X.S := by
  classical
  have hdisj : (A : Set (Fin X.I.m)).PairwiseDisjoint X.C :=
    fun c _ c' _ h ↦ Instance.disjoint_cluster _ h
  calc ∑ c ∈ A, X.costS (X.C c) = X.I.costOn X.S (A.biUnion X.C) := by
        change ∑ c ∈ A, ∑ j ∈ X.C c, X.I.dSet (.inl j) X.S =
          ∑ j ∈ A.biUnion X.C, X.I.dSet (.inl j) X.S
        rw [sum_biUnion hdisj]
    _ ≤ X.I.costF X.S := Instance.costOn_le_costF H.valid _ _

/-- The swap `T = (S \ {c'}) ∪ {c*}` of a synced center `c*` with its partner `c'`: by approximate
local optimality, the clients of `C* ∩ C_{c'}` pay in `S` at most their distance to `c*`, plus
`|C_{c'} \ C*| d(c', c*)` and the error `cost(S)/(N k)`. -/
private theorem swap_bound {c c' : Fin X.I.m} (hc'S : c' ∈ X.S) :
    ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S ≤ ∑ j ∈ X.C c ∩ X.CS c', X.dist j c +
      (X.CS c' \ X.C c).card * X.dF c' c + X.I.costF X.S / (X.P.N * X.I.k) := by
  classical
  have hv := H.valid
  have hSne := H.S_nonempty
  have hTne : (insert c (X.S.erase c')).Nonempty := insert_nonempty _ _
  have hTk : (insert c (X.S.erase c')).card ≤ X.I.k := by
    have h1 := card_insert_le c (X.S.erase c')
    have h2 := card_erase_of_mem hc'S
    have h3 := H.alo.1
    have h4 := H.two_le_k
    omega
  have hST : (X.S \ insert c (X.S.erase c')).card ≤ Par.p X.P.N := by
    have hsub : X.S \ insert c (X.S.erase c') ⊆ {c'} := by
      intro x hx
      obtain ⟨hxS, hxT⟩ := mem_sdiff.1 hx
      by_contra hxc
      exact hxT (mem_insert_of_mem (mem_erase.2 ⟨by simpa using hxc, hxS⟩))
    have h1 := card_le_card hsub
    rw [card_singleton] at h1
    unfold Par.p
    have := X.P.hN
    omega
  have halo := H.alo.2 _ hTne hTk hST
  have hpt : ∀ j, X.I.dSet (.inl j) (insert c (X.S.erase c')) ≤ X.I.dSet (.inl j) X.S +
      ((if j ∈ X.C c ∩ X.CS c' then X.dist j c - X.I.dSet (.inl j) X.S else 0) +
        (if j ∈ X.CS c' \ X.C c then X.dF c' c else 0)) := by
    intro j
    by_cases hjC' : j ∈ X.CS c'
    · have hjS : X.I.dSet (.inl j) X.S = X.dist j c' := Instance.dSet_of_mem_cluster hjC'
      have hjT : X.I.dSet (.inl j) (insert c (X.S.erase c')) ≤ X.dist j c :=
        Instance.dSet_le (mem_insert_self _ _) _
      by_cases hjC : j ∈ X.C c
      · rw [if_pos (mem_inter.2 ⟨hjC, hjC'⟩),
          if_neg fun h ↦ (mem_sdiff.1 h).2 hjC]
        linarith
      · rw [if_neg fun h ↦ hjC (mem_inter.1 h).1, if_pos (mem_sdiff.2 ⟨hjC', hjC⟩)]
        have := Instance.dd_triangle hv (.inl j) (.inr c') (.inr c)
        unfold Ctx.dist at hjS hjT
        unfold Ctx.dF
        linarith
    · rw [if_neg fun h ↦ hjC' (mem_inter.1 h).2, if_neg fun h ↦ hjC' (mem_sdiff.1 h).1,
        add_zero, add_zero]
      have hnear : X.I.near X.S hSne (.inl j) ∈ insert c (X.S.erase c') :=
        mem_insert_of_mem (mem_erase.2 ⟨fun h ↦ hjC' ((Instance.mem_cluster hSne).2 h),
          Instance.near_mem _ _⟩)
      calc _ ≤ X.I.dd (.inl j) (.inr (X.I.near X.S hSne (.inl j))) := Instance.dSet_le hnear _
        _ = _ := Instance.dd_near _ _
  have hTcost : X.I.costF (insert c (X.S.erase c')) ≤ X.I.costF X.S +
      ((∑ j ∈ X.C c ∩ X.CS c', X.dist j c - ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S) +
        (X.CS c' \ X.C c).card * X.dF c' c) := by
    calc X.I.costF (insert c (X.S.erase c'))
        ≤ ∑ j, (X.I.dSet (.inl j) X.S +
          ((if j ∈ X.C c ∩ X.CS c' then X.dist j c - X.I.dSet (.inl j) X.S else 0) +
            (if j ∈ X.CS c' \ X.C c then X.dF c' c else 0))) := sum_le_sum fun j _ ↦ hpt j
      _ = _ := by
        rw [sum_add_distrib, sum_add_distrib, sum_ite_mem, sum_ite_mem, univ_inter, univ_inter,
          sum_const, nsmul_eq_mul, sum_sub_distrib]
        rfl
  have : (1 - 1 / ((X.P.N : ℝ) * X.I.k)) * X.I.costF X.S =
      X.I.costF X.S - X.I.costF X.S / (X.P.N * X.I.k) := by ring
  linarith

/-- One synced cluster: `∑_{j ∈ C*} d(j, c') ≤ (1 + 2ε) cost_OPT(C*) + 2ε cost_S(C*) +
cost(S)/(N k)`. -/
private theorem syncSub_one {c : Fin X.I.m} (hc : c ∈ X.Osync) :
    ∑ j ∈ X.C c, X.dist j (X.σsync c) ≤ (1 + 2 * X.ε) * X.costO c +
      2 * X.ε * X.costS (X.C c) + X.I.costF X.S / (X.P.N * X.I.k) := by
  classical
  have hv := H.valid
  obtain ⟨hcO, hsync⟩ := mem_filter.1 hc
  obtain ⟨hc'S, hsym⟩ := H.σsync_spec hsync
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hstar := H.swap_bound (c := c) hc'S
  set c' := X.σsync c
  -- `d(c', c*)` is at most the average of `d(·, S) + d(·, c*)` over `C* ∩ C_{c'}`
  have hdF : ((X.C c ∩ X.CS c').card : ℝ) * X.dF c' c ≤
      ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) := by
    calc ((X.C c ∩ X.CS c').card : ℝ) * X.dF c' c = ∑ j ∈ X.C c ∩ X.CS c', X.dF c' c := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun j hj ↦ by
        have hjS : X.I.dSet (.inl j) X.S = X.dist j c' :=
          Instance.dSet_of_mem_cluster (mem_inter.1 hj).2
        have := Instance.dd_triangle hv (.inr c') (.inl j) (.inr c)
        rw [Instance.dd_comm hv (.inr c') (.inl j)] at this
        unfold Ctx.dist at hjS ⊢
        unfold Ctx.dF
        linarith
  have hsplit : ∑ j ∈ X.C c, X.dist j c' =
      ∑ j ∈ X.C c ∩ X.CS c', X.dist j c' + ∑ j ∈ X.C c \ X.CS c', X.dist j c' :=
    (sum_inter_add_sum_sdiff _ _ _).symm
  have hsplitO : X.costO c =
      ∑ j ∈ X.C c ∩ X.CS c', X.dist j c + ∑ j ∈ X.C c \ X.CS c', X.dist j c :=
    (sum_inter_add_sum_sdiff _ _ _).symm
  have hA : ∑ j ∈ X.C c ∩ X.CS c', X.dist j c' =
      ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S :=
    sum_congr rfl fun j hj ↦ (Instance.dSet_of_mem_cluster (mem_inter.1 hj).2).symm
  have hD : ∑ j ∈ X.C c \ X.CS c', X.dist j c' ≤
      ∑ j ∈ X.C c \ X.CS c', X.dist j c + (X.C c \ X.CS c').card * X.dF c' c := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr c')
    rw [Instance.dd_comm hv (.inr c) (.inr c')] at this
    exact this
  -- cardinalities
  have hBD : ((X.CS c' \ X.C c).card : ℝ) + (X.C c \ X.CS c').card ≤ X.ε * (X.C c).card := by
    have h1 : (X.C c \ X.CS c').card + (X.CS c' \ X.C c).card = X.symmCard c c' := by
      unfold Ctx.symmCard
      rw [card_union_of_disjoint disjoint_sdiff_sdiff]
    have h2 : X.ε * min ((X.C c).card : ℝ) (X.CS c').card ≤ X.ε * (X.C c).card :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hε.le
    have h3 : ((X.C c \ X.CS c').card : ℝ) + (X.CS c' \ X.C c).card = X.symmCard c c' := by
      exact_mod_cast h1
    linarith
  have hAcard : (1 - X.ε) * (X.C c).card ≤ (X.C c ∩ X.CS c').card := by
    have h1 : ((X.C c ∩ X.CS c').card : ℝ) + (X.C c \ X.CS c').card = (X.C c).card := by
      exact_mod_cast card_inter_add_card_sdiff _ _
    have : (0 : ℝ) ≤ (X.CS c' \ X.C c).card := Nat.cast_nonneg _
    linarith
  -- the averaged bound on `d(c', c*)`
  have hdF0 : 0 ≤ X.dF c' c := Instance.dd_nonneg hv _ _
  have hY : ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) ≤
      X.costS (X.C c) + X.costO c := by
    rw [sum_add_distrib]
    have h1 : ∑ j ∈ X.C c ∩ X.CS c', X.I.dSet (.inl j) X.S ≤ X.costS (X.C c) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_left fun j _ _ ↦ Instance.dSet_nonneg hv _ _
    have h2 : 0 ≤ ∑ j ∈ X.C c \ X.CS c', X.dist j c :=
      sum_nonneg fun j _ ↦ Instance.dd_nonneg hv _ _
    linarith
  have hP : ((X.C c).card : ℝ) * X.dF c' c ≤
      2 * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) := by
    have h1 : (1 - X.ε) * ((X.C c).card * X.dF c' c) ≤
        ((X.C c ∩ X.CS c').card : ℝ) * X.dF c' c := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hAcard hdF0
    have h2 : 0 ≤ ((X.C c).card : ℝ) * X.dF c' c := mul_nonneg (Nat.cast_nonneg _) hdF0
    nlinarith
  have hBDdF : (((X.CS c' \ X.C c).card : ℝ) + (X.C c \ X.CS c').card) * X.dF c' c ≤
      2 * X.ε * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) := by
    calc (((X.CS c' \ X.C c).card : ℝ) + (X.C c \ X.CS c').card) * X.dF c' c
        ≤ X.ε * (X.C c).card * X.dF c' c := mul_le_mul_of_nonneg_right hBD hdF0
      _ = X.ε * ((X.C c).card * X.dF c' c) := by ring
      _ ≤ X.ε * (2 * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c)) :=
          mul_le_mul_of_nonneg_left hP hε.le
      _ = _ := by ring
  have hfin : 2 * X.ε * ∑ j ∈ X.C c ∩ X.CS c', (X.I.dSet (.inl j) X.S + X.dist j c) ≤
      2 * X.ε * (X.costS (X.C c) + X.costO c) :=
    mul_le_mul_of_nonneg_left hY (by linarith)
  rw [hsplit, hA]
  nlinarith

end Hyp

end BCFGJPSSV26.Stable


