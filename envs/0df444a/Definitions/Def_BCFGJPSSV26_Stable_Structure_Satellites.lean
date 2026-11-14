-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Structure_Satellites
-- name    : BCFGJPSSV26_Stable_Structure_Satellites
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:01:43.192583+00:00
-- url     : https://prove2.me/theorems/654d5f99-b107-455b-916b-9d4ce70c165b
-- title:
--   BCFGJPSSV26.Stable.Structure.Satellites — Satellites
-- statement:
--   This is module `BCFGJPSSV26.Stable.Structure.Satellites` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Section 3.1]: the **satellites** of an optimal center `c*` are the local-search
--   centers within `(1 + κ + 2ε) per` of `c*` and within `ε per` of some client of `C*`
--   (`BCFGJPSSV26.Stable.Ctx.Gam`); the looser `Γ_ε` uses `(1 + κ + 3ε) per` and `2ε per`
--   (`BCFGJPSSV26.Stable.Ctx.GamE`).
--
--   The clusters of `O₂` (those the cluster sampling handles) have the properties of
--   `BCFGJPSSV26.Stable.Ctx.IsFar`, proved in `BCFGJPSSV26/Stable/Structure/ClientWitness.lean`. For
--   them:
--
--   * [BCFGJPSSV26b, Lemma 4.5] (`BCFGJPSSV26.Stable.Hyp.no_dense_cores`): the satellites have
--     diameter at least `ε per`; otherwise reassigning the core to one satellite would contradict the
--     optimality of `O` together with the technical condition `BCFGJPSSV26.Stable.technical`;
--   * the claim on comparable percentiles of [BCFGJPSSV26b, Section 4.7]
--     (`BCFGJPSSV26.Stable.Hyp.comparable_per`): two clusters sharing a loose satellite have
--     percentiles within a factor `3`.
--
--   **Contents.** The module is published as a whole: 13 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Structure_Satellites`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Structure/Satellites.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Stability_Defs

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Structure.Satellites` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Satellites

[BCFGJPSSV26b, Section 3.1]: the **satellites** of an optimal center `c*` are the local-search
centers within `(1 + κ + 2ε) per` of `c*` and within `ε per` of some client of `C*`
(`BCFGJPSSV26.Stable.Ctx.Gam`); the looser `Γ_ε` uses `(1 + κ + 3ε) per` and `2ε per`
(`BCFGJPSSV26.Stable.Ctx.GamE`).

The clusters of `O₂` (those the cluster sampling handles) have the properties of
`BCFGJPSSV26.Stable.Ctx.IsFar`, proved in `BCFGJPSSV26/Stable/Structure/ClientWitness.lean`. For
them:

* [BCFGJPSSV26b, Lemma 4.5] (`BCFGJPSSV26.Stable.Hyp.no_dense_cores`): the satellites have
  diameter at least `ε per`; otherwise reassigning the core to one satellite would contradict the
  optimality of `O` together with the technical condition `BCFGJPSSV26.Stable.technical`;
* the claim on comparable percentiles of [BCFGJPSSV26b, Section 4.7]
  (`BCFGJPSSV26.Stable.Hyp.comparable_per`): two clusters sharing a loose satellite have
  percentiles within a factor `3`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace Ctx

variable (X : Ctx)

open Classical in
/-- The **satellites** `Γ(c*)`. -/
noncomputable def Gam (c : Fin X.I.m) : Finset (Fin X.I.m) :=
  X.S.filter fun c' ↦ X.dF c' c ≤ (1 + X.kap c + 2 * X.ε) * X.per c ∧
    ∃ j ∈ X.C c, X.dist j c' ≤ X.ε * X.per c

open Classical in
/-- The **loose satellites** `Γ_ε(c*)`. -/
noncomputable def GamE (c : Fin X.I.m) : Finset (Fin X.I.m) :=
  X.S.filter fun c' ↦ X.dF c' c ≤ (1 + X.kap c + 3 * X.ε) * X.per c ∧
    ∃ j ∈ X.C c, X.dist j c' ≤ 2 * X.ε * X.per c

/-- The satellites of a set of optimal centers. -/
noncomputable def GamOf (A : Finset (Fin X.I.m)) : Finset (Fin X.I.m) := A.biUnion X.Gam

/-- The loose satellites of a set of optimal centers. -/
noncomputable def GamEOf (A : Finset (Fin X.I.m)) : Finset (Fin X.I.m) := A.biUnion X.GamE

/-- **The clusters of `O₂`**: far from `S`, with cheap cores in `S`, average and percentile
comparable, positive, and with a satellite near the center. -/
structure IsFar (c : Fin X.I.m) : Prop where
  mem : c ∈ X.O
  far : eta * X.avgO c + 2 * X.ε * X.avgS c < X.dOS c
  core_cheap : X.costS (X.core (X.kap c) c) < X.ε ^ 3 * X.costO c
  avg_ge : X.per c / (1 + 2 * X.ε) ≤ X.avgO c
  avg_le : X.avgO c ≤ (1 + X.ε) * X.per c / eta
  costO_pos : 0 < X.costO c
  per_pos : 0 < X.per c
  near_sat : ∃ c' ∈ X.Gam c, X.dF c c' ≤ (1 + X.ε) * X.per c ∧
    ∃ j ∈ X.C c, X.dist j c' ≤ X.ε * X.per c

end Ctx

theorem Ctx.Gam_subset_GamE (X : Ctx) (hv : X.I.Valid) (c : Fin X.I.m) :
    X.Gam c ⊆ X.GamE c := by
  classical
  intro c' hc'
  simp only [Ctx.Gam, Ctx.GamE, mem_filter] at hc' ⊢
  obtain ⟨hS, h1, j, hj, h2⟩ := hc'
  have hp : 0 ≤ X.per c := per_nonneg hv _ _ _
  have he : 0 ≤ X.ε := X.P.eps_pos.le
  exact ⟨hS, h1.trans (by nlinarith), j, hj, h2.trans (by nlinarith)⟩

theorem Ctx.Gam_subset_S (X : Ctx) (c : Fin X.I.m) : X.Gam c ⊆ X.S := filter_subset _ _

/-- The arithmetic of `no_dense_cores`. -/
private theorem sat1_arith {ε κ P n nK nR L aK aR O SK : ℝ} (he : 0 < ε) (he' : ε < 1 / 200)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hP : 0 < P) (hn : 0 < n) (hnn : n = nK + nR)
    (hL : L < ε * n) (hKl : (nK - L) * P ≤ aK) (hRl : nR * ((1 + κ) * P) ≤ aR)
    (hO : O = aK + aR) (hopt : O ≤ aR + nR * ((1 + ε) * P) + ε * nK * P + 4 / ε * SK)
    (hSK : SK < ε ^ 3 * O) (hle : O * (89 / 100) ≤ (1 + ε) * P * n)
    (hge : P * n ≤ O * (1 + 2 * ε)) (htech : (2 + 6 * ε) * O ≤ (2 + κ) * (n * P)) :
    False := by
  have hnP : 0 < n * P := mul_pos hn hP
  have hOp : 0 < O := by nlinarith
  have s1 : 4 / ε * SK ≤ 4 * ε ^ 2 * O := by
    rw [div_mul_eq_mul_div, div_le_iff₀ he]
    nlinarith
  have s2 : ε * (P * n) ≤ ε * (O * (1 + 2 * ε)) := mul_le_mul_of_nonneg_left hge he.le
  have s3 : L * P ≤ ε * n * P := mul_le_mul_of_nonneg_right hL.le hP.le
  have hsplit : n * P = nK * P + nR * P := by rw [hnn]; ring
  have hsplit' : ε * n * P = ε * nK * P + ε * nR * P := by rw [hnn]; ring
  -- `2 |core| per ≤ (1 + ε) |C| per + (ε + 6ε²) cost_OPT`
  have s4 : 2 * (nK * P) ≤ (1 + ε) * (n * P) + (ε + 6 * ε ^ 2) * O := by nlinarith
  -- `(ε + 6ε²) cost_OPT ≤ 2ε |C| per`
  have hq : (1 + 6 * ε) * (1 + ε) ≤ 178 / 100 := by nlinarith
  have s5a : (ε + 6 * ε ^ 2) * (O * (89 / 100)) ≤ (ε + 6 * ε ^ 2) * ((1 + ε) * P * n) :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  have s5b : ε * ((1 + 6 * ε) * (1 + ε)) * (n * P) ≤ ε * (178 / 100) * (n * P) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq he.le) hnP.le
  have s5 : (ε + 6 * ε ^ 2) * O ≤ 2 * ε * (n * P) := by nlinarith
  -- `|C \ core| per ≥ (1 - 3ε)/2 |C| per`
  have s6 : (1 - 3 * ε) / 2 * (n * P) ≤ nR * P := by nlinarith
  have s7 : κ * ((1 - 3 * ε) / 2 * (n * P)) ≤ κ * (nR * P) := mul_le_mul_of_nonneg_left s6 hκ0
  have s8 : ε * κ * (n * P) ≤ ε * (n * P) :=
    mul_le_mul_of_nonneg_right (by nlinarith) hnP.le
  have s9 : ε * (ε * O) ≤ 1 / 200 * (ε * O) :=
    mul_le_mul_of_nonneg_right he'.le (by positivity)
  have s10 : 0 < ε * O := mul_pos he hOp
  nlinarith

namespace Hyp

variable {X : Ctx} (H : Hyp X)
include H

/-- **Optimality of `O` against one swap**: replacing `c* ∈ O` by any facility `c'` (all clients
of `C*` served by `c'`, the others keeping their center) does not help:
`cost_OPT(C*) ≤ ∑_{j ∈ C*} d(j, c')`. -/
private theorem costO_le_swap {c : Fin X.I.m} (hc : c ∈ X.O) (c' : Fin X.I.m) :
    X.costO c ≤ ∑ j ∈ X.C c, X.dist j c' := by
  classical
  have hO := H.O_nonempty
  have hTk : (insert c' (X.O.erase c)).card ≤ X.I.k := by
    calc (insert c' (X.O.erase c)).card ≤ (X.O.erase c).card + 1 := card_insert_le _ _
      _ = X.O.card := card_erase_add_one hc
      _ = X.I.k := H.isOpt.card
  have hle := H.isOpt.le_costF (insert_nonempty _ _) hTk
  unfold Instance.costF at hle
  rw [← sum_add_sum_compl (X.C c), ← sum_add_sum_compl (X.C c)
    (fun j ↦ X.I.dSet (.inl j) (insert c' (X.O.erase c)))] at hle
  have h1 : ∑ j ∈ (X.C c)ᶜ, X.I.dSet (.inl j) (insert c' (X.O.erase c)) ≤
      ∑ j ∈ (X.C c)ᶜ, X.I.dSet (.inl j) X.O := by
    refine sum_le_sum fun j hj ↦ ?_
    have hne : X.I.near X.O hO (.inl j) ≠ c := fun h ↦
      (mem_compl.1 hj) ((Instance.mem_cluster hO).2 h)
    have hmem : X.I.near X.O hO (.inl j) ∈ insert c' (X.O.erase c) :=
      mem_insert_of_mem (mem_erase.2 ⟨hne, Instance.near_mem hO _⟩)
    rw [← Instance.dd_near hO]
    exact Instance.dSet_le hmem _
  have h2 : ∑ j ∈ X.C c, X.I.dSet (.inl j) (insert c' (X.O.erase c)) ≤
      ∑ j ∈ X.C c, X.dist j c' :=
    sum_le_sum fun j _ ↦ Instance.dSet_le (mem_insert_self _ _) _
  have h3 : ∑ j ∈ X.C c, X.I.dSet (.inl j) X.O = X.costO c :=
    sum_congr rfl fun j hj ↦ Instance.dSet_of_mem_cluster hj
  linarith

/-- `no_dense_cores`, one client of the core: if all satellites are within `ε per` of each
other, then `d(j, c') ≤ ε per + (4/ε) d(j, S)` for the satellite `c'` near `c*`. -/
private theorem dist_core_le {c c' : Fin X.I.m} (hc : X.IsFar c) (hc' : c' ∈ X.Gam c)
    (hcc' : X.dF c c' ≤ (1 + X.ε) * X.per c)
    (hcon : ∀ c₁ ∈ X.Gam c, ∀ c₂ ∈ X.Gam c, X.dF c₁ c₂ < X.ε * X.per c)
    {j : Fin X.I.n} (hj : j ∈ X.core (X.kap c) c) :
    X.dist j c' ≤ X.ε * X.per c + 4 / X.ε * X.I.dSet (.inl j) X.S := by
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  have hP := hc.per_pos
  have hκ := kappa_mem (X.xr c)
  obtain ⟨hjC, hjd⟩ := mem_filter.1 hj
  change X.I.dd (.inl j) (.inr c) ≤ (1 + X.kap c) * X.per c at hjd
  have hd0 := Instance.dSet_nonneg hv (.inl j) X.S
  have h4 : X.I.dSet (.inl j) X.S ≤ 4 / X.ε * X.I.dSet (.inl j) X.S := by
    have : (1 : ℝ) ≤ 4 / X.ε := by rw [le_div_iff₀ he]; linarith
    nlinarith
  have h6 : 0 ≤ X.ε * X.per c := by positivity
  unfold Ctx.dist
  by_cases hsmall : X.I.dSet (.inl j) X.S ≤ X.ε * X.per c
  · obtain ⟨c₀, hc₀S, hc₀⟩ := Instance.exists_dSet_eq H.S_nonempty (.inl j)
    have hc₀Γ : c₀ ∈ X.Gam c := by
      simp only [Ctx.Gam, mem_filter]
      refine ⟨hc₀S, ?_, j, hjC, ?_⟩
      · have := Instance.dd_triangle hv (.inr c₀) (.inl j) (.inr c)
        rw [Instance.dd_comm hv (.inr c₀) (.inl j)] at this
        unfold Ctx.dF
        linarith
      · unfold Ctx.dist
        linarith
    have h1 := hcon c₀ hc₀Γ c' hc'
    have := Instance.dd_triangle hv (.inl j) (.inr c₀) (.inr c')
    unfold Ctx.dF at h1
    linarith
  · push Not at hsmall
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr c')
    unfold Ctx.dF at hcc'
    have h5 : 4 * X.per c ≤ 4 / X.ε * X.I.dSet (.inl j) X.S := by
      rw [div_mul_eq_mul_div, le_div_iff₀ he]
      linarith
    have m1 : X.kap c * X.per c ≤ 23 / 65 * X.per c := mul_le_mul_of_nonneg_right hκ.2 hP.le
    have m2 : X.ε * X.per c ≤ 1 / 200 * X.per c := mul_le_mul_of_nonneg_right he'.le hP.le
    unfold Ctx.kap at m1 hjd
    linarith

/-- **No dense cores** ([BCFGJPSSV26b, Lemma 4.5]): the satellites of a cluster of `O₂` have
diameter at least `ε per`. -/
theorem no_dense_cores {c : Fin X.I.m} (hc : X.IsFar c) :
    ∃ c₁ ∈ X.Gam c, ∃ c₂ ∈ X.Gam c, X.ε * X.per c ≤ X.dF c₁ c₂ := by
  by_contra hcon
  push Not at hcon
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  obtain ⟨c', hc', hcc', -⟩ := hc.near_sat
  have hP := hc.per_pos
  have hκ : 12 / 65 ≤ X.kap c ∧ X.kap c ≤ 23 / 65 := kappa_mem _
  have hpos := hc.costO_pos
  have hC : (X.C c).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    simp [Ctx.costO, costAt, h] at hpos
  have hn : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
  obtain ⟨R, hR⟩ : ∃ R, R = (X.C c).filter
      (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) ≤ (1 + X.kap c) * X.per c) := ⟨_, rfl⟩
  have hK : X.core (X.kap c) c =
      (X.C c).filter (fun j ↦ X.I.dd (.inl j) (.inr c) ≤ (1 + X.kap c) * X.per c) := rfl
  have hsplit : ∀ f : Fin X.I.n → ℝ, ∑ j ∈ X.C c, f j =
      ∑ j ∈ X.core (X.kap c) c, f j + ∑ j ∈ R, f j := by
    intro f
    rw [hK, hR]
    exact (sum_filter_add_sum_filter_not _ _ _).symm
  have hcard : ((X.C c).card : ℝ) = (X.core (X.kap c) c).card + R.card := by
    rw [hK, hR]
    exact_mod_cast (card_filter_add_card_filter_not _).symm
  -- optimality of `O` against the swap `c* → c'`
  have hopt := H.costO_le_swap hc.mem c'
  rw [hsplit] at hopt
  have hKs : ∑ j ∈ X.core (X.kap c) c, X.dist j c' ≤
      (X.core (X.kap c) c).card * (X.ε * X.per c) +
        4 / X.ε * X.costS (X.core (X.kap c) c) := by
    calc ∑ j ∈ X.core (X.kap c) c, X.dist j c'
        ≤ ∑ j ∈ X.core (X.kap c) c, (X.ε * X.per c + 4 / X.ε * X.I.dSet (.inl j) X.S) :=
          sum_le_sum fun j hj ↦ H.dist_core_le hc hc' hcc' hcon hj
      _ = _ := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
          rfl
  have hRs : ∑ j ∈ R, X.dist j c' ≤
      ∑ j ∈ R, X.I.dd (.inl j) (.inr c) + R.card * ((1 + X.ε) * X.per c) := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    have := Instance.dd_triangle hv (.inl j) (.inr c) (.inr c')
    unfold Ctx.dF at hcc'
    unfold Ctx.dist
    linarith
  -- the clients of the core at distance `≥ per`
  have hKl : ((X.core (X.kap c) c).card -
      ((X.C c).filter fun j ↦ X.I.dd (.inl j) (.inr c) < X.per c).card) * X.per c ≤
        ∑ j ∈ X.core (X.kap c) c, X.I.dd (.inl j) (.inr c) := by
    have h1 : ∑ j ∈ X.core (X.kap c) c,
        (X.per c - if X.I.dd (.inl j) (.inr c) < X.per c then X.per c else 0) ≤
          ∑ j ∈ X.core (X.kap c) c, X.I.dd (.inl j) (.inr c) := by
      refine sum_le_sum fun j _ ↦ ?_
      split_ifs with h
      · rw [sub_self]
        exact Instance.dd_nonneg hv _ _
      · linarith [not_lt.1 h]
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul] at h1
    have h2 : (((X.core (X.kap c) c).filter
        fun j ↦ X.I.dd (.inl j) (.inr c) < X.per c).card : ℝ) ≤
          ((X.C c).filter fun j ↦ X.I.dd (.inl j) (.inr c) < X.per c).card := by
      exact_mod_cast card_le_card (filter_subset_filter _ (core_subset _ _ _ _))
    nlinarith
  have hRl : R.card * ((1 + X.kap c) * X.per c) ≤ ∑ j ∈ R, X.I.dd (.inl j) (.inr c) := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun j hj ↦ ?_
    rw [hR, mem_filter] at hj
    exact (not_le.1 hj.2).le
  have hL : (((X.C c).filter fun j ↦ X.I.dd (.inl j) (.inr c) < X.per c).card : ℝ) <
      X.ε * (X.C c).card := per_count_lt he (by linarith) hC c
  have hO : X.costO c = ∑ j ∈ X.core (X.kap c) c, X.I.dd (.inl j) (.inr c) +
      ∑ j ∈ R, X.I.dd (.inl j) (.inr c) := hsplit _
  have hle : X.costO c * eta ≤ (1 + X.ε) * X.per c * (X.C c).card := by
    have := hc.avg_le
    rwa [Ctx.avgO, div_le_div_iff₀ hn (by unfold eta; norm_num)] at this
  have hge : X.per c * (X.C c).card ≤ X.costO c * (1 + 2 * X.ε) := by
    have := hc.avg_ge
    rwa [Ctx.avgO, div_le_div_iff₀ (by linarith) hn] at this
  have havg : 0 < X.avgO c := div_pos hpos hn
  have hxr : X.xr c = X.per c / X.avgO c := by
    unfold Ctx.xr xRatio
    exact if_neg havg.ne'
  have htech : (2 + 6 * X.ε) * X.costO c ≤ (2 + X.kap c) * ((X.C c).card * X.per c) := by
    have hx : eta / (1 + X.ε) ≤ X.xr c := by
      rw [hxr, div_le_div_iff₀ (by linarith) havg]
      have := hc.avg_le
      rw [le_div_iff₀ (by unfold eta; norm_num)] at this
      linarith
    have h : 2 + 6 * X.ε ≤ (2 + X.kap c) * X.xr c := technical he.le he' hx
    rw [hxr, mul_div_assoc', le_div_iff₀ havg] at h
    have h2 : X.costO c = X.avgO c * (X.C c).card := by
      unfold Ctx.avgO
      field_simp
    rw [h2]
    nlinarith
  unfold eta at hle
  exact sat1_arith he he' (by linarith) (by linarith) hP hn hcard hL hKl hRl hO
    (by linarith) hc.core_cheap hle hge htech

/-- One direction of `comparable_per`: `per(C*)/3 ≤ per(C₁*)`. -/
private theorem per_div_three_le {c c₁ c'' : Fin X.I.m} (hc : X.IsFar c) (hc₁ : X.IsFar c₁)
    (h : c'' ∈ X.GamE c) (h₁ : c'' ∈ X.GamE c₁) : X.per c / 3 ≤ X.per c₁ := by
  have hv := H.valid
  have he := H.eps_pos
  have he' := H.eps_lt
  by_contra hlt
  push Not at hlt
  simp only [Ctx.GamE, mem_filter] at h h₁
  obtain ⟨hS, -, p, hp, hpd⟩ := h
  obtain ⟨-, hd₁, -⟩ := h₁
  have hpc : X.I.dd (.inl p) (.inr c) ≤ X.I.dd (.inl p) (.inr c₁) := by
    rw [← Instance.dSet_of_mem_cluster hp]
    exact Instance.dSet_le hc₁.mem _
  have hOS : X.dOS c ≤ X.dF c c'' := Instance.dSet_le hS _
  have ht1 := Instance.dd_triangle hv (.inr c) (.inl p) (.inr c'')
  rw [Instance.dd_comm hv (.inr c) (.inl p)] at ht1
  have ht2 := Instance.dd_triangle hv (.inl p) (.inr c'') (.inr c₁)
  have hfar := hc.far
  have hag := hc.avg_ge
  have hP := hc.per_pos
  have hP1 : 0 ≤ X.per c₁ := hc₁.per_pos.le
  have hκ1 := kappa_mem (X.xr c₁)
  have havgS : 0 ≤ X.avgS c := div_nonneg (Instance.costOn_nonneg hv _ _) (Nat.cast_nonneg _)
  have havgO : 0 ≤ X.avgO c := div_nonneg (sum_nonneg fun _ _ ↦ Instance.dd_nonneg hv _ _)
    (Nat.cast_nonneg _)
  rw [div_le_iff₀ (by linarith)] at hag
  have heta : eta = 89 / 100 := rfl
  rw [heta] at hfar
  unfold Ctx.dF at hOS hd₁
  unfold Ctx.dist at hpd
  unfold Ctx.kap at hd₁
  have m1 : X.kap c₁ * X.per c₁ ≤ 23 / 65 * X.per c₁ := mul_le_mul_of_nonneg_right hκ1.2 hP1
  have m2 : X.ε * X.per c₁ ≤ 1 / 200 * X.per c₁ := mul_le_mul_of_nonneg_right he'.le hP1
  have m3 : X.ε * X.per c ≤ 1 / 200 * X.per c := mul_le_mul_of_nonneg_right he'.le hP.le
  have m4 : X.ε * X.avgO c ≤ 1 / 200 * X.avgO c := mul_le_mul_of_nonneg_right he'.le havgO
  have m5 : 0 ≤ X.ε * X.avgS c := mul_nonneg he.le havgS
  unfold Ctx.kap at m1
  linarith

/-- **Comparable percentiles**: clusters of `O₂` with a common loose satellite have
percentiles within a factor `3`. -/
theorem comparable_per {c c₁ : Fin X.I.m} (hc : X.IsFar c) (hc₁ : X.IsFar c₁)
    (h : (X.GamE c ∩ X.GamE c₁).Nonempty) : X.per c / 3 ≤ X.per c₁ ∧ X.per c₁ ≤ 3 * X.per c := by
  obtain ⟨c'', hc''⟩ := h
  obtain ⟨h1, h2⟩ := mem_inter.1 hc''
  refine ⟨H.per_div_three_le hc hc₁ h1 h2, ?_⟩
  have := H.per_div_three_le hc₁ hc h2 h1
  linarith

end Hyp

end BCFGJPSSV26.Stable


