-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Final_Combine
-- name    : BCFGJPSSV26_Stable_Final_Combine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:12:43.900867+00:00
-- url     : https://prove2.me/theorems/daabb97c-35aa-45e7-b4c1-8b1e49229082
-- title:
--   BCFGJPSSV26.Stable.Final.Combine — The win-win combination
-- statement:
--   This is module `BCFGJPSSV26.Stable.Final.Combine` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   * [BCFGJPSSV26b, Section 3.5]: the `(a, 1 - a)` combination of the local
--     search bound `Ψ_LS` and the submodular bound `Ψ_T` is at most `(1 + η + 10 ε) opt`
--     (`BCFGJPSSV26.Stable.Partition.psi_combo`), cluster by cluster: each row is a multiple of
--     `cost_OPT(C*)` by `|C*| per = x cost_OPT(C*)` and
--     `cost_OPT(core_κ) + |core_κ| per = y_κ cost_OPT(C*)`, and the rows satisfy the win-win
--     inequalities (`BCFGJPSSV26.Stable.row_early`, `BCFGJPSSV26.Stable.row_late`,
--     `BCFGJPSSV26.Stable.row_R`). So the local search or the candidate of a good trial costs at most
--     `(1 + η + 100 ε) opt` (`BCFGJPSSV26.Stable.Partition.min_le_bound`).
--   * When `k = 1` or `opt = 0`, the local search alone costs at most
--     `(1.89 + 1000/N) opt` (`BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`): for `k = 1`, swapping
--     to an optimal center gives `(1 - 1/N) cost(S) ≤ opt`; for `opt = 0`, `cost(S) ≤ 4 opt = 0`.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Partition.min_le_bound`, `BCFGJPSSV26.Stable.Partition.psi_combo`, `BCFGJPSSV26.Stable.costF_le_bound_of_degenerate` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Final_Combine`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Final/Combine.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_LSBound_NiceMaps
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
public import Definitions.Def_BCFGJPSSV26_Stable_WinWin

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Final.Combine` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The win-win combination

* [BCFGJPSSV26b, Section 3.5]: the `(a, 1 - a)` combination of the local
  search bound `Ψ_LS` and the submodular bound `Ψ_T` is at most `(1 + η + 10 ε) opt`
  (`BCFGJPSSV26.Stable.Partition.psi_combo`), cluster by cluster: each row is a multiple of
  `cost_OPT(C*)` by `|C*| per = x cost_OPT(C*)` and
  `cost_OPT(core_κ) + |core_κ| per = y_κ cost_OPT(C*)`, and the rows satisfy the win-win
  inequalities (`BCFGJPSSV26.Stable.row_early`, `BCFGJPSSV26.Stable.row_late`,
  `BCFGJPSSV26.Stable.row_R`). So the local search or the candidate of a good trial costs at most
  `(1 + η + 100 ε) opt` (`BCFGJPSSV26.Stable.Partition.min_le_bound`).
* When `k = 1` or `opt = 0`, the local search alone costs at most
  `(1.89 + 1000/N) opt` (`BCFGJPSSV26.Stable.costF_le_bound_of_degenerate`): for `k = 1`, swapping
  to an optimal center gives `(1 - 1/N) cost(S) ≤ opt`; for `opt = 0`, `cost(S) ≤ 4 opt = 0`.
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

/-- The ratio `x = per/avg_OPT` of a cluster: `0 ≤ x ≤ 1 + 2ε` and `|C*| per = x cost_OPT(C*)`. -/
private theorem Hyp.xr_spec {X : Ctx} (H : Hyp X) (c : Fin X.I.m) :
    0 ≤ X.xr c ∧ X.xr c ≤ 1 + 2 * X.ε ∧ (X.C c).card * X.per c = X.xr c * X.costO c := by
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hp : 0 ≤ X.per c := per_nonneg H.valid _ _ _
  have hA : 0 ≤ X.costO c := sum_nonneg fun _ _ ↦ Instance.dd_nonneg H.valid _ _
  rcases (X.C c).eq_empty_or_nonempty with hC | hC
  · have hA0 : X.costO c = 0 := by rw [Ctx.costO, costAt, hC, sum_empty]
    have havg : X.avgO c = 0 := by rw [Ctx.avgO, hA0, zero_div]
    unfold Ctx.xr xRatio
    rw [if_pos havg, hC, card_empty, hA0]
    refine ⟨zero_le_one, by linarith, by simp⟩
  · have hle : X.per c ≤ (1 + 2 * X.ε) * X.avgO c :=
      per_le_avg H.valid hε (by linarith) hC c
    have hn : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
    have havg0 : 0 ≤ X.avgO c := div_nonneg hA hn.le
    have hAn : X.costO c = X.avgO c * (X.C c).card := by
      rw [Ctx.avgO]
      field_simp
    unfold Ctx.xr xRatio
    by_cases havg : X.avgO c = 0
    · rw [if_pos havg]
      rw [havg, mul_zero] at hle
      have hp0 : X.per c = 0 := le_antisymm hle hp
      rw [hp0, hAn, havg]
      refine ⟨zero_le_one, by linarith, by ring⟩
    · rw [if_neg havg]
      have hpos : 0 < X.avgO c := lt_of_le_of_ne havg0 (Ne.symm havg)
      refine ⟨div_nonneg hp hpos.le, (div_le_iff₀ hpos).2 hle, ?_⟩
      rw [hAn]
      field_simp

/-- **The row of a far cluster** (`O_R`). -/
private theorem Hyp.rowR_le {X : Ctx} (H : Hyp X) {c : Fin X.I.m} (hc : X.IsFar c) :
    aW * (costAt X.I c (X.core (X.kap c) c) +
        2 * (X.costO c - costAt X.I c (X.core (X.kap c) c)) +
        ((X.C c).card - (X.core (X.kap c) c).card) * X.per c) +
      (1 - aW) * (X.costO c + (X.C c).card * X.per c) ≤
        (1 + eta + 10 * X.ε) * X.costO c := by
  classical
  have hε := H.eps_pos
  have hε' := H.eps_lt
  obtain ⟨hx0, hx1, hxA⟩ := H.xr_spec c
  have hA := hc.costO_pos
  have hp := hc.per_pos
  have hC : (X.C c).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro h
    have : X.costO c = 0 := by rw [Ctx.costO, costAt, h, sum_empty]
    linarith
  have hn : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
  have havg : 0 < X.avgO c := div_pos hA hn
  have hxavg : X.xr c * X.avgO c = X.per c := by
    unfold Ctx.xr xRatio
    rw [if_neg havg.ne', div_mul_cancel₀ _ havg.ne']
  -- `x ≥ η/(1 + ε)`
  have hx : eta / (1 + X.ε) ≤ X.xr c := by
    rw [div_le_iff₀ (by linarith)]
    have h1 := hc.avg_le
    have he : (0 : ℝ) < eta := by unfold eta; norm_num
    rw [le_div_iff₀ he] at h1
    have h2 : eta * X.avgO c ≤ X.xr c * (1 + X.ε) * X.avgO c := by nlinarith
    exact le_of_mul_le_mul_right (by linarith) havg
  -- the clients outside the core pay more than `(1 + κ) per`
  set κ := X.kap c with hκ
  set p := X.per c with hpdef
  set A := X.costO c with hAdef
  set D := X.core κ c with hD
  set cK := costAt X.I c D with hcK
  have hκ0 : 0 < κ := kappa_pos _
  have hDf : D = (X.C c).filter fun j ↦ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p := rfl
  have hsplit := sum_filter_add_sum_filter_not (X.C c)
    (fun j ↦ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p) fun j ↦ X.I.dd (.inl j) (.inr c)
  rw [← hDf] at hsplit
  have hcardsplit := card_filter_add_card_filter_not (s := X.C c)
    (fun j ↦ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p)
  rw [← hDf] at hcardsplit
  have hout : (1 + κ) * p * (((X.C c).card : ℝ) - D.card) ≤
      ∑ j ∈ (X.C c).filter (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p),
        X.I.dd (.inl j) (.inr c) := by
    have : ((X.C c).card : ℝ) - D.card =
        ((X.C c).filter (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p)).card := by
      rw [← hcardsplit]
      push_cast
      ring
    rw [this, mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun j hj ↦ ?_
    exact (not_le.1 (mem_filter.1 hj).2).le
  -- the core pays at least `per`, except fewer than `ε |C*|` clients
  have hcore : p * D.card - X.ε * (X.C c).card * p ≤ cK := by
    have hlt := per_count_lt (I := X.I) hε (by linarith) hC c
    have hsub : (D.filter fun j ↦ X.I.dd (.inl j) (.inr c) < p) ⊆
        (X.C c).filter fun j ↦ X.I.dd (.inl j) (.inr c) < p :=
      filter_subset_filter _ (core_subset _ _ _ _)
    have hle : ((D.filter fun j ↦ X.I.dd (.inl j) (.inr c) < p).card : ℝ) <
        X.ε * (X.C c).card :=
      lt_of_le_of_lt (by exact_mod_cast card_le_card hsub) hlt
    have hs2 := sum_filter_add_sum_filter_not D
      (fun j ↦ X.I.dd (.inl j) (.inr c) < p) fun j ↦ X.I.dd (.inl j) (.inr c)
    have hc2 := card_filter_add_card_filter_not (s := D)
      (fun j ↦ X.I.dd (.inl j) (.inr c) < p)
    have h1 : 0 ≤ ∑ j ∈ D.filter (fun j ↦ X.I.dd (.inl j) (.inr c) < p),
        X.I.dd (.inl j) (.inr c) := sum_nonneg fun _ _ ↦ Instance.dd_nonneg H.valid _ _
    have h2 : p * ((D.filter fun j ↦ ¬ X.I.dd (.inl j) (.inr c) < p).card : ℝ) ≤
        ∑ j ∈ D.filter (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) < p), X.I.dd (.inl j) (.inr c) := by
      rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun j hj ↦ not_lt.1 (mem_filter.1 hj).2
    have h3 : (D.card : ℝ) = (D.filter fun j ↦ X.I.dd (.inl j) (.inr c) < p).card +
        (D.filter fun j ↦ ¬ X.I.dd (.inl j) (.inr c) < p).card := by
      rw [← hc2]
      push_cast
      ring
    have h4 : cK = ∑ j ∈ D, X.I.dd (.inl j) (.inr c) := rfl
    rw [h4, ← hs2, h3]
    nlinarith
  -- the bound on `y_κ`
  have hy : 2 * ((1 + kappa (X.xr c)) * X.xr c - 1) / kappa (X.xr c) -
      X.ε * X.xr c * (1 + 2 / kappa (X.xr c)) ≤ (cK + D.card * p) / A := by
    change 2 * ((1 + κ) * X.xr c - 1) / κ - X.ε * X.xr c * (1 + 2 / κ) ≤ (cK + D.card * p) / A
    rw [le_div_iff₀ hA]
    have e : κ * ((2 * ((1 + κ) * X.xr c - 1) / κ - X.ε * X.xr c * (1 + 2 / κ)) * A) =
        2 * ((1 + κ) * (X.xr c * A) - A) - X.ε * (X.xr c * A) * (κ + 2) := by
      field_simp
    rw [← hxA] at e
    have hA' : A = cK + ∑ j ∈ (X.C c).filter
        (fun j ↦ ¬ X.I.dd (.inl j) (.inr c) ≤ (1 + κ) * p), X.I.dd (.inl j) (.inr c) := by
      exact hsplit.symm
    have hprod : 0 ≤ (2 + κ) * (cK - p * D.card + X.ε * (X.C c).card * p) :=
      mul_nonneg (by linarith) (by linarith)
    refine le_of_mul_le_mul_left ?_ hκ0
    rw [e]
    nlinarith
  have hR := row_R hε.le hε' hx hx1 hy
  have e2 : (cK + D.card * p) / A * A = cK + D.card * p := div_mul_cancel₀ _ hA.ne'
  have hR' := mul_le_mul_of_nonneg_right hR hA.le
  unfold aW at hR' ⊢
  nlinarith

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

/-- **The win-win combination of one row.** -/
private theorem row_combo (H : Hyp X) {c : Fin X.I.m} (hc : c ∈ X.O) :
    aW * Q.rowLS c + (1 - aW) * Q.rowT c ≤ (1 + eta + 10 * X.ε) * X.costO c := by
  obtain ⟨hx0, hx1, hxA⟩ := H.xr_spec c
  have hA : 0 ≤ X.costO c := sum_nonneg fun _ _ ↦ Instance.dd_nonneg H.valid _ _
  have hε := H.eps_pos
  have hε' := H.eps_lt
  have hεA : 0 ≤ X.ε * X.costO c := mul_nonneg hε.le hA
  unfold rowLS rowT
  by_cases h1 : c ∈ X.OSall w₁.OL
  · rw [if_pos h1, if_pos h1]
    unfold aW
    nlinarith
  rw [if_neg h1, if_neg h1]
  by_cases h2 : c ∈ w₁.OLe
  · rw [if_pos h2, if_pos h2, hxA]
    have h := mul_le_mul_of_nonneg_right (row_early hε.le hε' hx0 hx1) hA
    have e : aW * (3 * X.costO c) + (1 - aW) * (X.costO c + 2 / Real.exp 1 *
        (X.xr c * X.costO c)) = (aW * 3 + (1 - aW) * (1 + 2 * X.xr c / Real.exp 1)) *
          X.costO c := by ring
    rw [e]
    nlinarith
  rw [if_neg h2, if_neg h2]
  by_cases h3 : c ∈ Q.OLam ∪ Q.OP
  · rw [if_pos h3, if_pos h3, hxA]
    have h := mul_le_mul_of_nonneg_right (row_late hε.le hε' hx0 hx1) hA
    have e : aW * (X.costO c + X.xr c * X.costO c) + (1 - aW) * (X.costO c + 2 / Real.exp 1 *
        ((1 + X.kap c) * (X.xr c * X.costO c))) = (aW * (1 + X.xr c) + (1 - aW) *
          (1 + 2 * (1 + kappa (X.xr c)) * X.xr c / Real.exp 1)) * X.costO c := by
      simp only [Ctx.kap]
      ring
    rw [e]
    nlinarith
  rw [if_neg h3, if_neg h3]
  have hR : c ∈ Q.OR := by
    obtain ⟨hcov, -⟩ := Q.cover H
    rw [← hcov] at hc
    simp only [mem_union] at hc h3
    tauto
  exact H.rowR_le (Q.far_R c hR)

end Partition

end BCFGJPSSV26.Stable


