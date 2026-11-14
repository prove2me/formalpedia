-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_LMP
-- name    : BCFGJPSSV26_Greedy_LMP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:48:35.093498+00:00
-- url     : https://prove2.me/theorems/8bf449dc-6b6a-4599-8034-4c3ec73f1bcc
-- title:
--   BCFGJPSSV26.Greedy.LMP — The robust LMP guarantee
-- statement:
--   This is module `BCFGJPSSV26.Greedy.LMP` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26a, Theorem D.7], in linear form (`BCFGJPSSV26.Greedy.robust_lmp`): for an
--   `η`-valid solution `H` with opening cost `f > n η` and every nonempty set `O` of facilities,
--   `(1 - δ) connCost H + |H_reg| f ≤ (ρ + 6δ) cost(O) + |O| f + |H_reg| n η`.
--   The bound is stated without dividing by `OPT - |S_reg| f`, which may be negative by up to
--   `|S_reg| n η`.
--
--   * `BCFGJPSSV26.Greedy.Run.Cost j`: what client `j` pays after it becomes inactive, plus
--     `(1 - δ) d(j, S⋆)`.
--   * `BCFGJPSSV26.Greedy.Run.cost_split` ([BCFGJPSSV26a, Lemma E.9]): the opening and connection
--     costs are paid by the clients.
--   * `BCFGJPSSV26.Greedy.Run.cost_le_alpha`: a client pays at most `α*_j` (chain lemma).
--   * `BCFGJPSSV26.Greedy.Run.cost_le_frp` ([BCFGJPSSV26a, Lemma E.12], client by client
--     `BCFGJPSSV26.Greedy.Run.cost_le_term`) and
--     `BCFGJPSSV26.Greedy.Run.dgood_cost` ([BCFGJPSSV26a, Lemma E.17]): the clients of `Dg` pay at most
--     `f + (ρ + 6δ) ∑_{Dg} d(j, i⋆)`, by the bound on the factor-revealing program.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.robust_lmp` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_LMP`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/LMP.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Embed

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.LMP` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The robust LMP guarantee

[BCFGJPSSV26a, Theorem D.7], in linear form (`BCFGJPSSV26.Greedy.robust_lmp`): for an
`η`-valid solution `H` with opening cost `f > n η` and every nonempty set `O` of facilities,
`(1 - δ) connCost H + |H_reg| f ≤ (ρ + 6δ) cost(O) + |O| f + |H_reg| n η`.
The bound is stated without dividing by `OPT - |S_reg| f`, which may be negative by up to
`|S_reg| n η`.

* `BCFGJPSSV26.Greedy.Run.Cost j`: what client `j` pays after it becomes inactive, plus
  `(1 - δ) d(j, S⋆)`.
* `BCFGJPSSV26.Greedy.Run.cost_split` ([BCFGJPSSV26a, Lemma E.9]): the opening and connection
  costs are paid by the clients.
* `BCFGJPSSV26.Greedy.Run.cost_le_alpha`: a client pays at most `α*_j` (chain lemma).
* `BCFGJPSSV26.Greedy.Run.cost_le_frp` ([BCFGJPSSV26a, Lemma E.12], client by client
  `BCFGJPSSV26.Greedy.Run.cost_le_term`) and
  `BCFGJPSSV26.Greedy.Run.dgood_cost` ([BCFGJPSSV26a, Lemma E.17]): the clients of `Dg` pay at most
  `f + (ρ + 6δ) ∑_{Dg} d(j, i⋆)`, by the bound on the factor-revealing program.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Run

variable {n m : ℕ} (R : Run n m)

/-- What client `j` pays from the step at which it becomes inactive on, plus
`(1 - δ) d(j, S⋆)`. -/
noncomputable def Cost (j : Fin n) : ℚ :=
  ∑ s ∈ Ico (R.σ j) R.len, R.contrib j s + R.Xv j R.len

/-- **[BCFGJPSSV26a, Lemma E.9]**: the clients pay for the regular facilities (up to `n η` each)
and for `(1 - δ)` times their connection cost. -/
theorem cost_split :
    (nReg R.H : ℚ) * (R.f - n * R.P.η) + (1 - R.P.δ) * connCost R.P R.X.d R.H ≤ ∑ j, R.Cost j := by
  classical
  have hc : ∀ j, ∑ s ∈ Ico (R.σ j) R.len, R.contrib j s = ∑ s ∈ range R.len, R.contrib j s := by
    intro j
    refine sum_subset (fun s hs ↦ ?_) (fun s hs hs' ↦ ?_)
    · rw [mem_Ico] at hs
      exact mem_range.2 hs.2
    · apply R.contrib_eq_zero
      rw [mem_Ico] at hs'
      rw [mem_range] at hs
      omega
  have hopen : (nReg R.H : ℚ) * (R.f - n * R.P.η) ≤ ∑ s ∈ range R.len, ∑ j, R.contrib j s := by
    rw [← R.card_regSteps]
    calc (((range R.len).filter R.IsReg).card : ℚ) * (R.f - n * R.P.η)
        = ∑ s ∈ (range R.len).filter R.IsReg, (R.f - n * R.P.η) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ s ∈ (range R.len).filter R.IsReg, ∑ j, R.contrib j s :=
          sum_le_sum fun s hs ↦
            R.sum_contrib_ge (mem_range.1 (mem_filter.1 hs).1) (mem_filter.1 hs).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun s _ _ ↦
          sum_nonneg fun j _ ↦ R.contrib_nonneg j s
  have hconn : (1 - R.P.δ) * connCost R.P R.X.d R.H = ∑ j, R.Xv j R.len := by
    unfold connCost
    rw [mul_sum]
    exact sum_congr rfl fun j _ ↦ (R.Xv_len j).symm
  unfold Cost
  rw [sum_add_distrib, ← hconn]
  simp only [hc]
  rw [sum_comm]
  linarith

/-- A client pays at most `α*_j`. -/
theorem cost_le_alpha (j : Fin n) : R.Cost j ≤ R.αs j := by
  have hσ := (R.σ_lt j).le
  have h1 : ∑ s ∈ Ico (R.σ j) R.len, R.contrib j s ≤
      ∑ s ∈ Ico (R.σ j) R.len, bid (R.Xv j s) (R.Xv j (s + 1)) := by
    refine sum_le_sum fun s hs ↦ ?_
    rw [mem_Ico] at hs
    exact (R.contrib_le hs.1 hs.2).trans (bid_mono_left (R.Zv_le_Xv hs.1 hs.2) _)
  have h2 := bid_chain hσ (fun s h1 h2 ↦ R.Xv_anti h1 h2) (R.Xv_nonneg j R.len)
  have h3 : R.Xv j (R.σ j) = R.αs j := by simp [Xv]
  unfold Cost
  linarith

end Run

end BCFGJPSSV26.Greedy


