-- Prove2me | Definitions.Def_TIESharp_bsCol
-- name    : TIESharp_bsCol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:59.017264+00:00
-- url     : https://prove2.me/theorems/55340d22-e4e0-4508-bdaf-446cbe5a813a
-- title:
--   Bounded-Square probabilities of one job
-- statement:
--   Let $c=(c_1,\dots,c_n)\in[0,\infty)^n$ be one job's column of processing times and $\mu=\min_k c_k$. If $\mu>0$, the **eligible machines** are $S=\{i: c_i\le 2\mu\}$ and the **Bounded-Square** probabilities are
--   $$q_i=\frac{\mathbf 1\{i\in S\}\,c_i^{-2}}{\sum_{k\in S}c_k^{-2}}.$$
--   If $\mu=0$ (a zero-minimum job), the job is allocated uniformly among its zero-cost machines, $q_i=\mathbf 1\{c_i=0\}/\#\{k:c_k=0\}$. This is Lu and Yu's truncation of the inverse-square rule.
--
--   **Formalization Note.** The zero-minimum case is decided first, so inverse squares are only formed when every $c_k\ge\mu>0$. The minimum is `⨅` over the nonempty finite set of machines ($n\ge1$).
-- source:
--   Li, Sharp Bounds for Truthful-in-Expectation Scheduling, arXiv:2611.05134 (held version, sha256 e611c390…b70e5481), §3.2, p.10

import Mathlib

set_option autoImplicit false

namespace TIESharp

/-- The **Bounded-Square probabilities** of one job (Li, *Sharp Bounds for
Truthful-in-Expectation Scheduling*, arXiv:2611.05134, §3.2, p.10). For a job with column
`c = (c_1, …, c_n)` of processing times and positive minimum `μ = min_k c_k > 0`, the eligible
machines are `S = {i : c_i ≤ 2μ}` and
`q_i = 1{i ∈ S} c_i^{-2} / Σ_{k ∈ S} c_k^{-2}`.
"For a zero-minimum job, allocate uniformly among its zero-cost machines":
`q_i = 1{c_i = 0} / #{k : c_k = 0}` when `μ = 0`.

**Formalization Note.** `μ` is `⨅ k, c k`, a genuine minimum over the finite nonempty machine set
(`n ≥ 1`). The zero-minimum branch is decided first, so the inverse squares are only taken in the
branch `μ ≠ 0`, where for a nonnegative column every `c_k ≥ μ > 0`. Values on columns with a
negative entry are irrelevant. -/
noncomputable def bsCol {n : ℕ} (c : Fin n → ℝ) (i : Fin n) : ℝ :=
  if (⨅ k, c k) = 0 then
    (if c i = 0 then 1 else 0) / ((Finset.univ.filter (fun k => c k = 0)).card : ℝ)
  else
    (if c i ≤ 2 * ⨅ k, c k then (c i)⁻¹ ^ 2 else 0) /
      ∑ k ∈ Finset.univ.filter (fun k => c k ≤ 2 * ⨅ k', c k'), (c k)⁻¹ ^ 2

end TIESharp


