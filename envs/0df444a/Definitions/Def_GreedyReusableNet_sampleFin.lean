-- Prove2me | Definitions.Def_GreedyReusableNet_sampleFin
-- name    : GreedyReusableNet_sampleFin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:03.659232+00:00
-- url     : https://prove2.me/theorems/a6966061-809e-4956-88e3-d081a10cf732
-- title:
--   Inverse-CDF sampling from a finite distribution
-- statement:
--   Given a probability distribution $p$ on a finite set listed as $x_0,x_1,\dots$ and a seed $u$, the sample is the first $x_k$ of positive mass with $u<p(x_0)+\dots+p(x_k)$. If $u$ is uniform on $[0,1]$, the sample has law $p$. The few seeds with no such $x_k$ (a null set) return a fixed point of the support.
--
--   It realizes the activation draw "the nature draws an independent sample $\mathcal A^\pi_{t,\mathrm{act}}\subset\mathcal A^\pi_t$ from an activation probability distribution".
-- source:
--   Simchi-Levi, Zheng & Zhu, On Greedy-like Policies in Online Matching with Reusable Network Resources and Decaying Rewards, SSRN 3981123, §2.1, p.9

import Mathlib

namespace GreedyReusableNet

/-- **Sampling from a finite distribution by a uniform seed** (inverse-CDF sampling). The
outcomes are listed in the order of `Fintype.equivFin`; for a seed `u` the sample is the first
outcome `k` of positive mass whose cumulative mass `p(0) + ⋯ + p(k)` exceeds `u`. When `u` is
uniform on `[0, 1]` the sample has law `p` (the seeds for which no such outcome exists form a
null set; they return a fixed element of the support).

Used for the activation draw "the nature draws an independent sample `𝒜^π_{t,act} ⊂ 𝒜^π_t` from
an activation probability distribution" (Simchi-Levi, Zheng & Zhu, SSRN 3981123, §2.1, p.9). -/
noncomputable def sampleFin {α : Type*} [Fintype α] (p : PMF α) (u : ℝ) : α := by
  classical
  let e := Fintype.equivFin α
  let cdf : Fin (Fintype.card α) → ℝ := fun k =>
    ∑ j ∈ Finset.univ.filter (fun j : Fin (Fintype.card α) => j ≤ k), (p (e.symm j)).toReal
  let good := Finset.univ.filter (fun k : Fin (Fintype.card α) => p (e.symm k) ≠ 0 ∧ u < cdf k)
  exact if hg : good.Nonempty then e.symm (good.min' hg) else p.support_nonempty.choose

end GreedyReusableNet


