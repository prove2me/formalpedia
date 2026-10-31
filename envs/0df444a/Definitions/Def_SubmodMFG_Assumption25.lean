-- Prove2me | Definitions.Def_SubmodMFG_Assumption25
-- name    : SubmodMFG_Assumption25
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:02.956114+00:00
-- url     : https://prove2.me/theorems/c8c89e5e-314e-4827-8ef4-966f5abe677f
-- title:
--   Assumption 2.5 — continuity requirements for the learning procedure
-- statement:
--   **Assumption 2.5.**
--
--   1. For any sequence $(\nu^n)_n$ with each $\nu^n\in\arg\min_E J(\cdot,\mu_n)$ for some $\mu_n\in L$, such that $p(\nu^n)$ is increasing (resp. decreasing) in $L$, there exist a subsequence $(n_j)_{j\in\mathbb N}$ and $\nu\in E$ such that $\nu^{n_j}\to\nu$ and $p\nu=\sup_j p(\nu^{n_j})$ (resp. $p\nu=\inf_j p(\nu^{n_j})$).
--   2. For any nondecreasing (resp. nonincreasing) sequence $(\mu^n)_n\subseteq L$:
--      - for every $\nu\in E$, $J(\nu,\sup_n\mu^n)=\lim_n J(\nu,\mu^n)$ (resp. $J(\nu,\inf_n\mu^n)=\lim_n J(\nu,\mu^n)$);
--      - for every sequence $\nu^n\to\nu$ in $E$,
--   $$
--   J(\nu,\sup_n\mu^n)\le\liminf_n J(\nu^n,\mu^n)\qquad(\text{resp. } J(\nu,\inf_n\mu^n)\le\liminf_n J(\nu^n,\mu^n)).
--   $$
--
--   These continuity requirements let the learning procedures of Theorem 2.6 b), c) pass to the limit.
--
--   **Formalization Note** The first condition is required only for **strictly** increasing (resp. strictly decreasing) $p(\nu^n)$, the weaker of the two readings of "increasing", so every model satisfying the paper's assumption satisfies this one. The printed "$\sup_n\mu$" is $\sup_n\mu^n$. The $\liminf$ is taken in the extended reals $[-\infty,\infty]$ (Lean `EReal`), so it is $-\infty$ for a sequence unbounded below.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.3, Assumption 2.5, p.7

import Mathlib
import Definitions.Def_SubmodMFG_argminSet

namespace SubmodMFG

open Filter Topology

/-- **Assumption 2.5** (continuity requirements for the learning procedure).
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.3, Assumption 2.5, p.7: "For any sequence (νⁿ)ₙ ⊂ {arg min_E J(·, µ) | µ ∈ L}
such that p(νⁿ) is increasing or decreasing in L, there exists a subsequence (n_j)_{j∈ℕ} and
ν ∈ E such that ν^{n_j} converges to ν as j → ∞ and pν = sup_j p(ν^{n_j}) or
pν = inf_j p(ν^{n_j}), respectively.
Moreover, respectively, for any nondecreasing or nonincreasing sequence (µⁿ)ₙ ⊂ L, we assume that
(1) for any ν ∈ E, J(ν, sup_n µ) = lim_n J(ν, µⁿ) or J(ν, inf_n µ) = lim_n J(ν, µⁿ)),
(2) for any sequence (νⁿ)ₙ ⊂ E converging to ν ∈ E, we have that J(ν, sup_n µ) ≤
lim inf_n J(νⁿ, µⁿ) or J(ν, inf_n µ) ≤ lim inf_n J(νⁿ, µⁿ)."

Fields: `seq_up`/`seq_down` are the first sentence (increasing ↔ sup, decreasing ↔ inf);
`cont_up`/`cont_down` are (1) and `liminf_up`/`liminf_down` are (2), for nondecreasing (sup) and
nonincreasing (inf) sequences `(µⁿ)` respectively.

**Formalization Note.**
* "(νⁿ)ₙ ⊂ {arg min_E J(·, µ) | µ ∈ L}" is read as: every `νⁿ` minimizes `J(·, µ)` for some
  `µ ∈ L` (possibly depending on `n`), i.e. the sequence lies in the union of the argmin sets.
* In the first sentence the hypothesis is only required for **strictly** increasing
  (`StrictMono`) resp. strictly decreasing (`StrictAnti`) `p(νⁿ)`. This is the weaker of the two
  readings of "increasing" (it is implied by the nondecreasing reading), so every family
  satisfying the paper's assumption satisfies this one.
* "sup_n µ" is `⨆ n, µ n` (the printed `µ` stands for `µⁿ`); "lim_n" in (1) is convergence in
  `ℝ`; "lim inf" in (2) is taken in `EReal` (`Filter.liminf` of the coerced sequence), so a
  sequence unbounded below has `lim inf = −∞` as in the paper rather than Mathlib's junk value
  for real `liminf`.
* `J` is curried (`J ν µ = J(ν, µ)`), subsequences are `ν ∘ φ` with `StrictMono φ`, and
  convergence in `E` is `Tendsto … atTop (𝓝 ν)`. -/
structure Assumption25 {E L : Type*} [TopologicalSpace E] [CompleteLattice L]
    (p : E → L) (J : E → L → ℝ) : Prop where
  /-- First sentence, increasing case. -/
  seq_up : ∀ ν : ℕ → E, (∀ n, ∃ μ : L, ν n ∈ argminSet J μ) → StrictMono (fun n => p (ν n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν₀ : E,
      Tendsto (fun j => ν (φ j)) atTop (𝓝 ν₀) ∧ p ν₀ = ⨆ j, p (ν (φ j))
  /-- First sentence, decreasing case. -/
  seq_down : ∀ ν : ℕ → E, (∀ n, ∃ μ : L, ν n ∈ argminSet J μ) → StrictAnti (fun n => p (ν n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν₀ : E,
      Tendsto (fun j => ν (φ j)) atTop (𝓝 ν₀) ∧ p ν₀ = ⨅ j, p (ν (φ j))
  /-- (1), nondecreasing case. -/
  cont_up : ∀ μ : ℕ → L, Monotone μ → ∀ ν : E,
    Tendsto (fun n => J ν (μ n)) atTop (𝓝 (J ν (⨆ n, μ n)))
  /-- (1), nonincreasing case. -/
  cont_down : ∀ μ : ℕ → L, Antitone μ → ∀ ν : E,
    Tendsto (fun n => J ν (μ n)) atTop (𝓝 (J ν (⨅ n, μ n)))
  /-- (2), nondecreasing case. -/
  liminf_up : ∀ μ : ℕ → L, Monotone μ → ∀ (ν : ℕ → E) (ν₀ : E),
    Tendsto ν atTop (𝓝 ν₀) →
      ((J ν₀ (⨆ n, μ n) : ℝ) : EReal) ≤ liminf (fun n => ((J (ν n) (μ n) : ℝ) : EReal)) atTop
  /-- (2), nonincreasing case. -/
  liminf_down : ∀ μ : ℕ → L, Antitone μ → ∀ (ν : ℕ → E) (ν₀ : E),
    Tendsto ν atTop (𝓝 ν₀) →
      ((J ν₀ (⨅ n, μ n) : ℝ) : EReal) ≤ liminf (fun n => ((J (ν n) (μ n) : ℝ) : EReal)) atTop

end SubmodMFG


