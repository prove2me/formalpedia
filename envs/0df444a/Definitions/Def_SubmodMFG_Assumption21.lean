-- Prove2me | Definitions.Def_SubmodMFG_Assumption21
-- name    : SubmodMFG_Assumption21
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:05.085205+00:00
-- url     : https://prove2.me/theorems/63adfe3a-1e7c-45ba-9b19-711651966bd8
-- title:
--   Assumption 2.1 — minimizers exist and are closed along monotone sequences
-- statement:
--   **Assumption 2.1.** For every $\mu\in L$:
--
--   1. the set $\arg\min_E J(\cdot,\mu)$ is nonempty and $J(\cdot,\mu)$ is lower semicontinuous on the topological space $E$;
--   2. for any sequence $(\nu^n)_n\subseteq\arg\min_E J(\cdot,\mu)$ such that $p(\nu^n)$ is nondecreasing (resp. nonincreasing) in $L$, there exist a subsequence $(n_j)_{j\in\mathbb N}$ and $\nu\in\arg\min_E J(\cdot,\mu)$ such that $\nu^{n_j}\to\nu$ as $j\to\infty$ and
--   $$
--   p\nu=\sup_j p(\nu^{n_j})\qquad(\text{resp. } p\nu=\inf_j p(\nu^{n_j})).
--   $$
--
--   This compactness-type condition is what makes $\inf R(\mu)$ and $\sup R(\mu)$ best responses themselves (Lemma 2.4 c)).
--
--   **Formalization Note** A subsequence is $\nu\circ\varphi$ with $\varphi:\mathbb N\to\mathbb N$ strictly increasing; convergence is in the topology of $E$; "nondecreasing"/"nonincreasing" are `Monotone`/`Antitone`. The nondecreasing case (with the supremum) and the nonincreasing case (with the infimum) are two separate fields.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.1, Assumption 2.1, p.5

import Mathlib
import Definitions.Def_SubmodMFG_argminSet

namespace SubmodMFG

open Filter Topology

/-- **Assumption 2.1** (existence of minimizers and closedness along monotone sequences).
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.1, Assumption 2.1, p.5: "For every µ ∈ L, we assume that:
(1) The set arg min_E J(·, µ) is nonempty and J(·, µ) is lower semicontinuous;
(2) For any sequence (νⁿ)ₙ ⊂ arg min_E J(·, µ) such that p(νⁿ) is nondecreasing or
nonincreasing in L, there exists a subsequence (n_j)_{j∈ℕ} and ν ∈ arg min_E J(·, µ) such that
ν^{n_j} converges to ν as j → ∞ and pν = sup_j p(ν^{n_j}) or pν = inf_j p(ν^{n_j}),
respectively."

Fields: `nonempty` and `lsc` are (1); `mono` is (2) for nondecreasing `p(νⁿ)` (with the
supremum), `anti` is (2) for nonincreasing `p(νⁿ)` (with the infimum).

**Formalization Note.** `J` is curried (`J ν µ = J(ν, µ)`); `E` carries an arbitrary topology and
convergence is `Tendsto … atTop (𝓝 ν)` in it. A subsequence is `ν ∘ φ` with `φ : ℕ → ℕ`
strictly increasing. "Nondecreasing"/"nonincreasing" are Mathlib's `Monotone`/`Antitone`.
Sup and inf are taken in the complete lattice `L`. -/
structure Assumption21 {E L : Type*} [TopologicalSpace E] [CompleteLattice L]
    (p : E → L) (J : E → L → ℝ) : Prop where
  /-- (1) `arg min_E J(·, µ)` is nonempty. -/
  nonempty : ∀ μ : L, (argminSet J μ).Nonempty
  /-- (1) `J(·, µ)` is lower semicontinuous. -/
  lsc : ∀ μ : L, LowerSemicontinuous (fun ν : E => J ν μ)
  /-- (2), nondecreasing case. -/
  mono : ∀ (μ : L) (ν : ℕ → E), (∀ n, ν n ∈ argminSet J μ) → Monotone (fun n => p (ν n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν₀ ∈ argminSet J μ,
      Tendsto (fun j => ν (φ j)) atTop (𝓝 ν₀) ∧ p ν₀ = ⨆ j, p (ν (φ j))
  /-- (2), nonincreasing case. -/
  anti : ∀ (μ : L) (ν : ℕ → E), (∀ n, ν n ∈ argminSet J μ) → Antitone (fun n => p (ν n)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ν₀ ∈ argminSet J μ,
      Tendsto (fun j => ν (φ j)) atTop (𝓝 ν₀) ∧ p ν₀ = ⨅ j, p (ν (φ j))

end SubmodMFG


