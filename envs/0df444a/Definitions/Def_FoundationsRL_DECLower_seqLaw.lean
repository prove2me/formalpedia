-- Prove2me | Definitions.Def_FoundationsRL_DECLower_seqLaw
-- name    : FoundationsRL_DECLower_seqLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:14:06.507694+00:00
-- url     : https://prove2.me/theorems/a7cd64a8-71d1-4b49-9caf-c47982846e91
-- title:
--   Law of a sequential process $X_i\sim P_i(\cdot\mid X_{1:i-1})$
-- statement:
--   Let $(\mathcal X_k,\mathcal F_k)_{k\ge0}$ be measurable spaces and, for each $k\ge 0$, let $\kappa_k$ be a kernel from $\mathcal X_0\times\dots\times\mathcal X_k$ to $\mathcal X_{k+1}$. For $n\ge 0$ and an initial point $x_0\in\mathcal X_0$, the **law of the sequential process** is the measure on $\mathcal X_0\times\dots\times\mathcal X_n$ of
--
--   $$
--   (x_0,X_1,\dots,X_n),\qquad X_{k+1}\sim\kappa_k(\cdot\mid x_0,X_1,\dots,X_k),\quad k=0,\dots,n-1,
--   $$
--
--   obtained by composing the kernels one step at a time (the Ionescu-Tulcea construction for finitely many steps).
--
--   It is the law $P$ of $X_1,\dots,X_n$ "under $X_i\sim P_i(\cdot\mid X_{1:i-1})$" in Lemma 22, with $P_i=\kappa_{i-1}$.
--
--   **Formalization Note** The notes' empty product $\mathcal X^0$ is the case of a one-point $\mathcal X_0$; an arbitrary $\mathcal X_0$ lets all kernels also depend on a fixed initial point. This is a local copy of the same object drafted in the mission on Foster, Kakade, Qian & Rakhlin (2021), which is not yet published.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 22, p. 107

import Mathlib

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Law of a sequential process** `X_i ∼ P_i(· | X_{1:i−1})`, `i = 1, …, n`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 22, p. 107 ("Let P and Q be the laws of X_1, …, X_n under X_i ∼ P_i(· | X_{1:i−1})").

Given measurable spaces `X 0, X 1, …` and kernels `κ k` from `X 0 × ⋯ × X k` to `X (k + 1)`,
`seqLaw κ n x₀` is the law on `X 0 × ⋯ × X n` of the process started at the point `x₀` that draws
coordinate `k + 1` from `κ k` given coordinates `0, …, k` (Mathlib's Ionescu-Tulcea partial
trajectory `Kernel.partialTraj κ 0 n` at `x₀`).

**Formalization Note.** The paper's `X_i` (`1 ≤ i ≤ n`) is coordinate `i`, and `P_i` is `κ (i − 1)`.
Coordinate `0` is a fixed initial point; the paper's `X^0` (the empty product) is the case
`X 0 = PUnit`, and an arbitrary `X 0` is a generalization. Kernels of index `≥ n` do not enter. -/
noncomputable def seqLaw {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) (n : ℕ)
    (x₀ : Π i : Iic 0, X i) : Measure (Π i : Iic n, X i) :=
  Kernel.partialTraj κ 0 n x₀

end FoundationsRL.DECLower


