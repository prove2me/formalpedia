-- Prove2me | Definitions.Def_HellingerSubadd_seqLaw
-- name    : HellingerSubadd_seqLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:47:39.087538+00:00
-- url     : https://prove2.me/theorems/a7e387a4-9ddc-4d4e-a127-7a355c293d01
-- title:
--   Law of a sequential process $X_i\sim P^{(i)}(\cdot\mid X_{1:i-1})$
-- statement:
--   Let $(\mathcal X_k,\mathcal F_k)_{k\ge0}$ be measurable spaces and, for each $k\ge0$, let $\kappa_k$ be a kernel from $\mathcal X_0\times\dots\times\mathcal X_k$ to $\mathcal X_{k+1}$. For $n\ge0$ and an initial point $x_0\in\mathcal X_0$, the **law of the sequential process** is the measure on $\mathcal X_0\times\dots\times\mathcal X_n$ of
--
--   $$
--   (x_0,X_1,\dots,X_n),\qquad X_{k+1}\sim\kappa_k(\cdot\mid x_0,X_1,\dots,X_k),\quad k=0,\dots,n-1,
--   $$
--
--   obtained by composing the kernels one step at a time (the Ionescu-Tulcea construction for finitely many steps).
--
--   This is the object "$\mathbb P$, the law of $X_1,\dots,X_n$ under $X_i\sim P^{(i)}(\cdot\mid X_{1:i-1})$" of Lemma A.13, with $P^{(i)}=\kappa_{i-1}$.
--
--   **Formalization Note** The measure is Mathlib's `Kernel.partialTraj κ 0 n` evaluated at $x_0$. The paper's $\mathcal X^{(0)}$ is a single point, which is the case $\mathcal X_0=$ `PUnit`; an arbitrary $\mathcal X_0$ lets all kernels depend on a common initial point. Kernels with index $\ge n$ do not enter the law of $(x_0,X_1,\dots,X_n)$.
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Lemma A.13, p. 73; probability kernels as in Section 2, p. 9

import Mathlib

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace HellingerSubadd

/-- **Law of a sequential process** `X_i ∼ P^(i)(· | X_{1:i−1})`, `i = 1, …, n`.
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Lemma A.13, p. 73 ("Let P and Q be the laws of X_1, …, X_n under
X_i ∼ P^(i)(· | X_{1:i−1})"); probability kernels as in Section 2, p. 9.

Given measurable spaces `X 0, X 1, X 2, …` and kernels `κ k` from `X 0 × ⋯ × X k` to `X (k+1)`,
`seqLaw κ n x₀` is the law on `X 0 × ⋯ × X n` of the process started at the point `x₀` of
`X 0` that draws coordinate `k + 1` from `κ k` given coordinates `0, …, k`. It is Mathlib's
Ionescu-Tulcea partial trajectory `Kernel.partialTraj κ 0 n` evaluated at `x₀`.

**Formalization Note.** The paper's `X_i` (`1 ≤ i ≤ n`) is coordinate `i`, and its kernel
`P^(i)(· | x_{1:i−1})` is `κ (i − 1)` applied to the restriction of the trajectory to coordinates
`0, …, i − 1`. Coordinate `0` is a fixed initial point `x₀`; the paper's `X^(0)` is a one-point
space, which is the case `X 0 = PUnit`. For an arbitrary `X 0` the kernels may in addition
depend on a common initial point (a generalization). Kernels with index `≥ n` do not enter
`seqLaw κ n x₀`. -/
noncomputable def seqLaw {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) (n : ℕ)
    (x₀ : Π i : Iic 0, X i) : Measure (Π i : Iic n, X i) :=
  Kernel.partialTraj κ 0 n x₀

end HellingerSubadd


