-- Prove2me | Definitions.Def_Komlos_model
-- name    : Komlos_model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-03T20:49:08.79489+00:00
-- url     : https://prove2.me/theorems/34c71be8-f640-40f2-9d4d-a7bb329aa93f
-- title:
--   Sign vectors and the Komlós property
-- statement:
--   The two definitions underlying vector-balancing discrepancy.
--
--   `IsSignVector ε` says the real vector $\varepsilon \in \mathbb{R}^n$ has every entry equal to $+1$ or $-1$.
--
--   `KomlosBound K` is the **Komlós property at constant $K$**: for every number of vectors $n$, every dimension $m$, and every family $v_1, \dots, v_n \in \mathbb{R}^m$ with Euclidean ($\ell^2$) norm $\lVert v_i\rVert_2 \le 1$, there is a sign vector $\varepsilon$ such that every coordinate $j$ of the signed sum satisfies $\lvert \sum_i \varepsilon_i v_{ij}\rvert \le K$ — i.e. $\lVert \sum_i \varepsilon_i v_i \rVert_\infty \le K$, uniformly in $n$ and $m$. The Komlós conjecture asserts `∃ K, KomlosBound K`. The quantifier order is the content: $K$ is fixed before $n$ and $m$.
-- source:
--   Standard; see Kunisky, The discrepancy of unsatisfiable matrices and a lower bound for the Komlos conjecture constant, SIAM J. Discrete Math. 37 (2023), Section 1, https://arxiv.org/abs/2111.02974

import Mathlib

namespace Komlos

/-- A **sign vector**: each entry is `+1` or `-1`. -/
def IsSignVector {n : ℕ} (ε : Fin n → ℝ) : Prop :=
  ∀ i, ε i = 1 ∨ ε i = -1

/-- **The Komlós property at constant `K`**: every finite family
`v 0, …, v (n-1)` of vectors of Euclidean (`ℓ²`) norm at most `1`, in any
dimension `m`, admits signs `ε i ∈ {±1}` such that every coordinate `j` of
the signed sum satisfies `|∑ i, ε i * v i j| ≤ K` — that is, the signed sum
has `ℓ∞` norm at most `K`, uniformly in `n` and `m`. The Komlós conjecture
asserts that this holds for some finite `K`. -/
def KomlosBound (K : ℝ) : Prop :=
  ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)), (∀ i, ‖v i‖ ≤ 1) →
    ∃ ε : Fin n → ℝ, IsSignVector ε ∧ ∀ j, |∑ i, ε i * v i j| ≤ K

end Komlos


