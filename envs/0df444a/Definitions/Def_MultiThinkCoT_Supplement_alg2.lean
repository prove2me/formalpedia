-- Prove2me | Definitions.Def_MultiThinkCoT_Supplement_alg2
-- name    : MultiThinkCoT_Supplement_alg2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:57:52.563795+00:00
-- url     : https://prove2.me/theorems/5705f69b-9b08-4427-b5ab-f2e720bfe9c2
-- title:
--   Algorithm 2 — parity support recovery from heterogeneous CoTs, with its cost
-- statement:
--   Algorithm 2 receives samples $\{(x^{(i)},\tilde z^{(i)})\}_{i=1}^m$ with $x^{(i)}\in\{0,1\}^d$, $\tilde z^{(i)}\in\{0,1\}^k$. With $\tilde z^{(i)}_0=0$ it forms the increments and their sums
--
--   $$
--   \tilde\delta^{(i)}_t:=1-2\big(\tilde z^{(i)}_t\oplus\tilde z^{(i)}_{t-1}\big),\qquad \tilde s^{(i)}:=\sum_{t=1}^k\tilde\delta^{(i)}_t,
--   $$
--
--   the coordinate scores
--
--   $$
--   \mathrm{score}(j)=\frac1m\sum_{i=1}^m\big(1-2x^{(i)}_j\big)\,\tilde s^{(i)},\qquad j\in[d],
--   $$
--
--   and outputs $\widehat S$, the $k$ indices with the largest score.
--
--   The paper does not specify how ties are broken; the definition ranks by larger score first and then by smaller index, so that $j\in\widehat S$ exactly when fewer than $k$ indices rank above $j$. The cost of the algorithm under unit-cost arithmetic is $m(d+k)$ to read the sample, $5mk$ for the increments and their sums, $d(4m+1)$ for the scores, and $3d^2+2d$ for the top-$k$ selection.
--
--   **Formalization Note** Bits enter the arithmetic as the reals $0,1$. At $m=0$ the average is $0$ by Lean's convention $1/0=0$.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Appendix G.1, Algorithm 2, p.61 (PDF p.61)

import Mathlib

namespace MultiThinkCoT.Supplement

/-!
# Algorithm 2 (parity support recovery under heterogeneous CoT supervision), with its cost

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers:
How Chain-of-Thought Heterogeneity Affects Efficient Learnability*, arXiv:2604.24737 (held
version, sha256 e663a640…), Algorithm 2, p.61 (PDF p.61).

Input: samples `{(x(i), z̃(i))}_{i=1}^m`, `x(i) ∈ {0,1}^d`, `z̃(i) ∈ {0,1}^k`. For each `i` and
`t ∈ [k]`, with `z̃(i)_0 = 0`, `δ̃(i)_t := 1 − 2 (z̃(i)_t ⊕ z̃(i)_{t−1})` and
`s̃(i) := Σ_{t=1}^k δ̃(i)_t`. For each `j ∈ [d]`, `score(j) = (1/m) Σ_i (1 − 2 x(i)_j) s̃(i)`.
Output `Ŝ` as the `k` indices with largest `score(j)`.

**Formalization Note.**
* `zext z t` is `z̃_t` for `t = 0, …, k` (`z̃_0 = 0`; the observed CoT `z : Fin k → Bool` holds
  `z̃_1, …, z̃_k`). Bits enter the arithmetic as `0/1` reals.
* Ties: the paper does not say how ties among scores are broken. `alg2Out` fixes the rule
  "larger score first, then smaller index": `j ∈ Ŝ` iff fewer than `k` indices `j'` beat `j`, where
  `j'` beats `j` when `score(j') > score(j)`, or `score(j') = score(j)` and `j' < j`. This is a
  strict total order, so `Ŝ` has exactly `k` elements when `k ≤ d`. At `m = 0` the average
  `(1/m) Σ` is `0` (Lean's `1/0 = 0`); Algorithm 2 is only run with `m ≥ 1` samples there.
* **Cost model (unit-cost real arithmetic, one unit per bit read, operation or comparison):**
  `alg2Cost d k m` charges `m (d + k)` to read the sample; `4` per increment (`⊕`, multiply,
  subtract, read of the previous token) and `1` per addition into `s̃(i)`, i.e. `5 m k`;
  per coordinate `j`, `4` per sample (read, `1 − 2x`, multiply, add) plus `1` division, i.e.
  `d (4 m + 1)`; for the top-`k` selection `3` per ordered pair of coordinates (two comparisons and
  a count), i.e. `3 d²`, plus `2` per coordinate (threshold test and output). The algorithm has no
  data-dependent branching beyond these comparisons, so its cost depends only on `(d, k, m)`.
-/

/-- `z̃_t` for `t = 0, …, k` (`z̃_0 = 0`), extended by `false` beyond `k`. -/
def zext {k : ℕ} (z : Fin k → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => if h : n < k then z ⟨n, h⟩ else false

/-- A bit as a real number in `{0, 1}`. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

/-- `s̃ = Σ_{t=1}^k (1 − 2 (z̃_t ⊕ z̃_{t−1}))`. -/
noncomputable def incrSum {k : ℕ} (z : Fin k → Bool) : ℝ :=
  ∑ t : Fin k, (1 - 2 * bitR (xor (zext z (t.1 + 1)) (zext z t.1)))

/-- `score(j) = (1/m) Σ_i (1 − 2 x(i)_j) s̃(i)`. -/
noncomputable def alg2Score {d k m : ℕ} (data : Fin m → (Fin d → Bool) × (Fin k → Bool))
    (j : Fin d) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, (1 - 2 * bitR ((data i).1 j)) * incrSum (data i).2

/-- The output `Ŝ` of Algorithm 2: the `k` indices with the largest score, ties broken towards
the smaller index. -/
noncomputable def alg2Out {d k m : ℕ} (data : Fin m → (Fin d → Bool) × (Fin k → Bool)) :
    Finset (Fin d) :=
  Finset.univ.filter fun j =>
    (Finset.univ.filter fun j' =>
      alg2Score data j < alg2Score data j' ∨
        (alg2Score data j' = alg2Score data j ∧ j' < j)).card < k

/-- The cost of Algorithm 2 on `m` samples with `x ∈ {0,1}^d`, `z̃ ∈ {0,1}^k` (see the cost
model above). -/
def alg2Cost (d k m : ℕ) : ℕ :=
  m * (d + k) + 5 * m * k + d * (4 * m + 1) + 3 * d * d + 2 * d

end MultiThinkCoT.Supplement


