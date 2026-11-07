-- Prove2me | Definitions.Def_SetMultCost_IsMGood
-- name    : SetMultCost_IsMGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:03.26242+00:00
-- url     : https://prove2.me/theorems/e2e8fce7-35cd-4739-ad85-985945606707
-- title:
--   $\alpha$ is $m$-good for $(\tau,S)$
-- statement:
--   A real $0<\alpha\le1$ is **$m$-good for $(\tau,S)$** when, for each $i\in S$ and all natural numbers $a_1,\dots,a_r,b_1,\dots,b_r$ with $a_j+b_j\le\tau_{i-1}$ for every $j$ and $\sum_j(a_j+b_j)>\tau_i$,
--
--   $$\sum_{j=1}^r|a_j\alpha-b_j|\ge m.$$
--
--   This is the imbalance condition linking the arithmetic of $\alpha$ to the rank measure.
--
--   **Formalization Note** A correction. The page prints "positive integers", but Lemma 4.4 applies the definition to $a_j=d_{\mathcal P_j}$ and $b_j=d_{\mathcal N_j}$, which may vanish, and the proofs of Lemmas 5.4 and 5.5 say "non-negative positive". With positive integers Lemma 4.4 is false: for $\tau=(1,1)$, $S=\{1\}$, $d=2$ no positive $a_j,b_j$ have $a_j+b_j\le1$, so every $\alpha$ is vacuously $m$-good for every $m$, yet $x\cdot y$ with $\mathcal P=\{1\}$, $\mathcal N=\{2\}$, $\alpha=1$ has relative rank $1/n$.
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Definition 4.3, pp.14–15

import Mathlib

namespace SetMultCost

/-- **`α` is `m`-good for `(τ,S)`.** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), Definition 4.3, pp.14–15: "A real number 0 < α ≤ 1 is
said to be m-good for (τ,S) if for each i ∈ S and for every positive integers a1, . . . , ar,
b1, · · · , br that satisfy: • For every j ∈ [r], (aj + bj) ≤ τi−1 • ∑j(aj + bj) > τi, we have
∑_{j=1}^r |ajα − bj| ≥ m."

**Formalization Note.** A correction: `a_j, b_j` range over `ℕ`, including `0`, in place of the
printed "positive integers". Lemma 4.4 applies this to `a_j = d_{P_j}`, `b_j = d_{N_j}`, which may
vanish, and the proofs of Lemmas 5.4, 5.5 say "non-negative positive". With positive integers Lemma
4.4 is false: for `τ = (1, 1)`, `S = {1}`, `d = 2` no positive `a_j, b_j` have `a_j + b_j ≤ 1`, so every
`α` would be `m`-good for every `m`, yet `x · y` with `P = {1}`, `N = {2}`, `α = 1` has relative rank
`1/n`. The clause `1 ≤ i` is the page's `S ⊆ [ℓ]`. The printed "Fix a non-decreasing τ" and "m > 0"
are hypotheses of the statements using this, which allow `m = 0`. -/
def IsMGood (α m : ℝ) (τ : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  0 < α ∧ α ≤ 1 ∧ ∀ i ∈ S, 1 ≤ i → ∀ (r : ℕ) (a b : Fin r → ℕ),
    (∀ j, a j + b j ≤ τ (i - 1)) → τ i < ∑ j, (a j + b j) →
      m ≤ ∑ j, |(a j : ℝ) * α - (b j : ℝ)|

end SetMultCost


