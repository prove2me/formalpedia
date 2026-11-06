-- Prove2me | Definitions.Def_FourierRankQLB_POVM
-- name    : FourierRankQLB_POVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:14.412611+00:00
-- url     : https://prove2.me/theorems/b217ead2-b8e4-4dd7-98b9-8576e4e1a758
-- title:
--   A positive operator-valued measure on a measurable space
-- statement:
--   Let $X$ be a measurable space and $H$ a complex Hilbert space. A POVM assigns to each measurable $S\subseteq X$ an operator $E(S)$ on $H$ such that
--
--   1. $E(S)\succeq0$;
--   2. $E(X)=I$;
--   3. for every $x\in H$ and pairwise disjoint measurable $S_1,S_2,\dots$,
--   $$
--   \Bigl\langle x,E\Bigl(\bigcup_iS_i\Bigr)x\Bigr\rangle=\sum_i\langle x,E(S_i)x\rangle .
--   $$
--
--   It is the final measurement of a query algorithm. No finiteness of $X$ or of $H$ is assumed, so the outcome may be a classical vector of $\mathbb R^n$.
--
--   **Formalization Note** Additivity is weak (for each vector state), the standard axiom. Only values on measurable sets carry meaning.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §3.1, pp.16–18

import Mathlib

namespace FourierRankQLB

/-- A positive operator-valued measure on a measurable space `X`, acting on a complex Hilbert space
`H`: effects `0 ⪯ E(S)` on measurable sets, `E(X) = I`, and weak countable additivity.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §3.1, pp. 16–18 (the final measurement of Eq. (15) and "a final POVM effect `0 ⪯ E ⪯ I`").

**Formalization Note.** `eff` is a function on all subsets, and only its values on measurable sets
carry meaning. Weak additivity (the sum converges for each vector state) is the standard axiom; norm
additivity would exclude ordinary projection-valued measures. `H` need not be finite-dimensional or
separable. Additivity gives `E(∅) = 0` and, with `E(X) = I`, also `E(S) ⪯ I`. -/
structure POVM (X H : Type) [MeasurableSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The effect of a set of outcomes. -/
  eff : Set X → H →L[ℂ] H
  /-- Effects of measurable sets are positive. -/
  isPositive_eff : ∀ S, MeasurableSet S → (eff S).IsPositive
  /-- Normalization: the effect of the whole outcome space is the identity. -/
  eff_univ : eff Set.univ = 1
  /-- Weak countable additivity on disjoint measurable sets. -/
  hasSum_eff : ∀ (x : H) (f : ℕ → Set X), (∀ i, MeasurableSet (f i)) →
    Pairwise (Function.onFun Disjoint f) →
    HasSum (fun i => inner ℂ x (eff (f i) x)) (inner ℂ x (eff (⋃ i, f i) x))

end FourierRankQLB


