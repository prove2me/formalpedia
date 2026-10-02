-- Prove2me | Definitions.Def_hardy2001_states
-- name    : hardy2001_states
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T09:00:16.446067+00:00
-- url     : https://prove2.me/theorems/0e8411af-bd7c-49e6-9768-00a88f4b2ec4
-- title:
--   Pure states, classical basis states and the classical state space
-- statement:
--   Let $S\subseteq\mathbb R^K$ be a set of (unnormalized) state vectors. Its set of **pure states** is
--
--   $$S_{\rm pure}=\operatorname{ext}(S)\setminus\{0\},$$
--
--   the extremal points of $S$ other than the null state $0$. A point is extremal if it is not a proper convex combination of two other points of $S$.
--
--   For a dimension $N$, the **basis states** of classical probability theory are the unit vectors $e_n\in\mathbb R^N$, with a $1$ in position $n$ and $0$ elsewhere. The **classical state space** is
--
--   $$S^{\rm cl}_N=\Big\{p\in\mathbb R^N:\ p_n\ge0\ \text{for all }n,\ \ \sum_{n}p_n\le1\Big\}.$$
--
--   This is the convex hull of the basis states and the null state.
--
--   These are the objects of Sections 4 and 6.9 of the paper: pure states are the definite states of a system, and the classical state space is a polytope.
--
--   **Formalization Note** Extremal points are Mathlib's `Set.extremePoints ℝ S`. Basis states are indexed by `Fin N`, so the paper's state $n$ is index $n-1$.
-- source:
--   L. Hardy, *Quantum Theory From Five Reasonable Axioms*, arXiv:quant-ph/0101012v4 (2001), https://arxiv.org/abs/quant-ph/0101012, pp. 4–5, Section 4, Eq. (2) and the sentence defining pure states; p. 12, Section 6.9

import Mathlib

namespace HardyFiveAxioms

/-- The pure states of a set `S` of (unnormalized) state vectors `p ∈ ℝᴷ`: the extremal points
of `S` other than the null state `0` (Hardy 2001, Section 6.9). -/
def pureStates {K : ℕ} (S : Set (Fin K → ℝ)) : Set (Fin K → ℝ) :=
  Set.extremePoints ℝ S \ {0}

/-- The `n`-th basis state of classical probability theory in dimension `N`: the vector with a
`1` in position `n` and `0` elsewhere (Hardy 2001, Eq. (2)). -/
def basisState {N : ℕ} (n : Fin N) : Fin N → ℝ :=
  Pi.single n 1

/-- The state space of classical probability theory in dimension `N` (Hardy 2001, Section 4):
the convex hull of the `N` basis states and the null state, i.e. the vectors `p ∈ ℝᴺ` with
nonnegative entries whose sum (the normalization coefficient) is at most `1`. -/
def classicalStates (N : ℕ) : Set (Fin N → ℝ) :=
  {p | (∀ n, 0 ≤ p n) ∧ ∑ n, p n ≤ 1}

end HardyFiveAxioms


