-- Prove2me | Definitions.Def_NashOrTriangle_IsMultisetSize
-- name    : NashOrTriangle_IsMultisetSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:43:32.988901+00:00
-- url     : https://prove2.me/theorems/8d8fb200-a6fa-4be0-b93a-f7868aafc365
-- title:
--   Valid sparsification size $s_H(u)$
-- statement:
--   For a finite game $H$ with payoff $M$ and $u > 0$, a number $s \ge 1$ is a **valid multiset size** $s_H(u)$ if every mixed strategy of either player can be approximated to within $u$, uniformly against all pure opposing strategies, by the uniform distribution on a multiset of $s$ actions (repetitions allowed):
--
--   1. for every probability vector $p$ on the rows there is a multiset $S$ of $s$ rows with
--   $$
--   \Bigl|\tfrac1s \sum_{a \in S} M(a, b) - \sum_a p(a) M(a, b)\Bigr| \le u \quad \text{for every column } b;
--   $$
--   2. for every probability vector $q$ on the columns there is a multiset $S$ of $s$ columns with the symmetric property against every row.
--
--   The same $s$ serves both players. Sampling bounds of this kind go back to Althöfer and to Lipton and Young.
--
--   **Formalization Note** Mixed strategies of the finite game are arbitrary real probability vectors. "$s_H(u) \le X$" is stated as "some valid $s$ satisfies $s \le X$", and a bound in terms of $s = s_H(u)$ is required for every valid $s$, so no junk-valued minimum is needed.
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), Appendix C, pp.23–24 (PDF pp.24–25)

import Mathlib

namespace NashOrTriangle

/-- `s` is a valid value of `s_H(u)` for the finite game `M`: `s ≥ 1`, and every mixed strategy
of either player is approximated to within `u`, uniformly against all pure opposing
strategies, by the uniform distribution on some multiset of `s` actions (repetitions allowed);
the same `s` serves both players.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), Appendix C, printed pp. 23–24 (PDF pp. 24–25): "Let sH(u) be a multiset size such that
every mixed strategy of either player can be approximated to within u, uniformly against all
pure opposing strategies, by the uniform distribution on a multiset of sH(u) actions.
Repetitions are allowed, and the same multiset size is used throughout the Ramsey argument."

**Formalization Note** Mixed strategies of the finite game are all real probability vectors
`p : A → ℝ`. "Within `u`" is `≤ u`. A statement "`s_H(u) ≤ X`" is written
"some valid `s` has `s ≤ X`", and a bound in terms of `s = s_H(u)` is required for every
valid `s`; no junk-valued minimum is used. -/
def IsMultisetSize {A B : Type*} [Fintype A] [Fintype B] (M : A → B → ℚ) (u : ℝ) (s : ℕ) :
    Prop :=
  1 ≤ s ∧
  (∀ p : A → ℝ, (∀ a, 0 ≤ p a) → ∑ a, p a = 1 →
    ∃ S : Multiset A, S.card = s ∧
      ∀ b, |(S.map fun a => (M a b : ℝ)).sum / s - ∑ a, p a * (M a b : ℝ)| ≤ u) ∧
  (∀ q : B → ℝ, (∀ b, 0 ≤ q b) → ∑ b, q b = 1 →
    ∃ S : Multiset B, S.card = s ∧
      ∀ a, |(S.map fun b => (M a b : ℝ)).sum / s - ∑ b, q b * (M a b : ℝ)| ≤ u)

end NashOrTriangle


