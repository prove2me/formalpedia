-- Prove2me | Definitions.Def_QueryDepthMIS_condProb
-- name    : QueryDepthMIS_condProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:02.954969+00:00
-- url     : https://prove2.me/theorems/c71c34de-2f6b-4aca-be04-8cf3fc35133d
-- title:
--   Conditional probability given exposed positions, $\Pr_T[X \mid \pi(S)]$
-- statement:
--   The paper builds $\pi$ by exposing positions one at a time; for disjoint sets of positions $S, T$ and an event $X$, $\Pr_T[X \mid \pi(S)]$ is the probability of $X$ when $\pi(T)$ is exposed, conditioned on $\pi(S)$ having already been exposed.
--
--   Here, for a set of positions $S$ and a reference ordering $\omega_0$ (supplying the exposed values $\pi(S)$),
--   $$
--   \Pr[X \mid \pi(S) = \pi_0(S)] = \frac{|\{\omega : \omega \text{ agrees with } \omega_0 \text{ on } S,\ \omega \in X\}|}{|\{\omega : \omega \text{ agrees with } \omega_0 \text{ on } S\}|},
--   $$
--   where $\omega$ agrees with $\omega_0$ on $S$ if every position of $S$ holds the same vertex in both. The denominator is at least $1$.
--
--   **Formalization Note** Every event conditioned this way in the mission is determined by the positions in $S \cup T$, so averaging over all completions of $\pi(S)$ gives the paper's $\Pr_T[X \mid \pi(S)]$.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.1, p.11

import Mathlib
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Conditional probability given the exposed positions `S` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.1, p.11): "For two
disjoint sets of positions S, T and an event X, we use the notation Pr_T[X | π(S)] to denote the
probability of X when exposing π(T), conditioned on π(S) having already been exposed."

`condProb E S ω₀` is the uniform probability of `E` among the permutations `ω` that put, at every
position of `S`, the same vertex as the reference permutation `ω₀` (the value of `π(S)` being
conditioned on is the one of `ω₀`):
`|{ω : ω agrees with ω₀ on S, E ω}| / |{ω : ω agrees with ω₀ on S}|`.

**Formalization Note** The denominator is at least `1` (`ω₀` agrees with itself). The paper's
`Pr_T[X | π(S)]` exposes only the positions of `T`; every event conditioned this way in the
mission (the events of Lemmas 3.2 and 3.3 and `E(P, Q)` of Claim 3.7) is determined by the
positions in `S ∪ T`, so averaging over all completions of `π(S)` gives the same number. Positions
outside `[1, n]` in `S` impose no constraint. -/
noncomputable def condProb {V : Type*} [Fintype V] [DecidableEq V] (E : Perm V → Prop)
    (S : Finset ℕ) (ω₀ : Perm V) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun ω : Perm V =>
      (∀ v, rank ω₀ v ∈ S → rank ω v = rank ω₀ v) ∧ E ω)).card : ℝ) /
    ((Finset.univ.filter (fun ω : Perm V =>
      ∀ v, rank ω₀ v ∈ S → rank ω v = rank ω₀ v)).card : ℝ)

end QueryDepthMIS


