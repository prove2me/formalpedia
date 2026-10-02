-- Prove2me | Definitions.Def_AppliedComb_Ramsey_hypergraphRamseyNumber
-- name    : AppliedComb_Ramsey_hypergraphRamseyNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T01:17:53.559534+00:00
-- url     : https://prove2.me/theorems/5acf36e8-3881-42e7-bd44-4199629a4bf4
-- title:
--   The Ramsey number R(s : h_1, …, h_r) (Theorem 11.6)
-- statement:
--   For a non-negative integer $n$ let $[n] = \{1, 2, \dots, n\}$, and for a finite set $X$ and an integer $k \ge 0$ let $C(X, k)$ be the family of all $k$-element subsets of $X$. Fix integers $r, s \ge 0$ and a string $h = (h_1, \dots, h_r)$ of non-negative integers. We say that $N$ is a **Ramsey bound** for $(s : h_1, \dots, h_r)$ if for every $n \ge N$ and every function (colouring)
--   $$\phi : C([n], s) \longrightarrow [r]$$
--   there are a colour $\alpha \in [r]$ and a subset $H_\alpha \subseteq [n]$ with $|H_\alpha| = h_\alpha$ such that $\phi(S) = \alpha$ for every $S \in C(H_\alpha, s)$. The **Ramsey number** $R(s : h_1, \dots, h_r)$ is the least positive such $N$.
--
--   Theorem 11.6 states that this least positive integer exists whenever $r, s \ge 1$ and $h_i \ge s$ for every $i$. The case $s = 1$ is the Pigeon Hole Principle and the case $s = r = 2$ is Ramsey's Theorem for Graphs.
--
--   **Formalization Note.** The ground set $[n]$ is `Fin n` and the colours $[r]$ are `Fin r` (both 0-based). A colouring is a function on the subtype `{S : Finset (Fin n) // S.card = s}` of $s$-element subsets, so it has no values on other subsets. `hypergraphRamseyNumber s r h` is `sInf` of the set of positive Ramsey bounds; under the hypotheses of Theorem 11.6 that set is nonempty and the value is its least element.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 234, Theorem 11.6 (definition of R(s : h_1, …, h_r)); notation C(X, k) and [n] from p. 229

import Mathlib

namespace AppliedComb.Ramsey

/-- The Ramsey property of Theorem 11.6 (Keller & Trotter, *Applied Combinatorics*, 2017 Edition,
p. 234) for the threshold `N`, with `r` colours, subset size `s` and target sizes
`h = (h_1, …, h_r)` (colours indexed by `Fin r`): for every `n ≥ N` and every colouring
`ϕ : C([n], s) → [r]` of the `s`-element subsets of `[n] = Fin n`, there are a colour `α` and a set
`H_α ⊆ [n]` with `|H_α| = h_α` such that `ϕ(S) = α` for every `s`-element subset `S ⊆ H_α`. -/
def IsHypergraphRamseyBound (s r : ℕ) (h : Fin r → ℕ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n → ∀ ϕ : {S : Finset (Fin n) // S.card = s} → Fin r,
    ∃ α : Fin r, ∃ H : Finset (Fin n), H.card = h α ∧
      ∀ (S : Finset (Fin n)) (hS : S.card = s), S ⊆ H → ϕ ⟨S, hS⟩ = α

/-- The Ramsey number `R(s : h_1, …, h_r)` (Keller & Trotter, p. 234, Theorem 11.6): the least
positive integer `N` with `IsHypergraphRamseyBound s r h N`, taken as `sInf` of that set of
positive integers. Theorem 11.6 (`AppliedComb.Ramsey.hypergraph_ramsey`) states that the set is
nonempty when `r, s ≥ 1` and every `h_i ≥ s`, so the value is its least element. -/
noncomputable def hypergraphRamseyNumber (s r : ℕ) (h : Fin r → ℕ) : ℕ :=
  sInf {N : ℕ | 0 < N ∧ IsHypergraphRamseyBound s r h N}

end AppliedComb.Ramsey


