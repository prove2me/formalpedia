-- Prove2me | Definitions.Def_F3SubsetSum_SubsetSum
-- name    : F3SubsetSum_SubsetSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:45.516458+00:00
-- url     : https://prove2.me/theorems/2f395109-2903-44ff-8a20-b6e7c1fa77ed
-- title:
--   Average-case $\mathbb F_3^n$-Subset-Sum: solutions and the probability that one exists
-- statement:
--   Let $h_1,\dots,h_m\in\mathbb F_3^n$. A **solution** of the instance $h=(h_1,\dots,h_m)$ (Problem 1.1) is a nonempty set $S\subseteq[m]$ with
--
--   $$
--   \sum_{i\in S}h_i=0 .
--   $$
--
--   The instance **has a solution** if some such $S$ exists. When $h_1,\dots,h_m$ are independent and uniform in $\mathbb F_3^n$, the probability that a solution exists is
--
--   $$
--   \Pr[\text{a solution exists}]=\frac{\#\{h\in(\mathbb F_3^n)^m : h \text{ has a solution}\}}{3^{nm}} .
--   $$
--
--   These are the objects of Fact 1.2 and the success criterion of every algorithm for Problem 1.1 in the mission.
--
--   **Formalization Note** $[m]$ is `Fin m`, $\mathbb F_3^n$ is `Fin n → ZMod 3`, and probabilities over uniform inputs are finite counts.
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Problem 1.1, p.4; Fact 1.2, p.4

import Mathlib

namespace F3SubsetSum

/-- **Zero subset sum** (Problem 1.1). Kothari, Metger, O'Donnell, Shutty, Wu, *Exponential quantum
speedup for F₃ⁿ-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE*,
arXiv:2609.40321v1, Problem 1.1, p.4: "find a nonempty set S ⊆ [m] such that Σ_{i∈S} h_i = 0."

`IsZeroSubsetSum h S` says that `S` is a solution of the instance `h = (h₁, …, h_m)`, each
`h i ∈ F₃ⁿ`: `S` is nonempty and the vectors indexed by `S` sum to `0`.

**Formalization Note** The index set `[m]` is `Fin m` (0-based) and `F₃ⁿ` is `Fin n → ZMod 3`. -/
def IsZeroSubsetSum {n m : ℕ} (h : Fin m → Fin n → ZMod 3) (S : Finset (Fin m)) : Prop :=
  S.Nonempty ∧ ∑ i ∈ S, h i = 0

/-- The instance `h` has a solution: some nonempty `S ⊆ [m]` with `Σ_{i∈S} h_i = 0`
(Problem 1.1, p.4; "a solution S exists", Fact 1.2, p.4). -/
def HasZeroSubsetSum {n m : ℕ} (h : Fin m → Fin n → ZMod 3) : Prop :=
  ∃ S : Finset (Fin m), IsZeroSubsetSum h S

open Classical in
/-- The probability, over `h₁, …, h_m` independent and uniform in `F₃ⁿ`, that a solution of
Problem 1.1 exists (Fact 1.2, p.4): the number of instances with a solution divided by `3^{nm}`. -/
noncomputable def probSolvable (n m : ℕ) : ℝ :=
  ((Finset.univ.filter fun h : Fin m → Fin n → ZMod 3 => HasZeroSubsetSum h).card : ℝ) /
    (3 : ℝ) ^ (n * m)

end F3SubsetSum


