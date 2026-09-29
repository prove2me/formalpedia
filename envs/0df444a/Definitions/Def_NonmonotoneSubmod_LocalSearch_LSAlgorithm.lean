-- Prove2me | Definitions.Def_NonmonotoneSubmod_LocalSearch_LSAlgorithm
-- name    : NonmonotoneSubmod_LocalSearch_LSAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:00:24.613204+00:00
-- url     : https://prove2.me/theorems/c3fb3c9b-cf46-4c30-bb63-3368f38992f2
-- title:
--   Algorithm LS — deterministic local search with acceptance factor $1+\epsilon/n^2$
-- statement:
--   Let $f : 2^X \to \mathbb{R}$ be a set function on a finite ground set $X$ with $n = |X|$ elements, let $\epsilon \in \mathbb{R}$ and put $c = 1 + \epsilon/n^2$. **Algorithm LS** of the paper is:
--
--   1. Let $S := \{v\}$, where $f(\{v\})$ is the maximum over all singletons $v \in X$.
--   2. If there is $a \in X \setminus S$ with $f(S \cup \{a\}) > c\, f(S)$, let $S := S \cup \{a\}$ and repeat step 2.
--   3. If there is $a \in S$ with $f(S \setminus \{a\}) > c\, f(S)$, let $S := S \setminus \{a\}$ and go back to step 2.
--   4. Return the maximum of $f(S)$ and $f(X \setminus S)$.
--
--   This definition file encodes the algorithm as a nondeterministic process that allows every choice the text allows:
--
--   - A **step** from $S$ to $S'$ is either an addition $S' = S \cup \{a\}$ with $a \notin S$ and $f(S \cup \{a\}) > c\,f(S)$, or, only when no such addition exists, a removal $S' = S \setminus \{a\}$ with $a \in S$ and $f(S \setminus \{a\}) > c\,f(S)$.
--   - A singleton $v$ is **of maximum value** if $f(\{w\}) \le f(\{v\})$ for every $w \in X$; ties are not broken.
--   - A **run of $k$ steps** is a sequence $S_0, S_1, \dots, S_k$ with $S_0 = \{v\}$ for some singleton $v$ of maximum value and each $S_{i+1}$ obtained from $S_i$ by a step.
--   - The run has **terminated** at $S$ if no step from $S$ exists.
--   - The **returned value** at $S$ is $\max\{f(S), f(X \setminus S)\}$.
--
--   **Formalization Note** The acceptance factor is $1 + \epsilon/n^2$ with $n = |X|$ as a real number. Steps use strict inequalities and the terminal condition is their negation, exactly as printed. Theorems about the algorithm quantify over every run, so no tie-breaking rule for the choice of $v$ or of the element $a$ is assumed.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1141, §3.1, Local Search Algorithm: LS, steps 1–4

import Mathlib

namespace NonmonotoneSubmod.LocalSearch

/-- The acceptance factor `1 + ε / n²` of Algorithm LS (Feige–Mirrokni–Vondrák 2011, p. 1141),
where `n = |X|` is the number of elements of the ground set. -/
noncomputable def lsFactor (X : Type) [Fintype X] (ε : ℝ) : ℝ :=
  1 + ε / (Fintype.card X : ℝ) ^ 2

/-- One step of Algorithm LS (Feige–Mirrokni–Vondrák 2011, p. 1141, steps 2–3), as a relation
allowing every choice of element the text allows. With `c = 1 + ε / n²`:
* (step 2) if some `a ∉ S` has `f (S ∪ {a}) > c · f S`, the step may move to `S ∪ {a}`;
* (step 3) only when no such addition exists, if some `a ∈ S` has `f (S \ {a}) > c · f S`, the
  step may move to `S \ {a}`. -/
def lsStep {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (f : Finset X → ℝ)
    (S S' : Finset X) : Prop :=
  (∃ a, a ∉ S ∧ lsFactor X ε * f S < f (insert a S) ∧ S' = insert a S) ∨
    ((∀ a, a ∉ S → f (insert a S) ≤ lsFactor X ε * f S) ∧
      ∃ a, a ∈ S ∧ lsFactor X ε * f S < f (S.erase a) ∧ S' = S.erase a)

/-- `v` is a singleton of maximum value: `f {w} ≤ f {v}` for every `w ∈ X` (Algorithm LS,
step 1). Ties are not broken: every maximizing `v` is allowed. -/
def IsMaxSingleton {X : Type} (f : Finset X → ℝ) (v : X) : Prop :=
  ∀ w : X, f {w} ≤ f {v}

/-- `S 0, S 1, …, S k` is a run of `k` steps of Algorithm LS: it starts (step 1) at `{v}` for a
singleton `v` of maximum value, and each `S (i + 1)` arises from `S i` by an LS step. -/
def IsLSRun {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (f : Finset X → ℝ)
    (S : ℕ → Finset X) (k : ℕ) : Prop :=
  (∃ v : X, IsMaxSingleton f v ∧ S 0 = {v}) ∧ ∀ i, i < k → lsStep ε f (S i) (S (i + 1))

/-- Algorithm LS has terminated at `S`: no step (addition of step 2 or removal of step 3)
applies. -/
def IsLSTerminal {X : Type} [Fintype X] [DecidableEq X] (ε : ℝ) (f : Finset X → ℝ)
    (S : Finset X) : Prop :=
  ∀ S' : Finset X, ¬ lsStep ε f S S'

/-- The value returned by Algorithm LS at the final set `S` (step 4): the maximum of `f(S)` and
`f(X \ S)`. -/
def lsOutput {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (S : Finset X) : ℝ :=
  max (f S) (f Sᶜ)

end NonmonotoneSubmod.LocalSearch


