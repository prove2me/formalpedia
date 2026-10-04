-- Prove2me | Definitions.Def_DoubleGreedyUSM_Fractional_Algorithm4
-- name    : DoubleGreedyUSM_Fractional_Algorithm4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:43:41.45206+00:00
-- url     : https://prove2.me/theorems/62ab4bfc-5b0d-437d-8c81-3a68c9295d6c
-- title:
--   Algorithm 4 (MultilinearUSM) — one fractional step, the run $(x_i, y_i)$, and $OPT_i = (OPT \vee x_i) \wedge y_i$
-- statement:
--   Let $\mathcal N$ be a finite ground set and $f : 2^{\mathcal N} \to \mathbb R$ a set function, with multilinear extension
--   $$F(x) = \sum_{S \subseteq \mathcal N} f(S) \prod_{u \in S} x_u \prod_{u \notin S} (1 - x_u), \qquad x \in \mathbb R^{\mathcal N},$$
--   which for $x \in [0,1]^{\mathcal N}$ is the expected value of $f(R(x))$, where the random set $R(x)$ contains each $u$ independently with probability $x_u$. A set $O \subseteq \mathcal N$ is identified with its characteristic vector $\mathbf 1_O$, and $\{u\}$ denotes the unit vector at $u$.
--
--   **Algorithm 4 (MultilinearUSM).** Fix an order $u_1, \dots, u_n$ of $\mathcal N$. Start from $x_0 = \mathbf 0$ (the empty set) and $y_0 = \mathbf 1$ (the ground set). For $i = 1, \dots, n$:
--
--   1. $a_i = F(x_{i-1} + \{u_i\}) - F(x_{i-1})$ and $b_i = F(y_{i-1} - \{u_i\}) - F(y_{i-1})$;
--   2. $a_i' = \max\{a_i, 0\}$ and $b_i' = \max\{b_i, 0\}$;
--   3. $x_i = x_{i-1} + \dfrac{a_i'}{a_i' + b_i'}\,\{u_i\}$ and $y_i = y_{i-1} - \dfrac{b_i'}{a_i' + b_i'}\,\{u_i\}$,
--
--   where, if $a_i' = b_i' = 0$, the two fractions are taken to be $1$ and $0$ respectively. The algorithm returns the random set $R(x_n)$.
--
--   The module defines one step of this loop on a state $(x, y)$ and an element $u$, the state $(x_i, y_i)$ after the first $i$ steps of the order, and, for a set $O$ (in the analysis, an optimal solution), the vector
--   $$OPT_i = (\mathbf 1_O \vee x_i) \wedge y_i,$$
--   where $\vee$ and $\wedge$ are coordinate-wise maximum and minimum.
--
--   These are the objects of Appendix A: every statement of the mission is about this concrete algorithm, not about an arbitrary process.
--
--   **Formalization Note.** The ground set is a `Fintype` $X$, vectors are functions $X \to \mathbb R$ (no $[0,1]$ constraint in the type; the run stays in $[0,1]^X$ by construction), and $F$ is the published `NonmonotoneSubmod.Shared.F`. The order is a list `l`; `state f l i` folds the step over its first $i$ entries, so `state f l 0 = (0, 1)` and `state f l i` is the final state for every $i \ge$ `l.length`. Lines 3–4 of the printed algorithm assign $a_i', b_i'$ although line 5 and the proof use $a_i, b_i$; the definition reads lines 3–4 as defining $a_i, b_i$ (`aGain`, `bGain`). The footnote's convention is written as an explicit case split on $a_i' + b_i' = 0$ (equivalent to $a_i' = b_i' = 0$ since both are nonnegative), because Lean's $0/0 = 0$ would otherwise reverse it.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, Appendix A, preamble and Algorithm 4 (PDF p. 9); OPT_i defined after Theorem A.1 (PDF p. 9)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace DoubleGreedyUSM.Fractional

/-- The characteristic vector `1_O ∈ {0,1}^X` of a set `O ⊆ X` (Buchbinder–Feldman–Naor–Schwartz,
FOCS 2012, App. A, PDF p. 9: "we … unify a set with its characteristic vector"). The unit vector
`{u}` of Algorithm 4 is `indicator {u}`. -/
def indicator {X : Type} [DecidableEq X] (O : Finset X) : X → ℝ :=
  fun v => if v ∈ O then 1 else 0

/-- Line 3 of Algorithm 4 (with the slip `a'_i` read as `a_i`): the gain
`a = F(x + {u}) − F(x)` of raising coordinate `u` of `x` by one. -/
noncomputable def aGain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (x : X → ℝ) (u : X) : ℝ :=
  NonmonotoneSubmod.Shared.F f (x + indicator {u}) - NonmonotoneSubmod.Shared.F f x

/-- Line 4 of Algorithm 4 (with the slip `b'_i` read as `b_i`): the gain
`b = F(y − {u}) − F(y)` of lowering coordinate `u` of `y` by one. -/
noncomputable def bGain {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (y : X → ℝ) (u : X) : ℝ :=
  NonmonotoneSubmod.Shared.F f (y - indicator {u}) - NonmonotoneSubmod.Shared.F f y

/-- One iteration (lines 3–7) of Algorithm 4, MultilinearUSM, on the state `s = (x, y)` and the
element `u`: with `a = aGain f x u`, `b = bGain f y u`, `a' = max a 0`, `b' = max b 0`,
`x ← x + a'/(a' + b') · {u}` and `y ← y − b'/(a' + b') · {u}`, where by the footnote of the
algorithm `a'/(a' + b') = 1` and `b'/(a' + b') = 0` when `a' = b' = 0`. -/
noncomputable def step {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (s : (X → ℝ) × (X → ℝ)) (u : X) : (X → ℝ) × (X → ℝ) :=
  let a' := max (aGain f s.1 u) 0
  let b' := max (bGain f s.2 u) 0
  let t : ℝ := if a' + b' = 0 then 1 else a' / (a' + b')
  let r : ℝ := if a' + b' = 0 then 0 else b' / (a' + b')
  (s.1 + t • indicator {u}, s.2 - r • indicator {u})

/-- The state `(x_i, y_i)` of Algorithm 4 after the first `i` iterations, processing the ground set
in the order `l = [u_1, …, u_n]`, from `x_0 = ∅` (the vector `0`) and `y_0 = 𝒩` (the vector `1`).
For `i ≥ l.length` it is the final state `(x_n, y_n)`. -/
noncomputable def state {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (l : List X) (i : ℕ) : (X → ℝ) × (X → ℝ) :=
  (l.take i).foldl (step f) (0, 1)

/-- `OPT_i = (OPT ∨ x_i) ∧ y_i` (App. A, PDF p. 9): the coordinate-wise minimum of `y_i` and the
coordinate-wise maximum of `1_O` and `x_i`, for the state `s = (x_i, y_i)` and a set `O`. -/
def optI {X : Type} [DecidableEq X] (O : Finset X) (s : (X → ℝ) × (X → ℝ)) : X → ℝ :=
  fun v => min (max (indicator O v) (s.1 v)) (s.2 v)

end DoubleGreedyUSM.Fractional


