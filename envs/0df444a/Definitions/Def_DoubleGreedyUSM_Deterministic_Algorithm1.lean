-- Prove2me | Definitions.Def_DoubleGreedyUSM_Deterministic_Algorithm1
-- name    : DoubleGreedyUSM_Deterministic_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T17:09:18.288159+00:00
-- url     : https://prove2.me/theorems/e7797d7c-c3f1-430f-bc09-d4dc25fa572f
-- title:
--   Algorithm 1 (DeterministicUSM) — one step, the states $(X_i, Y_i)$, and $OPT_i$
-- statement:
--   This file defines the deterministic double greedy algorithm (Algorithm 1, DeterministicUSM) of Buchbinder, Feldman, Naor and Schwartz for unconstrained submodular maximization, together with the auxiliary sets used in its analysis.
--
--   Let $\mathcal N$ be a finite ground set and $f : 2^{\mathcal N} \to \mathbb R$ a set function. The algorithm scans the elements of $\mathcal N$ once, in an arbitrary order $u_1, \dots, u_n$, and maintains two solutions $X$ and $Y$, starting from
--   $$X_0 = \emptyset, \qquad Y_0 = \mathcal N.$$
--   In iteration $i$ it computes the two marginal gains
--   $$a_i = f(X_{i-1} \cup \{u_i\}) - f(X_{i-1}), \qquad b_i = f(Y_{i-1} \setminus \{u_i\}) - f(Y_{i-1}),$$
--   and then:
--
--   1. if $a_i \ge b_i$, it sets $X_i = X_{i-1} \cup \{u_i\}$ and $Y_i = Y_{i-1}$;
--   2. otherwise it sets $X_i = X_{i-1}$ and $Y_i = Y_{i-1} \setminus \{u_i\}$.
--
--   A tie $a_i = b_i$ adds $u_i$ to $X$. After $n$ iterations the algorithm returns $X_n$ (equivalently $Y_n$).
--
--   The definitions are: the gain $a$ of adding an element to the first solution of a state $(X, Y)$; the gain $b$ of removing it from the second solution; the one-iteration update of the state; the state $(X_i, Y_i)$ after the first $i$ iterations, for the order given as a list $[u_1, \dots, u_n]$; and, for a set $O$ (in the analysis, an optimal solution $OPT$), the hybrid set
--   $$OPT_i = (OPT \cup X_i) \cap Y_i,$$
--   which interpolates between $OPT_0 = OPT$ and the algorithm's output.
--
--   These objects underlie the analysis of the deterministic algorithm: the approximation guarantee (Theorem I.1), the two lemmas of its proof, and the tight example. The gains $a_i, b_i$ and the hybrid sets $OPT_i$ are the same objects in the analysis of the randomized variant (Algorithm 2), which reuses them.
--
--   **Formalization Note** The ground set is a finite type `X`, subsets are `Finset X`, and $f$ takes real values; no hypothesis on $f$ is built into the definitions, the theorems carry them. The order $u_1, \dots, u_n$ is a list `l`; `state f l i` is the left fold of the update over the first `i` entries of `l`, starting from $(\emptyset, \mathcal N)$, so `state f l 0` $= (X_0, Y_0)$ and `state f l l.length` $= (X_n, Y_n)$. The update compares the gains by `removeGain ≤ addGain`, which is line 5's $a_i \ge b_i$ with ties going to "add". The step and the run are `noncomputable` only because comparison of real numbers is not computable in Lean.
-- source:
--   Buchbinder, Feldman, Naor, Schwartz, A Tight Linear Time (1/2)-Approximation for Unconstrained Submodular Maximization, FOCS 2012 version, §II, Algorithm 1 and the definition of OPT_i (PDF p. 3)

import Mathlib

namespace DoubleGreedyUSM.Deterministic

/-- The marginal gain `f(S.1 ∪ {u}) − f(S.1)` of adding `u` to the first solution of the state
`S = (X, Y)` (Buchbinder–Feldman–Naor–Schwartz, FOCS 2012, Algorithm 1, line 3: `aᵢ`). -/
def addGain {X : Type} [DecidableEq X] (f : Finset X → ℝ) (S : Finset X × Finset X) (u : X) : ℝ :=
  f (insert u S.1) - f S.1

/-- The marginal gain `f(S.2 \ {u}) − f(S.2)` of removing `u` from the second solution of the
state `S = (X, Y)` (Algorithm 1, line 4: `bᵢ`). -/
def removeGain {X : Type} [DecidableEq X] (f : Finset X → ℝ) (S : Finset X × Finset X) (u : X) :
    ℝ :=
  f (S.2.erase u) - f S.2

/-- One iteration of Algorithm 1 (DeterministicUSM) on the state `S = (X_{i-1}, Y_{i-1})` and the
element `u = u_i` (lines 3–6): if `a_i ≥ b_i` then `X_i = X_{i-1} ∪ {u_i}`, `Y_i = Y_{i-1}`;
otherwise `X_i = X_{i-1}`, `Y_i = Y_{i-1} \ {u_i}`. A tie `a_i = b_i` adds `u_i`. -/
noncomputable def step {X : Type} [DecidableEq X] (f : Finset X → ℝ) (S : Finset X × Finset X)
    (u : X) :
    Finset X × Finset X :=
  if removeGain f S u ≤ addGain f S u then (insert u S.1, S.2) else (S.1, S.2.erase u)

/-- The state `(X_i, Y_i)` of Algorithm 1 after its first `i` iterations, when the ground set is
scanned in the order of the list `l = [u₁, …, uₙ]`: start from `(X_0, Y_0) = (∅, 𝒩)` (line 1) and
apply `step` to `u₁, …, u_i`. For `i ≥ l.length` this is the final state `(X_n, Y_n)`; the
algorithm returns `X_n` (line 7). -/
noncomputable def state {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (l : List X)
    (i : ℕ) :
    Finset X × Finset X :=
  (l.take i).foldl (step f) (∅, Finset.univ)

/-- `OPT_i ≜ (OPT ∪ X_i) ∩ Y_i` for a set `O` (the optimal solution `OPT`) and a state
`S = (X_i, Y_i)` (§II, PDF p. 3). -/
def optI {X : Type} [DecidableEq X] (O : Finset X) (S : Finset X × Finset X) : Finset X :=
  (O ∪ S.1) ∩ S.2

end DoubleGreedyUSM.Deterministic


