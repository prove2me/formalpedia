-- Prove2me | Definitions.Def_RobustDP_ChiSquare_ChiSqSet
-- name    : RobustDP_ChiSquare_ChiSqSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:37:20.085527+00:00
-- url     : https://prove2.me/theorems/6d31bdc5-c479-43a8-b8f5-ae1c65020f05
-- title:
--   The χ² set of conditional measures (46) and the dual objective of (48)
-- statement:
--   Let $\mathcal S$ be a finite set and $\mathcal M(\mathcal S)=\{p\in\mathbb R^{\mathcal S}: p\ge 0,\ \sum_{s}p(s)=1\}$ the set of probability measures on $\mathcal S$. For a centre $q$ with $q(s)>0$ for all $s$ and a radius $t$, the **χ² distance** of a vector $p$ from $q$ and the **χ² set** (46) are
--
--   $$
--   \chi^2(p,q)=\sum_{s\in\mathcal S}\frac{(p(s)-q(s))^2}{q(s)},\qquad
--   \mathcal P=\Big\{p\in\mathcal M(\mathcal S):\ \sum_{s\in\mathcal S}\frac{(p(s)-q(s))^2}{q(s)}\le t\Big\}.
--   $$
--
--   For a value vector $v:\mathcal S\to\mathbb R$ and a multiplier $\mu:\mathcal S\to\mathbb R$, the **dual objective** of problem (48) is
--
--   $$
--   g_{q,t,v}(\mu)=\mathbf E^q[v-\mu]-\sqrt{t\,\mathbf{Var}^q[v-\mu]} .
--   $$
--
--   In Iyengar's robust dynamic programming the set $\mathcal P$ is the ambiguity set of one state–action pair: an inner (conservative) approximation of the relative-entropy confidence region around the empirical distribution $q$. Lemma 5 says that the worst-case expectation over $\mathcal P$ equals the maximum of $g_{q,t,v}$ over $\mu\ge 0$.
--
--   **Formalization Note** $\mathcal M(\mathcal S)$ is Mathlib's `stdSimplex ℝ S`. Lean's division gives $x/0=0$, so the χ² distance has its intended meaning only when $q(s)>0$ for every $s$; every theorem of the mission assumes this. The square root is `Real.sqrt`, which returns $0$ on negative inputs; the theorems assume $t\ge 0$, so its argument $t\,\mathbf{Var}^q[\cdot]$ is nonnegative.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), p. 18, eq. (46) (the set P) and eq. (48) (the dual objective)

import Mathlib
import Definitions.Def_RobustDP_ChiSquare_Moments

namespace RobustDP.ChiSquare

/-- The χ² distance `∑_{s ∈ S} (p(s) − q(s))² / q(s)` of (46) (Iyengar, TR-2002-07, p. 18).
It is used only with `q(s) > 0` for every `s`. -/
noncomputable def chiSqDist {S : Type*} [Fintype S] (p q : S → ℝ) : ℝ :=
  ∑ s, (p s - q s) ^ 2 / q s

/-- The set of conditional measures (46) (Iyengar, TR-2002-07, p. 18):
`P = {p ∈ M(S) : ∑_{s ∈ S} (p(s) − q(s))² / q(s) ≤ t}`, where `M(S)` is the probability simplex
`stdSimplex ℝ S` (nonnegative coordinates summing to `1`). -/
def chiSqSet {S : Type*} [Fintype S] (q : S → ℝ) (t : ℝ) : Set (S → ℝ) :=
  {p | p ∈ stdSimplex ℝ S ∧ chiSqDist p q ≤ t}

/-- The objective of the dual problem (48) (Iyengar, TR-2002-07, p. 18):
`E^q[v − μ] − √(t Var^q[v − μ])`, as a function of the multiplier `μ : S → ℝ`. -/
noncomputable def dualObj {S : Type*} [Fintype S] (q : S → ℝ) (t : ℝ) (v μ : S → ℝ) : ℝ :=
  expect q (v - μ) - Real.sqrt (t * variance q (v - μ))

end RobustDP.ChiSquare


