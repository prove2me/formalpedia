-- Prove2me | Definitions.Def_StochApproxDyn_LimitSet_ChainRecurrence
-- name    : StochApproxDyn_LimitSet_ChainRecurrence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:02:25.362982+00:00
-- url     : https://prove2.me/theorems/3b384067-601a-4317-9d01-46a0032ebed5
-- title:
--   $(\delta,T)$-pseudo-orbits, chain recurrence, internally chain recurrent and internally chain transitive sets
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $(X,d)$, and let $\delta>0$, $T>0$. A **$(\delta,T)$-pseudo-orbit** from $a\in X$ to $b\in X$ is a finite sequence of partial trajectories
--   $$\{\Phi_t(y_i):0\le t\le t_i\},\qquad i=0,\dots,k-1,\qquad t_i\ge T,$$
--   with $k\ge1$, such that
--   $$d(y_0,a)<\delta,\qquad d(\Phi_{t_j}(y_j),y_{j+1})<\delta\ \ (j=0,\dots,k-1),\qquad y_k=b .$$
--   We write $a\hookrightarrow_{\delta,T}b$ if such a pseudo-orbit exists, and $a\hookrightarrow b$ if $a\hookrightarrow_{\delta,T}b$ for every $\delta>0$ and $T>0$. A point with $a\hookrightarrow a$ is **chain recurrent**, and $R(\Phi)$ denotes the set of chain recurrent points.
--
--   Now let $\Phi$ be a semiflow on a metric space $M$ and $\Lambda\subset M$.
--
--   1. $\Lambda$ is **internally chain recurrent** if it is nonempty, compact and invariant ($\Phi_t(\Lambda)=\Lambda$ for all $t\ge0$), and every $p\in\Lambda$ is chain recurrent for the restricted semiflow $\Phi|\Lambda$, i.e. $\Lambda=R(\Phi|\Lambda)$.
--   2. $\Lambda$ is **internally chain transitive** if it is nonempty, compact and invariant, and $a\hookrightarrow b$ for $\Phi|\Lambda$ for all $a,b\in\Lambda$.
--
--   The pseudo-orbits of $\Phi|\Lambda$ have all their points $y_i$ in $\Lambda$; this is what makes the notion *internal*. The limit set of a precompact asymptotic pseudotrajectory is internally chain transitive (Theorem 5.7 (i)), and on a locally path connected space every internally chain transitive set arises this way (Theorem 5.7 (ii)), which is why they organize the long-run analysis of stochastic approximation algorithms.
--
--   **Formalization Note** A pseudo-orbit is encoded by its length $k$ with $1\le k$, points `y : ℕ → X` (only $y_0,\dots,y_k$ matter) and times `t : ℕ → ℝ≥0` (only $t_0,\dots,t_{k-1}$ matter); $T$ is a positive element of `ℝ≥0`. The requirement $k\ge1$ excludes the degenerate chain with no trajectory piece. Nonemptiness of $\Lambda$ is part of both definitions, following the source's sentence "Let $\Lambda\subset M$ be a nonempty invariant set". The restriction $\Phi|\Lambda$ is a semiflow on the subtype $\Lambda$ with the inherited metric, so its pseudo-orbits are those of $\Phi$ with all points in $\Lambda$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 21, Section 5.1 "Chain Recurrence and Attractors" ((δ,T)-pseudo-orbits, chain recurrence, R(Φ), internally chain recurrent / transitive sets)

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Invariance

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- A `(δ,T)`-pseudo-orbit from `a` to `b` (Benaïm 1999, p. 21), given by its length `k`, its
points `y 0, …, y k` and its times `t 0, …, t (k-1)`: there is at least one partial trajectory
(`1 ≤ k`), every time satisfies `t_i ≥ T`, `d(y_0, a) < δ`, `d(Φ_{t_j}(y_j), y_{j+1}) < δ` for
`j = 0, …, k-1`, and `y_k = b` exactly. -/
def IsPseudoOrbit {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (δ : ℝ) (T : ℝ≥0) (a b : X)
    (k : ℕ) (y : ℕ → X) (t : ℕ → ℝ≥0) : Prop :=
  1 ≤ k ∧ (∀ i < k, T ≤ t i) ∧ dist (y 0) a < δ ∧
    (∀ j < k, dist (Φ (t j) (y j)) (y (j + 1)) < δ) ∧ y k = b

/-- `a ↪_{δ,T} b`: there exists a `(δ,T)`-pseudo-orbit from `a` to `b`. -/
def PseudoOrbitTo {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (δ : ℝ) (T : ℝ≥0) (a b : X) :
    Prop :=
  ∃ (k : ℕ) (y : ℕ → X) (t : ℕ → ℝ≥0), IsPseudoOrbit Φ δ T a b k y t

/-- `a ↪ b`: `a ↪_{δ,T} b` for every `δ > 0` and `T > 0`. -/
def ChainTo {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) (a b : X) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ T : ℝ≥0, 0 < T → PseudoOrbitTo Φ δ T a b

/-- `R(Φ)`, the set of chain recurrent points `a ↪ a`. -/
def chainRecurrentSet {X : Type*} [MetricSpace X] (Φ : Flow ℝ≥0 X) : Set X :=
  {a | ChainTo Φ a a}

/-- An *internally chain recurrent* set (p. 21): a nonempty compact invariant set `Λ` such that
every point of `Λ` is chain recurrent for the restricted semiflow `Φ|Λ` (pseudo-orbits of `Φ|Λ`
have all their points in `Λ`). -/
def IsInternallyChainRecurrent {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Λ : Set M) :
    Prop :=
  Λ.Nonempty ∧ IsCompact Λ ∧
    ∃ h : IsInvariantSet Φ Λ, ∀ p : Λ, ChainTo (restrictSemiflow Φ h) p p

/-- An *internally chain transitive* set (p. 21): a nonempty compact invariant set `Λ` such that
`Φ|Λ` is chain transitive, i.e. `a ↪ b` for `Φ|Λ` for all `a, b ∈ Λ`. -/
def IsInternallyChainTransitive {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M) (Λ : Set M) :
    Prop :=
  Λ.Nonempty ∧ IsCompact Λ ∧
    ∃ h : IsInvariantSet Φ Λ, ∀ a b : Λ, ChainTo (restrictSemiflow Φ h) a b

end StochApproxDyn.LimitSet


