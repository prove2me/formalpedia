-- Prove2me | Definitions.Def_PriceCapacities_LowerBound_WeightedSets
-- name    : PriceCapacities_LowerBound_WeightedSets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:21:32.530548+00:00
-- url     : https://prove2.me/theorems/e0f84b9d-d091-44f2-8c74-2ac6919a0049
-- title:
--   Weighted point sets, weighted sums $f(W)$, total weight $\mathbf 1(W)$, size, unweighted sets (§2.2)
-- statement:
--   A **weighted point set** $W$ in a set $X$ is a finitely supported measure: a function $W:X\to\mathbb R_{\ge0}$ that is nonzero at only finitely many points. $W(x)$ is the weight of $x$, and $x\in W$ means that $x$ lies in the support $\operatorname{supp}W=\{x: W(x)>0\}$. For a real function $f$ on $X$,
--   $$f(W)=\sum_{x\in W}W(x)\,f(x),$$
--   so the total weight is $\mathbf 1(W)=\sum_{x\in W}W(x)$. The **size** of $W$ is $|\operatorname{supp}W|$, the number of distinct points of positive weight. A finite set $S\subseteq X$ is viewed as the **unweighted** set that gives every point of $S$ weight one, so $\mathbf 1(S)=|S|$. The **restriction** of $W$ to a set $s\subseteq X$ keeps the weights of the points of $W$ lying in $s$ and sets all others to zero.
--
--   These are the conventions of §2.2: coresets are weighted point sets, and the input of the lower bound is an unweighted set.
--
--   **Formalization Note.** `WeightedSet X = X →₀ ℝ≥0`; `wsum W f` is $f(W)$, `totalWeight W` is $\mathbf 1(W)$, `size W = W.support.card`, `unweighted S = Σ_{x∈S} single x 1`, `restrict W s = W.filter (· ∈ s)`.
-- source:
--   Prabhu, Schwiegelshohn, Shyam, The Price of Capacities for Clustering Coresets, STOC 2027 submission (manuscript sha256 ec35f5ef…), p. 5, §2.2; p. 5, Definition 2.2 (size)

import Mathlib

open scoped BigOperators NNReal

namespace PriceCapacities.LowerBound

/-!
# Weighted point sets (§2.2)

Prabhu, Schwiegelshohn, Shyam, *The Price of Capacities for Clustering Coresets*, STOC 2027
submission (manuscript sha256 ec35f5ef…), p. 5, §2.2.

* A weighted point set `W` in `X` is a finitely supported nonnegative weight function
  `X →₀ ℝ≥0` (a finitely supported measure); `W x` is the weight of `x`, zero outside the
  support, and `x ∈ W` means `x ∈ W.support` (the points of positive weight).
* `wsum W f = f(W) = Σ_{x ∈ W} W(x) f(x)`; `totalWeight W = 1(W)`.
* `size W` is the number of distinct points with positive weight.
* `unweighted S` gives every point of the finite set `S` weight one.
* `restrict W s` is the restriction of `W` to the points of `W` lying in `s`.
-/

/-- A weighted point set in `X`: a finitely supported nonnegative weight function. -/
abbrev WeightedSet (X : Type*) := X →₀ ℝ≥0

/-- The weighted sum `f(W) = Σ_{x ∈ W} W(x) f(x)`. -/
noncomputable def wsum {X : Type*} (W : WeightedSet X) (f : X → ℝ) : ℝ :=
  ∑ x ∈ W.support, (W x : ℝ) * f x

/-- The total weight `1(W) = Σ_{x ∈ W} W(x)`. -/
noncomputable def totalWeight {X : Type*} (W : WeightedSet X) : ℝ :=
  wsum W (fun _ => 1)

/-- The size of `W`: the number of distinct points with positive weight. -/
def size {X : Type*} (W : WeightedSet X) : ℕ :=
  W.support.card

/-- The unweighted set `S`: every point of the finite set `S` has weight one. -/
noncomputable def unweighted {X : Type*} (S : Finset X) : WeightedSet X :=
  ∑ x ∈ S, Finsupp.single x 1

/-- The restriction of `W` to the points lying in `s` (weights outside `s` set to zero). -/
noncomputable def restrict {X : Type*} (W : WeightedSet X) (s : Set X) : WeightedSet X := by
  classical exact W.filter (· ∈ s)

end PriceCapacities.LowerBound


