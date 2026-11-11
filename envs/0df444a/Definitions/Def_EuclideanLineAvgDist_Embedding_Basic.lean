-- Prove2me | Definitions.Def_EuclideanLineAvgDist_Embedding_Basic
-- name    : EuclideanLineAvgDist_Embedding_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:33.79352+00:00
-- url     : https://prove2.me/theorems/b9b9d23e-3635-42b6-b07f-037617eb49dd
-- title:
--   Finite metric spaces, line embeddings, average distortion, open balls and minimum matchings
-- statement:
--   Basic objects for non-expansive embeddings of finite metric spaces into the line.
--
--   Let $(X,d)$ be a finite metric space with $n=|X|$ points. All sums below run over **ordered** pairs, the diagonal included.
--
--   1. $\mathbb R^k$ denotes $k$-dimensional real Euclidean space with the Euclidean norm $\|\cdot\|_2$ and inner product $\langle\cdot,\cdot\rangle$. A finite set $X\subset\mathbb R^k$ is regarded as the finite metric space $(X,\|x-y\|_2)$.
--   2. The distance sum and the average distance are
--   $$S_d=\sum_{x,y\in X} d(x,y),\qquad \Delta=\frac{1}{n^2}\sum_{x,y\in X}d(x,y).$$
--   3. An embedding into the line is any map $f:X\to\mathbb R$ (injectivity is not required). Its spread is $S_f=\sum_{x,y\in X}|f(x)-f(y)|$, and its average distortion is $\operatorname{avd}(f)=S_d/S_f$. The map is **non-expansive** if $|f(x)-f(y)|\le d(x,y)$ for all $x,y\in X$.
--   4. The open ball is $B(x,r)=\{y\in X: d(x,y)<r\}$.
--   5. For a nonempty finite set $S\subseteq X$, $d(x,S)=\min_{y\in S}d(x,y)$.
--   6. A perfect matching between finite subsets $A,B\subseteq X$ is a bijection $M:A\to B$; its weight is $\sum_{a\in A}d(a,M(a))$. It is of minimum weight if no bijection $A\to B$ has smaller weight. The minimum weight of a perfect matching between $A$ and $B$ is the minimum of the weight over all bijections $A\to B$.
--   7. The rate $\log n/\log\log n$ (natural logarithms) is continued to all $n$ as
--   $$\rho(n)=\frac{\log \max(3,n)}{\log\log \max(3,n)},$$
--   which equals $\log n/\log\log n$ for $n\ge 3$ and is positive for every $n$.
--
--   These are the objects of Theorem 1.1, Lemma 1.7, Corollary 2.2 and Lemma 3.1.
--
--   **Formalization Note** The ratio $\operatorname{avd}(f)$ is never formed; theorems state $S_d\le \beta\, S_f$ instead. The distance to the empty set is given the value $0$, and the minimum over an empty set of bijections the value $0$; neither value is reached by the statements of the mission, whose sets are nonempty, respectively of equal size. The ball is open; the source does not specify open or closed.
-- source:
--   Jack Spalding-Jamieson, STOC 2027 submission #1643 (October 2026), p. 1, §1 (embedding, non-expansive, avd), p. 5, Lemma 1.7 and Corollary 2.2 (Δ, B(x, r), d(x, B), minimum-weight perfect matching), p. 6, Lemma 3.1

import Mathlib

open scoped BigOperators
set_option autoImplicit false

namespace EuclideanLineAvgDist.Embedding

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Real `k`-dimensional Euclidean space `ℝᵏ`, with the Euclidean (ℓ²) norm and inner product. -/
abbrev Eucl (k : ℕ) := EuclideanSpace ℝ (Fin k)

section FiniteMetric

variable (X : Type*) [PseudoMetricSpace X] [Fintype X]

/-- `S_d = ∑_{x,y ∈ X} d(x,y)`, the sum of all distances over ordered pairs (diagonal included). -/
def distSum : ℝ := ∑ x : X, ∑ y : X, dist x y

/-- `Δ = (1/n²) ∑_{x,y ∈ X} d(x,y)` with `n = |X|`. -/
def avgDist : ℝ := distSum X / (Fintype.card X : ℝ) ^ 2

variable {X}

/-- `S_f = ∑_{x,y ∈ X} |f(x) - f(y)|`, the sum of line distances over ordered pairs. -/
def lineSpread (f : X → ℝ) : ℝ := ∑ x : X, ∑ y : X, |f x - f y|

/-- A map into the line is non-expansive (1-Lipschitz): `|f(x) - f(y)| ≤ d(x,y)` for all `x, y`. -/
def NonExpansive (f : X → ℝ) : Prop := ∀ x y : X, |f x - f y| ≤ dist x y

/-- The open ball `B(x,r) = {y ∈ X : d(x,y) < r}`, as a finite subset of `X`. -/
def ball (x : X) (r : ℝ) : Finset X := Finset.univ.filter (fun y => dist x y < r)

/-- Distance from `x` to a finite set `S`: the minimum of `d(x,y)` over `y ∈ S` when `S` is
nonempty (the value `0` on the empty set is never used by the statements of this mission). -/
def distToFinset (S : Finset X) (x : X) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun y => dist x y) else 0

/-- Total weight `∑_{a ∈ A} d(a, M(a))` of a perfect matching `M : A ≃ B` between finite subsets. -/
def matchingCost {A B : Finset X} (M : A ≃ B) : ℝ := ∑ a : A, dist (a : X) (M a : X)

/-- `M` is a minimum-weight perfect matching between `A` and `B`. -/
def IsMinMatching {A B : Finset X} (M : A ≃ B) : Prop :=
  ∀ M' : A ≃ B, matchingCost M ≤ matchingCost M'

/-- The minimum weight of a perfect matching between `A` and `B` (a minimum over the finitely many
bijections `A ≃ B`, attained whenever `|A| = |B|`; the value is `0` when no bijection exists). -/
def minMatchingCost (A B : Finset X) : ℝ := ⨅ M : (A ≃ B), matchingCost M

end FiniteMetric

/-- The rate `log n / log log n`, continued to all `n` by replacing `n` with `max 3 n`
(natural logarithms); for `n ≥ 3` it is exactly `log n / log log n`, and it is positive for all `n`. -/
def logRate (n : ℕ) : ℝ :=
  Real.log (max 3 (n : ℝ)) / Real.log (Real.log (max 3 (n : ℝ)))

end

end EuclideanLineAvgDist.Embedding


