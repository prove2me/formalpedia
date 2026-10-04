-- Prove2me | Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
-- name    : NonsmoothLojasiewicz_Continuous_IsSubanalytic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:49:51.980497+00:00
-- url     : https://prove2.me/theorems/9f482c77-2da9-46f8-b445-8ba3901c0696
-- title:
--   Semianalytic and subanalytic sets, and subanalytic functions (Definition 2.1)
-- statement:
--   Let $X$ be a finite-dimensional real normed space (in the paper $X = \mathbb{R}^n$, $\mathbb{R}^n \times \mathbb{R}$ or $\mathbb{R}^n \times \mathbb{R}^m$).
--
--   1. A subset $A \subseteq X$ is **semianalytic** if every point of $X$ (not only of $A$) has an open neighbourhood $V$ such that
--   $$
--   A \cap V = \bigcup_{i=1}^{p} \bigcap_{j=1}^{q} \{x \in V : f_{ij}(x) = 0,\ g_{ij}(x) > 0\}
--   $$
--   for finitely many functions $f_{ij}, g_{ij} : V \to \mathbb{R}$ that are real-analytic on $V$.
--   2. A subset $A \subseteq X$ is **subanalytic** if every point of $X$ has a neighbourhood $V$ such that $A \cap V$ is the projection onto $X$ of a **bounded** semianalytic subset $B$ of $X \times \mathbb{R}^m$, for some $m \ge 1$:
--   $$
--   A \cap V = \{x \in X : (x, y) \in B \text{ for some } y \in \mathbb{R}^m\}.
--   $$
--   3. A function $f : X \to \mathbb{R} \cup \{+\infty\}$ is **subanalytic** if its graph
--   $$
--   \operatorname{Gr} f = \{(x, \lambda) \in X \times \mathbb{R} : f(x) = \lambda\}
--   $$
--   is a subanalytic subset of $X \times \mathbb{R}$.
--
--   Subanalytic sets contain the semialgebraic sets and the sets locally defined by real-analytic equations and inequalities; boundedness of $B$ in item 2 is essential, since projections of unbounded semianalytic sets need not be subanalytic. These are the classes for which the nonsmooth Łojasiewicz inequality is proved.
--
--   **Formalization Note.** The ambient space is any `[NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]`; products carry the sup norm, and neither real-analyticity (`AnalyticOnNhd ℝ`) nor boundedness depends on the choice of an equivalent norm. The functions $f_{ij}, g_{ij}$ are total functions `X → ℝ` required to be analytic on `V` only. The paper indexes $1 \le i \le p$, $1 \le j \le q$; the Lean statement allows $p = 0$ or $q = 0$ and intersects the union with $V$, which adds nothing because $\emptyset$ and $V$ already have the printed form. In item 1 the neighbourhood is taken open, which is harmless. The values $f(x) = +\infty$ are not points of the graph.
-- source:
--   Bolte, Daniilidis & Lewis, The Łojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205–1223, DOI 10.1137/050644641, p. 1207 (PDF p. 3), Definition 2.1 (i)–(iii)

import Mathlib

open Filter Topology

namespace NonsmoothLojasiewicz.Continuous

/-- Definition 2.1(i) of Bolte–Daniilidis–Lewis (SIAM J. Optim. 17 (2007), p. 1207):
a subset `A` of a finite-dimensional real normed space `X` is **semianalytic** if every point
`x₀` of `X` (not only of `A`) has an open neighbourhood `V` on which `A` is a finite union of
finite intersections of sets `{x ∈ V : F i j x = 0, G i j x > 0}`, with all `F i j`, `G i j`
real-analytic on `V`. The page indexes `1 ≤ i ≤ p`, `1 ≤ j ≤ q`; allowing `p = 0` or `q = 0`
adds nothing (`∅` and `V` already have the printed form, e.g. `{x ∈ V : 0 = 0, 1 > 0}`). -/
def IsSemianalytic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (A : Set X) : Prop :=
  ∀ x₀ : X, ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧
    ∃ (p q : ℕ) (F G : Fin p → Fin q → X → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (F i j) V ∧ AnalyticOnNhd ℝ (G i j) V) ∧
      A ∩ V = V ∩ ⋃ i : Fin p, ⋂ j : Fin q, {x | F i j x = 0 ∧ 0 < G i j x}

/-- Definition 2.1(ii) (p. 1207): a subset `A` of `X` is **subanalytic** if every point `x₀` of
`X` has a neighbourhood `V` such that `A ∩ V` is the projection onto `X` of a **bounded**
semianalytic subset `B` of `X × ℝᵐ` for some `m ≥ 1`. -/
def IsSubanalytic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (A : Set X) : Prop :=
  ∀ x₀ : X, ∃ V ∈ 𝓝 x₀, ∃ m : ℕ, 1 ≤ m ∧
    ∃ B : Set (X × EuclideanSpace ℝ (Fin m)),
      IsSemianalytic B ∧ Bornology.IsBounded B ∧ A ∩ V = Prod.fst '' B

/-- Definition 2.1(iii) (p. 1207): a function `f : ℝⁿ → ℝ ∪ {+∞}` (here `f : X → EReal`) is
**subanalytic** if its graph `Gr f = {(x, λ) ∈ X × ℝ : f x = λ}` is a subanalytic subset of
`X × ℝ`. Points where `f x = +∞` are not in the graph. -/
def IsSubanalyticFn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (f : X → EReal) : Prop :=
  IsSubanalytic {p : X × ℝ | f p.1 = (p.2 : EReal)}

end NonsmoothLojasiewicz.Continuous


