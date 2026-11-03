-- Prove2me | Definitions.Def_DNNProj_Basics
-- name    : DNNProj_Basics
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:14:45.068888+00:00
-- url     : https://prove2.me/theorems/bb18ab67-fc10-4dcb-a243-451e734866aa
-- title:
--   Convex-analysis vocabulary: indicator, subdifferential, normal and polar cones, polyhedral sets and maps, metric subregularity, bounded linear regularity
-- statement:
--   Let $E$ be a real inner-product space (the paper's $\mathbb X$, $\mathbb Y$ are finite-dimensional).
--
--   1. For a set-valued map $\Gamma:\mathbb U\rightrightarrows\mathbb V$, the **graph** is $\operatorname{gph}\Gamma=\{(u,v)\mid v\in\Gamma(u)\}$ and the **inverse** is $\Gamma^{-1}(v)=\{u\mid v\in\Gamma(u)\}$.
--   2. The **indicator** of $D$ is $\delta_D(x)=0$ for $x\in D$ and $\delta_D(x)=+\infty$ otherwise.
--   3. The **subdifferential** $\partial f(x)$ is the set of $v$ with $f(x')\ge f(x)+\langle v,x'-x\rangle$ for all $x'$, at points where $f(x)$ is finite (empty elsewhere).
--   4. The **normal cone** of $D$ at $x\in D$ is $\mathcal N_D(x)=\{v\mid\langle v,d-x\rangle\le0\ \forall d\in D\}$ (empty for $x\notin D$), and the **polar** of $D$ is $D^\circ=\{x\mid\langle x,d\rangle\le0\ \forall d\in D\}$.
--   5. A **polyhedral convex set** is an intersection of finitely many closed half-spaces $\{z\mid\varphi_i(z)\le\beta_i\}$; a **convex polyhedral cone** is a polyhedral set that is a cone; a set-valued map is **polyhedral** if its graph is a finite union of polyhedral convex sets.
--   6. **Definition 2.** $F:\mathbb X\rightrightarrows\mathbb Y$ is **metrically subregular** at $\bar x$ for $\bar y$ with modulus $\kappa>0$ if $(\bar x,\bar y)\in\operatorname{gph}F$ and for some $\varepsilon>0$
--   $$\operatorname{dist}(x,F^{-1}(\bar y))\le\kappa\,\operatorname{dist}(\bar y,F(x))\qquad\forall x\in\mathbb B_\varepsilon(\bar x).$$
--   7. **Definition 3.** Closed convex sets $D_1,\dots,D_m$ ($m\ge1$) with nonempty intersection $D$ are **boundedly linearly regular** if for every bounded $B$ there is $\kappa>0$ with
--   $$\operatorname{dist}(x,D)\le\kappa\max\{\operatorname{dist}(x,D_1),\dots,\operatorname{dist}(x,D_m)\}\qquad\forall x\in B.$$
--
--   These are the objects in which every statement of §3.1 is phrased. A **closed proper convex** function (lower semicontinuous, convex epigraph, never $-\infty$, not identically $+\infty$) is the published `TensorAHPE.IsProperClosedConvex`, referenced by this mission.
--
--   **Formalization Note** Extended values are `EReal`. In Definition 2 both distances are `Metric.infEDist`, so that $\operatorname{dist}(\bar y,\emptyset)=+\infty$. $\mathbb B_\varepsilon$ is the closed ball. In Definition 3 the sets are indexed by `Fin m` and the maximum is a supremum over a nonempty finite index set.
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, §1 notation p.4 (dist, δ_D, N_D, D°, gph, 𝔹_ε); §3.1 Definition 2 p.7, polyhedral mappings p.7, Definition 3 p.8, problem (9) p.8 (convex polyhedral cone)

import Mathlib

open scoped RealInnerProductSpace

namespace DNNProj

/-! # Convex-analysis vocabulary of Cui–Liang–Sun–Toh, §1 and §3.1

Y. Cui, L. Liang, D. Sun, K.-C. Toh, *On Degenerate Doubly Nonnegative Projection Problems*,
arXiv:2009.11272v2, §1 (notation, p.4), §3.1 (Definitions 2–3 and the polyhedral notions,
pp.7–8).

**Formalization Note.** The paper's spaces 𝕌, 𝕍, 𝕏, 𝕐 are finite-dimensional real Euclidean
spaces. The definitions below are stated on a real inner-product space `E` (or, where no inner
product is needed, a real vector space or a pseudo-metric space); the theorems add
`[FiniteDimensional ℝ E]` where the paper's standing convention requires it. Extended-real valued
functions `(−∞, +∞]` take values in `EReal`. "Closed proper convex" is the published
`TensorAHPE.IsProperClosedConvex` (never `−∞`, not identically `+∞`, lower semicontinuous,
convex epigraph). A set-valued map `F : 𝕌 ⇒ 𝕍` is a function
`U → Set V`; its inverse `F⁻¹(v)` is `{u | v ∈ F u}`. -/

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The graph `gph Γ ≜ {(u, v) ∈ 𝕌 × 𝕍 | v ∈ Γ(u)}` of a set-valued map (arXiv:2009.11272v2,
§1, p.4 and §3.1, p.7). -/
def gph {U V : Type*} (Γ : U → Set V) : Set (U × V) := {q | q.2 ∈ Γ q.1}

/-- The inverse `Γ⁻¹(v) = {u | v ∈ Γ(u)}` of a set-valued map (used in Definition 2, p.7, and
in `(∂p)⁻¹(v)`, Assumption 1, p.9). -/
def invMap {U V : Type*} (Γ : U → Set V) (v : V) : Set U := {u | v ∈ Γ u}

open Classical in
/-- The indicator function `δ_D` (arXiv:2009.11272v2, §1, p.4): `δ_D(x) = 0` if `x ∈ D` and
`δ_D(x) = ∞` if `x ∉ D`. -/
def indicatorE {V : Type*} (D : Set V) (x : V) : EReal := if x ∈ D then 0 else ⊤

/-- The (convex-analysis) subdifferential `∂f(x)` of `f : E → (−∞, +∞]`:
`v ∈ ∂f(x)` iff `f(x)` is finite and `f(x') ≥ f(x) + ⟨v, x' − x⟩` for all `x'`.
**Formalization Note.** `∂f(x) = ∅` where `f(x)` is not finite (for a proper `f`: off `dom f`),
the standard convention; `f(x)` enters as the real number `(f x).toReal`. -/
def subdiff (f : E → EReal) (x : E) : Set E :=
  {v | f x ≠ ⊤ ∧ f x ≠ ⊥ ∧ ∀ x', ((((f x).toReal + ⟪v, x' - x⟫ : ℝ)) : EReal) ≤ f x'}

/-- The normal cone `N_D(x)` of a convex set `D` at `x` (arXiv:2009.11272v2, §1, p.4):
`{v | ⟨v, d − x⟩ ≤ 0 ∀ d ∈ D}` for `x ∈ D`.
**Formalization Note.** The paper defines `N_D(x)` only for `x ∈ D`; here `N_D(x) = ∅` for
`x ∉ D`, which is the convention `N_D = ∂δ_D`. -/
def normalCone (D : Set E) (x : E) : Set E :=
  {v | x ∈ D ∧ ∀ d ∈ D, ⟪v, d - x⟫ ≤ 0}

/-- The polar cone `D° ≜ {x ∈ 𝕏 | ⟨x, d⟩ ≤ 0, ∀ d ∈ D}` (arXiv:2009.11272v2, §1, p.4). -/
def polar (D : Set E) : Set E := {x | ∀ d ∈ D, ⟪x, d⟫ ≤ 0}

/-- A **polyhedral convex set**: the intersection of finitely many closed half-spaces
`{z | φᵢ z ≤ βᵢ}` with `φᵢ` linear functionals (the standard notion used in §3.1, p.7, and in
Proposition 7(a), p.11). With no half-space it is the whole space; `∅ = {z | 0 ≤ −1}` is
polyhedral. -/
def IsPolyhedral {V : Type*} [AddCommGroup V] [Module ℝ V] (C : Set V) : Prop :=
  ∃ (k : ℕ) (φ : Fin k → Module.Dual ℝ V) (β : Fin k → ℝ), C = {z | ∀ i, φ i z ≤ β i}

/-- A **convex polyhedral cone** (problem (9), p.8): a polyhedral convex set that is a cone
(contains `0` and is closed under multiplication by nonnegative scalars). -/
def IsPolyhedralCone {V : Type*} [AddCommGroup V] [Module ℝ V] (C : Set V) : Prop :=
  IsPolyhedral C ∧ (0 : V) ∈ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ z ∈ C, t • z ∈ C

/-- A set-valued map `F : 𝕏 ⇒ 𝕐` is **polyhedral** if its graph is the union of finitely many
polyhedral convex sets (arXiv:2009.11272v2, §3.1, p.7). -/
def IsPolyhedralMap {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    (F : U → Set V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Set (U × V)), (∀ i, IsPolyhedral (P i)) ∧ gph F = ⋃ i, P i

/-- **Definition 2** (arXiv:2009.11272v2, p.7). `F : 𝕏 ⇒ 𝕐` is metrically subregular at `x̄` for
`ȳ` with modulus `κ > 0` if `(x̄, ȳ) ∈ gph F` and there is `ε > 0` with
`dist(x, F⁻¹(ȳ)) ≤ κ dist(ȳ, F(x))` for all `x ∈ 𝔹_ε(x̄)` (closed ball).
**Formalization Note.** Distances are `Metric.infEDist` (values in `[0, ∞]`), so that
`dist(ȳ, ∅) = +∞` (the infimum over the empty set), as in the paper; `Metric.infDist` would
give `0` there and strengthen the property. -/
def MetricSubregularWith {U V : Type*} [PseudoMetricSpace U] [PseudoMetricSpace V]
    (F : U → Set V) (xbar : U) (ybar : V) (κ : ℝ) : Prop :=
  0 < κ ∧ ybar ∈ F xbar ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.closedBall xbar ε,
    Metric.infEDist x (invMap F ybar) ≤ ENNReal.ofReal κ * Metric.infEDist ybar (F x)

/-- `F` is metrically subregular at `x̄` for `ȳ` (for some modulus `κ > 0`, Definition 2, p.7);
the sense used in Propositions 3 and 8. -/
def MetricSubregular {U V : Type*} [PseudoMetricSpace U] [PseudoMetricSpace V]
    (F : U → Set V) (xbar : U) (ybar : V) : Prop :=
  ∃ κ : ℝ, MetricSubregularWith F xbar ybar κ

/-- **Definition 3** (arXiv:2009.11272v2, p.8). For a positive integer `m` and closed convex sets
`D₁, …, D_m` with nonempty intersection `D`, the collection is **boundedly linearly regular** if
for every bounded set `B` there is `κ > 0` with
`dist(x, D) ≤ κ max{dist(x, D₁), …, dist(x, D_m)}` for all `x ∈ B`.
**Formalization Note.** The sets are indexed by `Fin m`; `0 < m`, closedness, convexity and
nonemptiness of `D` are clauses of the predicate, as in the definition. Every set involved is
nonempty, so `Metric.infDist` is the true distance, and the real `⨆` over `Fin m` with `m > 0` is
the maximum. -/
def BoundedLinRegular {m : ℕ} (D : Fin m → Set E) : Prop :=
  0 < m ∧ (∀ i, IsClosed (D i) ∧ Convex ℝ (D i)) ∧ (⋂ i, D i).Nonempty ∧
    ∀ B : Set E, Bornology.IsBounded B → ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ B,
      Metric.infDist x (⋂ i, D i) ≤ κ * ⨆ i, Metric.infDist x (D i)

end

end DNNProj


