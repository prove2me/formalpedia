-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_Supplement_SparsifierModel
-- name    : BourgainUnion_Euclidean_Supplement_SparsifierModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:33.70946+00:00
-- url     : https://prove2.me/theorems/673b7752-8e4d-4df7-80ac-00a5ea3706ea
-- title:
--   Euclidean metric sparsifiers, $Q(\mathcal D,A)$, $e(\mathcal D,A)$, $Q_k$, $e_k$
-- statement:
--   Let $X$ be a finite set, $U_1,\dots,U_k$ a partition of $X$ into nonempty sets, and $\mathcal D$ the class of pseudometrics on $X$ whose restriction to every $U_j$ is Euclidean. Fix $A=U_i$.
--
--   1. A weighted graph $H$ on $A$ (nonnegative symmetric weights, zero diagonal, no weight outside $A\times A$) is a **Euclidean metric sparsifier** of a weighted graph $G$ on $X$ with **quality** $Q\ge1$ if, for every Euclidean pseudometric $\rho$ on $A$,
--   $$\frac1Q E_H(\rho^2)\le \operatorname{min\text{-}ext}_{\mathcal D}(\rho,G)\le E_H(\rho^2),$$
--   with the same $H$ for every $\rho$ (Definition 4.1, inequality (4)); $\operatorname{min\text{-}ext}_{\mathcal D}$ is the published optimal extension cost (3).
--   2. $Q(\mathcal D,A)$ is the least $Q$ such that every loopless weighted graph $G$ on $X$ has a sparsifier of quality $Q$.
--   3. $e(\mathcal D,A)$ is the least $\Lambda\ge1$ such that for every $d\in\mathcal D$, every $L\ge0$ and every map $f:A\to\ell_2$ that is $L$-Lipschitz for $d$, some $F:X\to\ell_2$ extends $f$ and is $\Lambda L$-Lipschitz for $d$ on all of $X$.
--   4. $Q_k$ and $e_k$ are the suprema of $Q(\mathcal D,A)$ and $e(\mathcal D,A)$ over all finite sets $X$, all partitions of $X$ into at most $k$ nonempty sets, and all choices $A=U_i$.
--
--   All four quantities take values in $[0,\infty]$: an infimum over an empty set of admissible constants is $\infty$.
--
--   **Formalization Note** Lipschitz conditions in $e(\mathcal D,A)$ are with respect to the varying pseudometric $d$, not a fixed metric instance; the suprema range over finite types in `Type`.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 13–14, §4.1, equation (3), Definition 4.1, inequality (4), definitions of Q(D,A), e(D,A), Q_k, e_k

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_GraphModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

open BourgainUnion.Euclidean

/-- Definition 4.1, p. 13: `h` is a weighted graph on `A` (nonnegative, symmetric, zero diagonal,
no weight outside `A × A`) and a Euclidean metric sparsifier of the graph with weights `w` for the
class `D` of `U`, with quality `Q ≥ 1`: inequality (4) holds for every Euclidean `ρ` on `A`, with
the same `h` for all such `ρ`. -/
def IsSparsifier {X : Type*} [Fintype X] {k : ℕ} (U : Fin k → Set X) (A : Finset X)
    (w h : X → X → ℝ) (Q : ℝ) : Prop :=
  1 ≤ Q ∧ (∀ x y, 0 ≤ h x y) ∧ (∀ x y, h x y = h y x) ∧ (∀ x, h x x = 0) ∧
  (∀ x y, x ∉ A ∨ y ∉ A → h x y = 0) ∧
  ∀ ρ : X → X → ℝ, RawEuclidean ρ (A : Set X) →
    ENNReal.ofReal (energy h ρ A / Q) ≤ minExt U A ρ w ∧
      minExt U A ρ w ≤ ENNReal.ofReal (energy h ρ A)

/-- `Q(D, A)`, p. 13: the least quality guaranteed for every (loopless) weighted graph on `X`;
`⊤` when no finite quality works. -/
def sparsifierQuality {X : Type*} [Fintype X] {k : ℕ} (U : Fin k → Set X) (A : Finset X) :
    ℝ≥0∞ :=
  sInf {q | ∃ Q : ℝ, (∀ G : ClusterDecomp.WGraph X, Loopless G →
      ∃ h : X → X → ℝ, IsSparsifier U A G.w h Q) ∧ q = ENNReal.ofReal Q}

/-- `e(D, A)`, pp. 13–14: the least `Λ ≥ 1` such that, for every pseudometric `d` in the class
`D` of `U`, every `L`-Lipschitz map `(A, d) → ℓ₂` extends to a `ΛL`-Lipschitz map `(X, d) → ℓ₂`.
Lipschitz conditions are with respect to `d`, which varies over the class. -/
def extensionConstantD {X : Type*} {k : ℕ} (U : Fin k → Set X) (A : Set X) : ℝ≥0∞ :=
  sInf {q | ∃ Λ : ℝ, 1 ≤ Λ ∧
    (∀ d : X → X → ℝ, MetricClass U d → ∀ L : ℝ, 0 ≤ L → ∀ f : X → H2,
      (∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ L * d x y) →
      ∃ F : X → H2, Set.EqOn F f A ∧ ∀ x y, dist (F x) (F y) ≤ Λ * L * d x y) ∧
    q = ENNReal.ofReal Λ}

/-- `Q_k`, p. 14: the supremum of `Q(D, A)` over finite sets `X`, partitions of `X` into at most
`k` nonempty sets, and choices `A = U_i`. -/
def Qk (k : ℕ) : ℝ≥0∞ :=
  ⨆ (X : Type) (_ : Fintype X) (j : ℕ) (_ : j ≤ k) (U : Fin j → Set X) (_ : Partition U)
    (i : Fin j), sparsifierQuality U (U i).toFinite.toFinset

/-- `e_k`, p. 14: the supremum of `e(D, A)` over the same data as `Q_k`. -/
def ek (k : ℕ) : ℝ≥0∞ :=
  ⨆ (X : Type) (_ : Fintype X) (j : ℕ) (_ : j ≤ k) (U : Fin j → Set X) (_ : Partition U)
    (i : Fin j), extensionConstantD U (U i)

end BourgainUnion.Euclidean.Supplement


