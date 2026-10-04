-- Prove2me | Definitions.Def_ProjLikeRetr_Spectral_IsSubmanifold
-- name    : ProjLikeRetr_Spectral_IsSubmanifold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:41:53.696968+00:00
-- url     : https://prove2.me/theorems/3f74676c-eb3f-4311-9b80-085b56caac37
-- title:
--   §2.1, p. 3 — $\mathcal M$ is a $C^k$ submanifold of dimension $d$ (coordinate slice charts)
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $N$, let $\mathcal M \subseteq E$, let $k, d \in \mathbb N$ and $\bar x \in E$.
--
--   We say that $\mathcal M$ is a **submanifold of $E$ of class $C^k$ and dimension $d$ around $\bar x$** if $\bar x \in \mathcal M$ and there is a chart $\varphi : U \to V$, a homeomorphism from an open set $U \ni \bar x$ of $E$ onto an open set $V \subseteq \mathbb R^N$, such that $\varphi$ is $C^k$ on $U$, $\varphi^{-1}$ is $C^k$ on $V$, and in this chart $\mathcal M$ is a coordinate slice:
--   $$
--   \mathcal M \cap U = \{\, x \in U : \varphi_i(x) = 0 \text{ for every coordinate index } i > d \,\}.
--   $$
--   We say that $\mathcal M$ is a **submanifold of $E$ of class $C^k$ and dimension $d$** if $d \le N$ and $\mathcal M$ is such a submanifold around each of its points.
--
--   This is the standard notion of an embedded submanifold used throughout the paper (§2.1: "$\mathcal M$ stands for a submanifold of $\mathcal E$ of class $C^k$ ($k \ge 2$) and of dimension $d$"). In this mission $E = \mathbb R^n$ with the Euclidean norm, and the hypothesis of Theorem 3.5 is that $\mathcal M$ is a $C^2$ submanifold of $\mathbb R^n$.
--
--   **Formalization Note** The chart is an `OpenPartialHomeomorph` into `EuclideanSpace ℝ (Fin N)` with `N = finrank ℝ E`; coordinate indices are 0-based, so "index $i > d$" is `d ≤ i.val`. The two predicates are `IsSubmanifoldAt k d M x̄` (around a point) and `IsSubmanifold k d M` (everywhere, with `d ≤ N`).
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 3, §2.1

import Mathlib

namespace ProjLikeRetr.Spectral

/-- `M` is a `C^k` submanifold of dimension `d` of the Euclidean space `E` around `x̄`
(§2.1, p. 3): `x̄ ∈ M` and there is a `C^k` chart `φ` of `E` around `x̄`, with `C^k` inverse,
in which `M` is the coordinate slice `{φ x i = 0 for every index i ≥ d}` (0-based indices). -/
def IsSubmanifoldAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (xbar : E) : Prop :=
  xbar ∈ M ∧ ∃ φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
    xbar ∈ φ.source ∧ ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source ∧
    ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target ∧
    M ∩ φ.source = {x ∈ φ.source | ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ x i = 0}

/-- `M` is a `C^k` submanifold of dimension `d ≤ dim E` of `E` (§2.1, p. 3): it is a
`C^k` submanifold of dimension `d` around each of its points. -/
def IsSubmanifold {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) : Prop :=
  d ≤ Module.finrank ℝ E ∧ ∀ x ∈ M, IsSubmanifoldAt k d M x

end ProjLikeRetr.Spectral


