-- Prove2me | Definitions.Def_ProjLikeRetr_Retractor_IsSubmanifold
-- name    : ProjLikeRetr_Retractor_IsSubmanifold
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:44:53.77357+00:00
-- url     : https://prove2.me/theorems/7c5664dd-5a3c-4672-873a-261d3f9961b6
-- title:
--   §2.1, p. 3 — C^k submanifold of dimension d of a Euclidean space (coordinate slice)
-- statement:
--   Let $\mathcal E$ be a Euclidean space of dimension $n$, and let $k\ge 0$ and $0\le d\le n$ be integers. A set $\mathcal M\subseteq\mathcal E$ is a **submanifold of $\mathcal E$ of class $C^k$ and of dimension $d$ around** a point $\bar x\in\mathcal M$ if $\mathcal M$ is a *coordinate slice* near $\bar x$: there exist an open neighbourhood $\mathcal U_{\mathcal E}$ of $\bar x$ in $\mathcal E$ and a $C^k$ diffeomorphism $\phi$ of $\mathcal U_{\mathcal E}$ onto an open subset of $\mathbb R^n$ such that
--
--   $$\mathcal M\cap\mathcal U_{\mathcal E}=\{x\in\mathcal U_{\mathcal E}:\ \phi_{d+1}(x)=\cdots=\phi_n(x)=0\}.$$
--
--   The set $\mathcal M$ is a **$C^k$ submanifold of dimension $d$** of $\mathcal E$ if this holds around every point of $\mathcal M$.
--
--   This is the standing assumption of the whole paper (with $k\ge2$): every result about retractions and retractors is stated for such an $\mathcal M$.
--
--   **Formalization Note** $n$ is `Module.finrank ℝ E` and $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`. The chart is an open partial homeomorphism whose source is $\mathcal U_{\mathcal E}$, with $\phi$ of class $C^k$ on its source and $\phi^{-1}$ of class $C^k$ on its (open) target. Coordinates are numbered from $0$, so the page's $\phi_{d+1},\dots,\phi_n$ are the coordinates of index $i\ge d$. The condition $d\le n$ is part of the definition (without it the slice condition is vacuous and a set of "dimension $d>n$" would just be an open set).
-- source:
--   Absil & Malick, Projection-like retractions on matrix manifolds, HAL hal-00651608v2, p. 3, §2.1 (Submanifolds)

import Mathlib

namespace ProjLikeRetr.Retractor

/-- §2.1, p. 3: `M` is, around `x̄ ∈ M`, a `C^k` submanifold of dimension `d` of the Euclidean
space `E` (of dimension `n = finrank ℝ E`), in the sense of a coordinate slice: there are an open
neighbourhood `U` of `x̄` and a `C^k` diffeomorphism `φ` of `U` onto an open subset of `ℝⁿ` with
`M ∩ U = {x ∈ U | φ_{d+1}(x) = ⋯ = φ_n(x) = 0}`. Coordinates are 0-based, so the page's
`φ_{d+1}, …, φ_n` are the coordinates `i` with `d ≤ i`. -/
def IsSubmanifoldAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) (xbar : E) : Prop :=
  d ≤ Module.finrank ℝ E ∧ xbar ∈ M ∧
    ∃ φ : OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))),
      xbar ∈ φ.source ∧ ContDiffOn ℝ (k : WithTop ℕ∞) φ φ.source ∧
      ContDiffOn ℝ (k : WithTop ℕ∞) φ.symm φ.target ∧
      M ∩ φ.source = {x | x ∈ φ.source ∧ ∀ i : Fin (Module.finrank ℝ E), d ≤ i.val → φ x i = 0}

/-- §2.1, p. 3: `M` is a `C^k` submanifold of dimension `d` of `E`: a coordinate slice around
each of its points. -/
def IsSubmanifold {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (k d : ℕ) (M : Set E) : Prop :=
  ∀ x ∈ M, IsSubmanifoldAt k d M x

end ProjLikeRetr.Retractor


