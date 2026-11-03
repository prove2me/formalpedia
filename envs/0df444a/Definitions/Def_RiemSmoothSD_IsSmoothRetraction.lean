-- Prove2me | Definitions.Def_RiemSmoothSD_IsSmoothRetraction
-- name    : RiemSmoothSD_IsSmoothRetraction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:45.037666+00:00
-- url     : https://prove2.me/theorems/abbcd4df-a9cc-4a88-8987-c311c5fb5a5d
-- title:
--   Retraction on $\mathcal M$ (Definition 2.1)
-- statement:
--   Let $\mathcal M$ be a subset of a finite-dimensional real inner product space $E$ with tangent spaces $T_x\mathcal M$ and tangent bundle $T\mathcal M=\{(x,\xi): x\in\mathcal M,\ \xi\in T_x\mathcal M\}$. A map $R:T\mathcal M\to\mathcal M$, $(x,\xi)\mapsto R_x(\xi)$, is a **retraction** if
--
--   1. $R$ is smooth ($C^\infty$) on $T\mathcal M$;
--   2. $R_x(\xi)\in\mathcal M$ for $\xi\in T_x\mathcal M$, and $R_x(0_x)=x$;
--   3. the differential of $R_x$ at $0_x$ is the identity of $T_x\mathcal M$:
--   $$
--   dR_x(0_x)=\mathrm{id}_{T_x\mathcal M}.
--   $$
--
--   Retractions are the first-order substitutes for the exponential map with which Riemannian line-search methods move along the manifold.
--
--   **Formalization Note** $R$ is a function `E → E → E`. Clauses 2–3 and smoothness of each $R_x$ on $T_x\mathcal M$ are the published predicate `ZORiem.RGD.IsRetraction`; clause 1 is added as `ContDiffOn ℝ ∞` of $(x,\xi)\mapsto R_x(\xi)$ on $T\mathcal M\subseteq E\times E$, because Definition 2.1 asks smoothness on the whole tangent bundle. Values of $R$ off $T\mathcal M$ play no role.
-- source:
--   Zhang, Chen & Ma, A Riemannian Smoothing Steepest Descent Method for Non-Lipschitz Optimization on Submanifolds, arXiv:2104.04199v1, Definition 2.1, p.3

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ZORiem_RGD_IsRetraction
set_option autoImplicit false

namespace RiemSmoothSD

open ProjLikeRetr.Retractor

/-- **Retraction** (Zhang, Chen & Ma, arXiv:2104.04199v1, Definition 2.1, p.3, after [2]):
a smooth map `R : TM → M` with `R_x(0_x) = x` and `dR_x(0_x) = id_{T_xM}`, where `R_x` is the
restriction of `R` to `T_xM`.

**Formalization Note** `M ⊆ E` is a subset of a real inner product space and `R : E → E → E`,
`R x ξ = R_x(ξ)`. The published fibrewise predicate `ZORiem.RGD.IsRetraction M R` gives, for every
`x ∈ M`: `R_x` maps `T_xM` into `M`, `R_x(0) = x`, `R_x` is `C^∞` on `T_xM`, and its derivative at
`0` is the inclusion `T_xM → E`. Definition 2.1 also asks `R` to be smooth as a map on the tangent
bundle `TM = {(x, ξ) | x ∈ M, ξ ∈ T_xM}`; that is the second clause, `C^∞` (not analytic) on
`TM ⊆ E × E`. Values of `R x ξ` off `TM` play no role. -/
def IsSmoothRetraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (R : E → E → E) : Prop :=
  ZORiem.RGD.IsRetraction M R ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : E × E => R p.1 p.2) (tangentBundle M)

end RiemSmoothSD


