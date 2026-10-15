-- Prove2me | Definitions.Def_ZORiem_RGD_IsRetraction
-- name    : ZORiem_RGD_IsRetraction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:04:25.183181+00:00
-- url     : https://prove2.me/theorems/e84ec1ad-521b-4ba6-bc65-07411352257d
-- title:
--   Definition 2.4 with Assumption 2.1's ρₓ = ∞, p. 6 — a retraction defined on all of TₓM
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (the ambient space $\mathbb R^n$), let $M\subseteq E$, and for $x\in E$ let $T_xM$ denote the tangent space of $M$ at $x$ (the linear span of the tangent cone of $M$ at $x$). A map $R:E\times E\to E$, written $R_x(\eta)=R(x,\eta)$, is a **retraction on $M$** if for every $x\in M$:
--
--   1. $R_x(\eta)\in M$ for every $\eta\in T_xM$;
--   2. $R_x(0)=x$;
--   3. the restriction $\eta\mapsto R_x(\eta)$, $T_xM\to E$, is smooth ($C^\infty$);
--   4. its differential at $0$ is the inclusion of $T_xM$ into $E$, i.e.
--
--   $$\frac{d}{dt}R_x(t\eta)\Big|_{t=0}=\eta\qquad\text{for all }\eta\in T_xM .$$
--
--   This is Definition 2.4 of the paper, with $R_x$ defined on the whole tangent space: the paper requires its smoothness assumption (2.2) for all $\eta\in T_xM$ ("$\rho_x=\infty$"), so the retraction must be global. Examples are the exponential map of a complete manifold, $R_x(\eta)=(x+\eta)/\|x+\eta\|$ on the sphere, and $R_x(\eta)=x+\eta$ on $M=E$.
--
--   **Formalization Note** "Smooth" is `ContDiff ℝ ∞` (the value `((⊤ : ℕ∞) : WithTop ℕ∞)`, not the analytic `ω`), stated for the map on the subtype `T_xM`; the differential condition is `HasFDerivAt … (T_xM).subtypeL 0`. Values of $R(x,\eta)$ for $x\notin M$ or $\eta\notin T_xM$ are unconstrained and never used. The published local predicate `ProjLikeRetr.Retractor.IsRetraction` is deliberately not used, because it only constrains $R$ near the zero section.
-- source:
--   Li, Balasubramanian and Ma, arXiv:2003.11238v3, Definition 2.4 and Assumption 2.1, p. 6

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle

namespace ZORiem.RGD

open ProjLikeRetr.Retractor

/-- Definition 2.4, p. 6, made global as Assumption 2.1 requires ("ρ_x = ∞", p. 6): for every
`x ∈ M`, the map `R_x = R x` restricted to the tangent space `T_xM` sends `T_xM` into `M`, satisfies
`R_x(0) = x`, is smooth on `T_xM`, and has differential at `0` equal to the inclusion `T_xM → E`
(the identity of `T_xM`). "Smooth" is `C^∞`, i.e. `((⊤ : ℕ∞) : WithTop ℕ∞)`
(not the analytic `ω = ⊤`). Values of `R x η` for `η ∉ T_xM` play no role. -/
def IsRetraction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : Set E) (R : E → E → E) : Prop :=
  ∀ x ∈ M, (∀ η ∈ tangentSpace M x, R x η ∈ M) ∧ R x 0 = x ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun η : tangentSpace M x => R x η) ∧
    HasFDerivAt (fun η : tangentSpace M x => R x η) (tangentSpace M x).subtypeL 0

end ZORiem.RGD


