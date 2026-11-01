-- Prove2me | Definitions.Def_PConeEB_gammaZ
-- name    : PConeEB_gammaZ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:00.884042+00:00
-- url     : https://prove2.me/theorems/077540b3-1786-451e-9d13-87409b196e73
-- title:
--   The quantity $\gamma_{z,\eta}$ of (2.13)
-- statement:
--   Let $K$ be a closed convex cone, $z\in K^*$, $\mathcal F=\{z\}^\perp\cap K$, $\eta\ge0$ and $\mathfrak g:\mathbb R_+\to\mathbb R_+$. Define
--   $$
--   \gamma_{z,\eta}:=\inf_v\left\{\frac{\mathfrak g(\|w-v\|)}{\|w-u\|}\ \middle|\ v\in\partial K\cap B(\eta)\setminus\mathcal F,\ w=P_{\{z\}^\perp}v,\ u=P_{\mathcal F}w,\ w\ne u\right\},
--   $$
--   where $B(\eta)=\{x:\|x\|\le\eta\}$.
--
--   Positivity of this infimum is equivalent to a one-sided error bound on $\{z\}^\perp\cap B(\eta)$ (Theorem 2.2).
--
--   **Formalization Note** The value lies in $[0,\infty]$ (`ENNReal`), so that the empty infimum is $+\infty$, as in the paper's "$\gamma_{z,0}=\infty$". The boundary $\partial K$ is the topological boundary in $\mathcal E$ (`frontier K`), which agrees with the relative boundary when $K$ is full-dimensional.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, (2.13), p.8

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_PConeEB_hyperplane

open MoreauProx.Decomposition (IsProj)

namespace PConeEB

/-- The quantity `γ_{z,η}` of (2.13): the infimum of `g(‖w - v‖) / ‖w - u‖` over
`v ∈ ∂K ∩ B(η) \ F`, `w = P_{{z}^⊥} v`, `u = P_F w`, `w ≠ u`, where `F = K ∩ {z}^⊥`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, (2.13), p.8.

**Formalization Note.** The value lies in `ENNReal`, so the infimum of the empty set is `⊤`, the
paper's `+∞` (its "`γ_{z,0} = ∞`"). `∂K` is the topological boundary `frontier K` in `E`, not a
relative boundary. The quotient is positive or zero when `g` is nonnegative, and `w ≠ u` makes the
denominator positive, so `ENNReal.ofReal` loses nothing. `IsProj C x y` is the published predicate
"`y` is a nearest point of `C` to `x`", i.e. `y = P_C(x)` on a nonempty closed convex set. -/
noncomputable def gammaZ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (z : E) (g : ℝ → ℝ) (η : ℝ) : ENNReal :=
  ⨅ (v : E) (w : E) (u : E)
    (_ : v ∈ frontier K ∧ ‖v‖ ≤ η ∧ v ∉ K ∩ hyperplane z ∧
      IsProj (hyperplane z) v w ∧ IsProj (K ∩ hyperplane z) w u ∧ w ≠ u),
    ENNReal.ofReal (g ‖w - v‖ / ‖w - u‖)

end PConeEB


