-- Prove2me | Definitions.Def_TiltedCvx_Supplement_tiltedAffine
-- name    : TiltedCvx_Supplement_tiltedAffine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:24:15.932086+00:00
-- url     : https://prove2.me/theorems/9f7d2d28-4a16-4440-89d0-d231e8f8c9a5
-- title:
--   Tilted affine family $H_\gamma$ (Definition 8)
-- statement:
--   For $\gamma\in(0,1]$,
--
--   $$
--   H_\gamma:=\big\{\,y\mapsto c+\psi_\gamma(\langle y-w,z\rangle)\ :\ c\in\mathbb R,\ z,w\in\mathbb R^d\,\big\},
--   $$
--
--   where $\psi_\gamma(t)=\min\{\gamma t,\gamma^{-1}t\}$. Each member is piecewise affine, with gradient $\gamma z$ on one side of the hyperplane $\{\langle y-w,z\rangle=0\}$ and $z/\gamma$ on the other; $H_1$ is the family of affine functions. Suprema of members of $H_\gamma$ are exactly the $\gamma^2$–tilted secant convex functions (Theorem 24).
--
--   **Formalization Note** Members are functions into `EReal`; for $\gamma>0$ they are real-valued.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Definition 8, p.15

import Mathlib
import Definitions.Def_TiltedCvx_psi

open scoped InnerProductSpace

namespace TiltedCvx.Supplement

/-- **The tilted affine family `H_γ` (Definition 8).** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Definition 8, p.15: for `γ ∈ (0, 1]`,
`H_γ := {y ↦ c + ψγ(⟨y − w, z⟩) : ℝ^d → ℝ | c ∈ ℝ, z, w ∈ ℝ^d}`.

**Formalization Note** The members are `E → EReal`; for `γ > 0` the published `TiltedCvx.psi`
sends reals to reals, so every member is real-valued, as in the paper. Only `γ ∈ (0, 1]` is
used. -/
def tiltedAffine {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (γ : ℝ) :
    Set (E → EReal) :=
  {h | ∃ (c : ℝ) (z w : E),
    h = fun y => (c : EReal) + TiltedCvx.psi γ ((⟪y - w, z⟫_ℝ : ℝ) : EReal)}

end TiltedCvx.Supplement


