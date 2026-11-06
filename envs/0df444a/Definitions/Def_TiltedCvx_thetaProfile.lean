-- Prove2me | Definitions.Def_TiltedCvx_thetaProfile
-- name    : TiltedCvx_thetaProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:15.119928+00:00
-- url     : https://prove2.me/theorems/e5eb9b42-fa38-46af-a664-dacba98f048b
-- title:
--   The profile formula $\min\{s^\gamma,1-(1-s)^{1/\gamma}\}$
-- statement:
--   For $\gamma\in(0,1]$ and $s\in[0,1]$,
--
--   $$
--   \vartheta_\gamma(s)=\min\big\{s^{\gamma},\ 1-(1-s)^{1/\gamma}\big\}.
--   $$
--
--   This is the real-valued formula of the extremal profile on $[0,1]$; it is used in the interpolation bound (12).
--
--   **Formalization Note** Real powers (`Real.rpow`), used only for $\gamma\in(0,1]$ and $s\in[0,1]$.
-- source:
--   Pedramfar–Khanna–Quinn–Aggarwal, Tilted Convexity and an Exact Offline–Online Separation, arXiv:2611.03472, Theorem 13, (11), p.22

import Mathlib

namespace TiltedCvx

/-- **The profile formula `min{s^γ, 1 − (1 − s)^{1/γ}}`.** Pedramfar–Khanna–Quinn–Aggarwal,
arXiv:2611.03472, Theorem 13, (11), p.22: the value of `ϑγ(s)` for `s ∈ [0, 1]`.

**Formalization Note** Real powers (`Real.rpow`); used for `γ ∈ (0, 1]` and `s ∈ [0, 1]`, where
both bases are nonnegative. The extended-real function `ϑγ` is `theta`. -/
noncomputable def thetaProfile (γ s : ℝ) : ℝ :=
  min (s ^ γ) (1 - (1 - s) ^ (1 / γ))

end TiltedCvx


