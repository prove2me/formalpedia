-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_Supplement_chd
-- name    : DetTerminalEmbedding1373_Real_Supplement_chd
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:15:00.960199+00:00
-- url     : https://prove2.me/theorems/a5f5d680-d021-4441-9191-a6c48398e460
-- title:
--   Convex hull distortion $\mathrm{chd}_Y(A)$ (Definition 7.2)
-- statement:
--   Let $E_d=\mathbb R^d$ with the Euclidean norm, let $A:E_d\to E_m$ be a linear map and let $Y\subseteq E_d$. The **convex hull distortion** of $A$ on $Y$ is
--
--   $$\mathrm{chd}_Y(A)=\sup_{z\in\operatorname{conv}(Y)}\bigl|\,\|Az\|-\|z\|\,\bigr|.$$
--
--   It measures, uniformly over the convex hull of $Y$, how far the linear map is from preserving Euclidean norms. In the finite-bit part of the paper it transfers a distortion guarantee proved on rational approximations of the terminal directions to the exact, generally irrational, directions.
--
--   **Formalization Note** The supremum is the real supremum over the points of $\operatorname{conv}(Y)$. For a finite $Y$, the only case the paper uses, the hull is compact and the supremum is a maximum. For $Y=\emptyset$ Lean's real supremum over an empty family is $0$. $E_d$ is the published `DetTerminalEmbedding1373.Real.E`.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), p. 24, Definition 7.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib
import Definitions.Def_DetTerminalEmbedding1373_Real_geometry

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real.Supplement

/-- Definition 7.2, p. 24 (convex hull distortion): for a linear map `A : ℝᵈ → ℝᵐ` and a set `Y`,
`chd_Y(A) = sup_{z ∈ conv(Y)} |‖A z‖ - ‖z‖|` (Euclidean norms). It is the real supremum over the
convex hull; for a finite `Y` the hull is compact and the supremum is attained. For `Y = ∅` the
real supremum over the empty index type is `0` by Lean's convention. -/
noncomputable def chd {d m : ℕ} (A : E d →ₗ[ℝ] E m) (Y : Set (E d)) : ℝ :=
  ⨆ z : convexHull ℝ Y, |‖A z‖ - ‖(z : E d)‖|

end DetTerminalEmbedding1373.Real.Supplement


