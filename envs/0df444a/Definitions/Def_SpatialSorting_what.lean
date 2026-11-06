-- Prove2me | Definitions.Def_SpatialSorting_what
-- name    : SpatialSorting_what
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:48:46.936755+00:00
-- url     : https://prove2.me/theorems/4ba19694-81ea-46be-aea9-ca32ac5b2e6f
-- title:
--   The auxiliary activity $\widehat w_j(\gamma;\mathbf h)$
-- statement:
--   The auxiliary activity of a type-$j$ contour is
--
--   $$\widehat w_j(\gamma;\mathbf h)=e^{\|\gamma\|_{\beta,\mathbf h}+R_j(\gamma;\mathbf h)}\,\chi\bigl(R_j(\gamma;\mathbf h)-\kappa_\beta s_\gamma\bigr),\qquad R_j(\gamma;\mathbf h)=\sum_{I\in\mathcal I(\gamma)}\bigl[\log\widehat Z_{i(I)}(I;\mathbf h)-\log\widehat Z_j(I;\mathbf h)\bigr],$$
--
--   defined by increasing filled volume, with $\kappa_\beta=\beta A_{\min}/8$, $s_\gamma=|\overline\gamma|$ and $\widehat Z$ the auxiliary partition functions of the interiors. The cutoff keeps the activity small where the interior log-ratios are large; at the coexistence field it is inactive, and the auxiliary activity agrees with the physical weight.
--
--   **Formalization Note** $\widehat w_j(\gamma;\mathbf h)$ is the level-$v_\gamma$ term of `act`; by the volume decrease of Lemma C.1 the interior contours are evaluated at levels at least their own filled volumes, where the recursion has stabilized, so this is exactly the induction on filled volume of (58)–(60).
-- source:
--   Calvert, Oh, Randall, Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights); Eq. (59), p. 17 (PDF p. 18)

import Mathlib
import Definitions.Def_SpatialSorting_Contour
import Definitions.Def_SpatialSorting_vol
import Definitions.Def_SpatialSorting_act
open Classical Filter Topology

namespace SpatialSorting

/-- The auxiliary (truncated) activity `ŵ_j(γ; h)`, Eq. (59), as the level-`v_γ` value of the recursion.

Calvert, Oh, Randall, *Spatial Sorting and the Geometry of Lattice Spin Systems at Fixed Magnetization*, STOC 2027 submission manuscript (sha256 4d4d4b7d…7fae), unnumbered (Truncated weights); Eq. (59), p. 17 (PDF p. 18). -/
noncomputable def what {q : ℕ} [NeZero q] (A : Matrix (Fin q) (Fin q) ℝ) (χ : ℝ → ℝ) (β : ℝ)
    (j : Fin q) (γ : Contour q) (h : Fin q → ℝ) : ℝ :=
  act A χ β (vol γ) j γ h

end SpatialSorting


