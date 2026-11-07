-- Prove2me | Definitions.Def_PolySphereLP_vconst
-- name    : PolySphereLP_vconst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:57:50.524239+00:00
-- url     : https://prove2.me/theorems/a3cb2df9-7344-4676-bb8e-d6b9befda6d2
-- title:
--   The covariance constant $v_{n,d,r}$
-- statement:
--   With $h=h_{n,d}$ and $q=dr$,
--   $$v_{n,d,r}=r!\,\frac{h^r}{\mathrm R_{h,r}}\,\frac{\ell^r_{n,d}}{\ell_{n,q}}.$$
--   It is the scale of the covariance $\mathbb E_{\mathbf a}[F_{\mathbf a}(x)F_{\mathbf a}(y)]$ in (44).
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (44), p.17

import Mathlib
import Definitions.Def_PolySphereLP_hdim
import Definitions.Def_PolySphereLP_Rmom
import Definitions.Def_PolySphereLP_ellCoef

namespace PolySphereLP

/-- **The covariance constant `v_{n,d,r}`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (44), p.17:
`v_{n,d,r} =def r! h^r / R_{h,r} · ℓ^r_{n,d} / ℓ_{n,q}`, with `h = h_{n,d}` and `q = dr`. -/
noncomputable def vconst (n d r : ℕ) : ℝ :=
  (r.factorial : ℝ) * (hdim n d : ℝ) ^ r / Rmom (hdim n d) r *
    (ellCoef n d ^ r / ellCoef n (d * r))

end PolySphereLP


