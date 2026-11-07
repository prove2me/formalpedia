-- Prove2me | Definitions.Def_PolySphereLP_ellCoef
-- name    : PolySphereLP_ellCoef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:32.809217+00:00
-- url     : https://prove2.me/theorems/5c5aceba-cbb7-4f85-84eb-b2e0212e4c2d
-- title:
--   Leading coefficient $\ell_{m,j}$ of the normalized Gegenbauer polynomial
-- statement:
--   For ambient dimension $m\ge3$ let $Q^{(m)}_j(t)=C^{(m-2)/2}_j(t)/C^{(m-2)/2}_j(1)$ be the Gegenbauer polynomial normalized by $Q^{(m)}_j(1)=1$. Its leading coefficient is
--   $$\ell_{m,j}=[t^j]\,Q^{(m)}_j(t)=\frac{2^j((m-2)/2)_j}{(m-2)_j},$$
--   with $(b)_j=b(b+1)\cdots(b+j-1)$. It enters the covariance constant $v_{n,d,r}$ of (44).
--
--   **Formalization Note** $Q^{(m)}_j$ is the published `SphereSOS.Rate.geg m j`, defined by $Q_0=1$, $Q_1=t$ and the three-term recurrence $(k+m-1)Q_{k+2}=(2k+m)\,t\,Q_{k+1}-(k+1)Q_k$, which is the recurrence of $C^\lambda_k/C^\lambda_k(1)$ for $\lambda=(m-2)/2$. The definition takes the coefficient of $t^j$ (the paper's definition); the closed form is a consequence.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (17), p.11

import Mathlib
import Definitions.Def_SphereSOS_Rate_Gegenbauer

namespace PolySphereLP

/-- **The leading coefficient `ℓ_{m,j}` of the normalized Gegenbauer polynomial.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (17), p.11:
`Q_j^{(m)}(t) = C_j^{(m−2)/2}(t)/C_j^{(m−2)/2}(1)` and `ℓ_{m,j} =def [t^j] Q_j^{(m)}(t)`
(`= 2^j((m−2)/2)_j/(m−2)_j`).

`ellCoef m j` is the coefficient of `t^j` in `SphereSOS.Rate.geg m j`, the published normalized
Gegenbauer polynomial `Q_j^{(m)}` of the sphere `S^{m−1}`.

**Formalization Note.** `SphereSOS.Rate.geg m` is defined by `Q_0 = 1`, `Q_1 = t` and the three-term
recurrence `(k+m−1)Q_{k+2} = (2k+m) t Q_{k+1} − (k+1) Q_k`, which is the recurrence of
`C_k^λ/C_k^λ(1)` with `λ = (m−2)/2`; for `m ≥ 3` it is the paper's `Q_j^{(m)}`. The definition is the
paper's `def` (the leading coefficient); the closed form in (17) is a consequence. -/
noncomputable def ellCoef (m j : ℕ) : ℝ :=
  (SphereSOS.Rate.geg m j).coeff j

end PolySphereLP


