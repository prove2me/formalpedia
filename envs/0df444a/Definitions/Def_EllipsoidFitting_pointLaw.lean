-- Prove2me | Definitions.Def_EllipsoidFitting_pointLaw
-- name    : EllipsoidFitting_pointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:16.702167+00:00
-- url     : https://prove2.me/theorems/9c93967f-938f-4f4c-8478-010658df888f
-- title:
--   Law of $m$ i.i.d. $N(0,I_d/d)$ points in $\mathbb R^d$
-- statement:
--   $\mathbb P_{d,m}$ is the joint law of $m$ independent Gaussian vectors $v_1,\dots,v_m\sim N(0,I_d/d)$ in $\mathbb R^d$: all $md$ coordinates $v_i[a]$ are independent centered real Gaussians with variance $1/d$.
--
--   The variance $1/d$ normalizes $\|v_i\|_2^2\approx1$, so that $\Lambda\approx I_d$ nearly fits the points.
--
--   **Formalization Note** A nested product measure (`Measure.pi`) of `gaussianReal 0 (1/d)` on `Fin m → Fin d → ℝ`. At $d=0$ the variance is the junk value $0$ on the one-point space $\mathbb R^0$.
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Theorems 1.1–1.2, p.3 (PDF p.5)

import Mathlib

set_option autoImplicit false

namespace EllipsoidFitting

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **The law of the points.** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase Transition for
Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Theorems 1.1–1.2, p.3:
"v1, . . . , vm ∼ N(0, Id/d) be independent d-dimensional Gaussian vectors".

`pointLaw d m` is the joint law of `m` independent vectors `v 0, …, v (m-1)` of `ℝ^d`, each
`N(0, I_d / d)`: all `m·d` coordinates are independent centered real Gaussians of variance `1/d`.

**Formalization Note** The law is the product measure `Measure.pi` over `Fin m × Fin d` (nested)
of `gaussianReal 0 (1/d)`. For `d = 0` the variance `(0 : ℝ≥0)⁻¹ = 0` is a junk value, but then
`Fin 0 → ℝ` is a point and nothing depends on it. -/
noncomputable def pointLaw (d m : ℕ) : Measure (Fin m → Fin d → ℝ) :=
  Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin d => gaussianReal 0 (d : ℝ≥0)⁻¹))

end EllipsoidFitting


