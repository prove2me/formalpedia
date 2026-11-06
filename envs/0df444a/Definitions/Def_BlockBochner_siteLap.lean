-- Prove2me | Definitions.Def_BlockBochner_siteLap
-- name    : BlockBochner_siteLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:24.659941+00:00
-- url     : https://prove2.me/theorems/1ededf0c-4e02-4c69-85fb-4afa7f0cc833
-- title:
--   Local Laplacian $L_v=I-E_v$
-- statement:
--   For a site $v$, the local Laplacian is
--   $$L_v=I-E_v,\qquad E_vf=E_\nu[f\mid X_{-v}],$$
--   the orthogonal projection of $L^2(\nu)$ onto the functions with zero conditional mean given the other spins. On a link it is $L^\nu_i=I-P^\nu_i$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.6, p.8; Sec. 2.2, p.16

import Mathlib
import Definitions.Def_BlockBochner_condExpOn

open MeasureTheory

namespace BlockBochner

/-- **Local Laplacian `L_v = I − E_v`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.6, p.8: `E_v f = E_µ[f | X_{−v}]` and
`L_v = I − E_v`; on a link, `L^ν_i = I − P^ν_i` (Sec. 2.2, p.16).

**Formalization Note** `E_v` is `condExpOn ν {v}ᶜ`, the conditional expectation given every spin
except the one at `v`. -/
noncomputable def siteLap {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (ν : Measure (∀ i, X i)) (i : ι) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  1 - condExpOn ν {i}ᶜ

end BlockBochner


