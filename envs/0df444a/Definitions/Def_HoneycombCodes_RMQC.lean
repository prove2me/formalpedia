-- Prove2me | Definitions.Def_HoneycombCodes_RMQC
-- name    : HoneycombCodes_RMQC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:53.292909+00:00
-- url     : https://prove2.me/theorems/9547009c-f1b6-43d2-bc53-396e4a1b17cf
-- title:
--   Normalized MQC exponent $R_{MQC}(\delta)$
-- statement:
--   With $g$ as above, the normalized mixed-qubit-channel exponent of Alrabiah and Guruswami, as recalled in the paper, is
--
--   $$
--   R_{MQC}(\delta)=\min_{1-2\delta\le u\le 1}\Bigl\{g(u^2)-g\bigl(u(u-(1-2\delta))\bigr)\Bigr\}.
--   $$
--
--   **Formalization Note** Defined by the paper's display (119) in normalized variables, not re-derived from the channel. The minimum is the real `sInf` of the image of the compact interval $[1-2\delta,1]$.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.1, eq. (119), p.59 (PDF 61)

import Mathlib
import Definitions.Def_HoneycombCodes_H2

set_option autoImplicit false

namespace HoneycombCodes

/-- The **normalized MQC exponent** of [AG26] as recalled in
Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2
(sha256 f4b07e31…cd51), App. D.1, eq. (119), p.59 (PDF 61):
`R_MQC(δ) = min_{1 − 2δ ≤ u ≤ 1} { g(u²) − g(u(u − (1 − 2δ))) }`.

**Formalization Note.** The exponent is defined by the paper's own display (119), in the
normalized variables; it is not re-derived from Alrabiah–Guruswami's channel. The minimum is the
real `sInf` of the image of the closed interval `[1 − 2δ, 1]` (nonempty and compact for
`0 < δ < 1/2`, continuous integrand). -/
noncomputable def RMQC (δ : ℝ) : ℝ :=
  sInf ((fun u : ℝ => g (u ^ 2) - g (u * (u - (1 - 2 * δ)))) '' Set.Icc (1 - 2 * δ) 1)

end HoneycombCodes


