-- Prove2me | Definitions.Def_KMeansTaper_c085
-- name    : KMeansTaper_c085
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:09.650024+00:00
-- url     : https://prove2.me/theorems/bd714e61-304b-4bd7-9059-c62ae4845668
-- title:
--   The taper constant $c_{0.85}$
-- statement:
--   $c_{0.85}$ is the IEEE double-precision number nearest to $0.85$:
--
--   $$c_{0.85}=\frac{7656119366529843}{2^{53}}=0.84999999999999997779\ldots<0.85 .$$
--
--   It is the taper constant of the main certificate (Theorem 3.2).
--
--   **Formalization Note** Stored as the exact rational above; it differs from $85/100$ by $0.2\cdot 2^{-53}$.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 3.2, p.4 (PDF p.7)

import Mathlib

namespace KMeansTaper

/-- **The taper constant `c_{0.85}`**, Theorem 3.2, p.4 (PDF p.7): the IEEE double nearest to
`0.85`, printed as `0.849999999999999977…`.

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** The double nearest to `0.85` is exactly `7656119366529843 / 2^53`
(`2^53 = 9007199254740992`), i.e. `0.84999999999999997779…`; it is not `85/100`. -/
def c085 : ℚ := 7656119366529843 / 9007199254740992

end KMeansTaper


