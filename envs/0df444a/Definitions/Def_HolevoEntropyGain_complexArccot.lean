-- Prove2me | Definitions.Def_HolevoEntropyGain_complexArccot
-- name    : HolevoEntropyGain_complexArccot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:06.353839+00:00
-- url     : https://prove2.me/theorems/c48952d1-ce11-469c-b87a-1e61bb594526
-- title:
--   Complex inverse cotangent
-- statement:
--   For a complex number $z \ne \pm i$,
--
--   $$
--   \operatorname{arc\,cot} z = \frac{1}{2i}\log\frac{z+i}{z-i},
--   $$
--
--   with the principal logarithm.
--
--   **Formalization Note** Only used at $z = \pm 2i\alpha_j$ with $\alpha_j>\frac12$, where $(z+i)/(z-i)$ is a positive real and the principal logarithm is the real one.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (19), p.5

import Mathlib

namespace HolevoEntropyGain

/-- The complex inverse cotangent `arc cot z = (1/2i) log((z + i)/(z - i))`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, Lemma 2, eq. (19), p.5, PDF p.5).

**Formalization Note** Only used at `z = ±2iαⱼ` with `αⱼ > ½`, where `(z + i)/(z - i)` is a positive real
and the principal logarithm is the real one. -/
noncomputable def complexArccot (z : ℂ) : ℂ :=
  (1 / (2 * Complex.I)) * Complex.log ((z + Complex.I) / (z - Complex.I))

end HolevoEntropyGain


