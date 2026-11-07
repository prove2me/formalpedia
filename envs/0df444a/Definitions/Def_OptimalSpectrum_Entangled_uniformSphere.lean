-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_uniformSphere
-- name    : OptimalSpectrum_Entangled_uniformSphere
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:47.710486+00:00
-- url     : https://prove2.me/theorems/96912d2c-6d55-4769-b351-e01fc53b2540
-- title:
--   Uniform probability measure on the unit sphere of $\mathbb C^d$
-- statement:
--   The uniform (unitarily invariant) probability measure $U$ on the unit sphere $\{u\in\mathbb C^d:\|u\|=1\}$, obtained by normalizing the surface measure of the sphere of $\mathbb C^d\cong\mathbb R^{2d}$. It is the reference measure of the uniform POVM on $\mathbb C^d$ used by the unentangled scheme.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.1, p. 20 (PDF p. 22)

import Mathlib

open MeasureTheory

namespace OptimalSpectrum.Entangled

/-- **Uniform probability measure on the unit sphere of `ℂ^d`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.1, printed p. 20 (PDF p. 22): "we apply the uniform POVM on C^d. Let |u⟩ ∈ C^d be the
resulting unit vector".

The rotation-invariant surface measure on the unit sphere of `ℂ^d ≅ ℝ^(2d)` (Mathlib's
`Measure.toSphere` of Lebesgue measure), normalized to total mass one and viewed as a measure on
`ℂ^d`.

**Formalization Note.** For `d = 0` the sphere is empty and the measure is zero; every statement
using it has `d ≥ 1` implicitly through a density matrix. -/
noncomputable def uniformSphere (d : ℕ) : Measure (EuclideanSpace ℂ (Fin d)) :=
  (((volume : Measure (EuclideanSpace ℂ (Fin d))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℂ (Fin d))).toSphere).map Subtype.val

end OptimalSpectrum.Entangled


