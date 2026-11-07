-- Prove2me | Definitions.Def_CompNonlocal_sphereMeasure
-- name    : CompNonlocal_sphereMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:47.194196+00:00
-- url     : https://prove2.me/theorems/9179e8a3-a9ca-468d-a774-1274fd235a75
-- title:
--   The normalized surface measure on $S^2$
-- statement:
--   The rotation-invariant probability measure $\mu$ on the unit sphere $S^2\subset\mathbb R^3$ ("normalized sphere measure"). A "uniform direction $h\in S^2$" (Lemmas 5 and 15) has law $\mu$.
--
--   **Formalization Note** Mathlib's surface measure induced by Lebesgue measure on $\mathbb R^3$ (total mass $4\pi$), divided by its total mass.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), proof of Lemma 5, p.28

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace CompNonlocal

/-- The normalized surface measure on the unit sphere `S² ⊂ ℝ³`. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), proof of Lemma 5, p.28:
"Let µ be normalized sphere measure"; Lemma 5 (p.27) and Lemma 15 (p.42) let "the shared random
variable h be a uniform direction in S²".

**Formalization Note** Mathlib's `Measure.toSphere` of Lebesgue measure on `EuclideanSpace ℝ (Fin 3)`
(total mass 4π), divided by its total mass, so that the sphere has measure 1. -/
noncomputable def sphereMeasure : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere

end CompNonlocal


