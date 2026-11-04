-- Prove2me | Definitions.Def_ChapterG3Promoted
-- name    : ChapterG3Promoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-03T12:28:33.723678+00:00
-- url     : https://prove2.me/theorems/4cb4f272-f15a-434c-99c5-aeb5bbb0f065
-- title:
--   Mehler = uniform measure: the sphere layer
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterG3.lean`): the `PhysHSGaussian` sphere layer (`sphereProj`, `sphereUniform`) carved out of ChapterG3 under the §2.13 new-name route: the served copy carries `gaussianE` but not the push-forward of the standard Gaussian under the radial projection, so the three `mehler_uniform_*` statements, which cite `PhysHSGaussian.sphereUniform`, die server-side with `Unknown identifier`. Consumers add a single `import Definitions.Def_ChapterG3Promoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterG3.lean

-- Generated from ChapterG3.lean — the `PhysHSGaussian` sphere layer that the
-- platform's served ChapterG3 copy predates (§2.13 new-name route:
-- submit-definition rejects an existing name, so the decls live here instead).
-- The three `mehler_uniform_*` statements cite `PhysHSGaussian.sphereUniform`.
import Definitions.Def_ChapterG3
import Mathlib

open MeasureTheory
open scoped ENNReal

namespace BookProof.ChapterG3

namespace PhysHSGaussian

/-- Radial projection onto the sphere of radius `√k` (junk value at 0). -/
noncomputable def sphereProj (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  if x = 0 then x else (Real.sqrt k / ‖x‖) • x

/-- The uniform measure on the `√k`-sphere, as the push-forward of the standard
Gaussian under the radial projection. -/
noncomputable def sphereUniform (k : ℕ) : MeasureTheory.Measure (EuclideanSpace ℝ (Fin k)) :=
  (gaussianE k).map (sphereProj k)

end PhysHSGaussian

end BookProof.ChapterG3


