-- Prove2me | Definitions.Def_Section5Verified_Section5SampleCovarianceBilinear
-- name    : Section5Verified_Section5SampleCovarianceBilinear
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:58.802258+00:00
-- url     : https://prove2.me/theorems/dab65543-c8c1-46f1-93da-6459b4da9bf7
-- title:
--   Section5SampleCovarianceBilinear — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5SampleCovarianceBilinear; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5TiltedFrameTail
import Mathlib
section
set_option autoImplicit false

namespace Section5BooleanFrame

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

noncomputable def bilinear (A : Matrix ι ι ℝ) (u v : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, u i*A i j*v j

noncomputable def populationCovariance (w : ι → ℝ) : Matrix ι ι ℝ := fun i j =>
  tiltedMean w (fun x => sign x i*sign x j)









end Section5BooleanFrame

end


