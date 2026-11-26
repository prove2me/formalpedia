-- Prove2me | Definitions.Def_Section5Verified_Section5TiltedProjectionMGF
-- name    : Section5Verified_Section5TiltedProjectionMGF
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:23.285809+00:00
-- url     : https://prove2.me/theorems/bd752add-33fa-5438-9bc3-87f5a045132a
-- title:
--   Section5TiltedProjectionMGF — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5TiltedProjectionMGF; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
import Definitions.Def_Section5Verified_Section5FiniteProbabilityLaw
import Mathlib
section
set_option autoImplicit false

namespace Section5BooleanFrame

open MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (ι → Bool)] [MeasurableSingletonClass (ι → Bool)]

noncomputable def probabilityLaw (w : ι → ℝ) (hw : ∑ i, w i^2=1) :
    Measure (ι → Bool) := Section5FiniteProbability.law (weight w)
  (weight_nonneg w) ((weight_sum w).trans hw)

instance probabilityLaw_probability (w : ι → ℝ) (hw : ∑ i, w i^2=1) :
    IsProbabilityMeasure (probabilityLaw w hw) :=
  inferInstanceAs (IsProbabilityMeasure (Section5FiniteProbability.law (weight w)
    (weight_nonneg w) ((weight_sum w).trans hw)))













end Section5BooleanFrame

end


