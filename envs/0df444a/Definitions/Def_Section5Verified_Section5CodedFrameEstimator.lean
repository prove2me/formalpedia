-- Prove2me | Definitions.Def_Section5Verified_Section5CodedFrameEstimator
-- name    : Section5Verified_Section5CodedFrameEstimator
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:36.494372+00:00
-- url     : https://prove2.me/theorems/c7ddcb02-c078-5650-9b28-cabadded4175
-- title:
--   Section5CodedFrameEstimator — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5CodedFrameEstimator; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_Section5Verified_Section5CodedFrameCovariance
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Mathlib
section
set_option autoImplicit false

/-! An unbiased, symmetric matrix sample. Its entries use only the measured
frame seed and an independent computational-basis outcome. They do not use the
unknown target amplitudes. No concentration or circuit bound is asserted. -/

namespace Section5PowerCode

variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

noncomputable def matrixSample {k : ℕ} (χ : AddChar F ℝ) (v : ι → F)
    (t : Fin k → F) (y : ι) : Matrix ι ι ℝ := fun i j =>
  (codeSign χ v t i*codeSign χ v t j-(if i=j then 1 else 0))/2+
    if i=j ∧ y=i then 1 else 0



noncomputable def jointWeight {k : ℕ} (χ : AddChar F ℝ) (v : ι → F)
    (w : ι → ℝ) (outcome : (Fin k → F) × ι) : ℝ :=
  frameWeight χ v w outcome.1*w outcome.2^2









end Section5PowerCode

end


