-- Prove2me | Definitions.Def_LindbladStructLearn_FinDist
-- name    : LindbladStructLearn_FinDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:59.584213+00:00
-- url     : https://prove2.me/theorems/403c494d-2992-43db-afba-25bdc6c4c10a
-- title:
--   Finitely supported law (list of weighted outcomes)
-- statement:
--   A finitely supported law on a type, written as a list of (probability, outcome) pairs. The randomness of Algorithms 2 and 3 is finite, and their output laws are written in this form. No condition is bundled.
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Algorithms 2–3, pp.30–32

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- A finitely supported law, as a list of (probability, outcome) pairs. The randomness of
Algorithms 2 and 3 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), pp.30–32) is finite, and their laws are written in this form.

**Formalization Note** No condition is bundled: weights are whatever the algorithm's sampling
probabilities are. -/
abbrev FinDist (α : Type*) : Type _ := List (ℝ × α)

end LindbladStructLearn


