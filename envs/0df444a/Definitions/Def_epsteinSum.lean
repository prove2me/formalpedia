-- Prove2me | Definitions.Def_epsteinSum
-- name    : epsteinSum
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:58:25.604851+00:00
-- url     : https://prove2.me/theorems/ad480bed-34d6-40f7-bdd9-2a6657764273
-- title:
--   M10 — epsteinSum (Epstein sum)
-- statement:
--   Definition of the Epstein sum: epsteinSum Λ s = ∑' l : Λ, if (l : ℂ) = 0 then 0 else latticeArea Λ ^ s / ‖(l : ℂ)‖ ^ (2 * s), for a ℤ-submodule Λ of ℂ and s real. This is a definition item (a function returning ℝ), without a milestone — a milestone needs a theorem item, so this definition item has none. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:38–39 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies: latticeArea — ours (definition item M10g_latticeArea in this mission). Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. Definition stack must be ported as platform definitions first; the statement alone is not submittable as a proved item.
-- source:
--   Alpöge archive, GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:38

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_latticeArea

namespace AlpoegeClaudeRH

noncomputable def epsteinSum (Λ : Submodule ℤ ℂ) (s : ℝ) : ℝ :=
  ∑' l : Λ, if (l : ℂ) = 0 then 0 else latticeArea Λ ^ s / ‖(l : ℂ)‖ ^ (2 * s)

end AlpoegeClaudeRH


