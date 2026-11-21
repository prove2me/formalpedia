-- Prove2me | Definitions.Def_logPeriod
-- name    : logPeriod
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:59:42.453553+00:00
-- url     : https://prove2.me/theorems/d36c8b47-1250-42f2-8cc0-9eb500175a4a
-- title:
--   M10 — logPeriod (log-period of a lattice)
-- statement:
--   Definition of the log-period of a lattice: logPeriod Λ = Real.log (latticeArea Λ / π) + (1/6) * Real.log ‖latticeDiscr Λ‖. This is a definition item (a function returning ℝ), without a milestone — a milestone needs a theorem item, so this definition item has none. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:27–28 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies: latticeArea — ours (definition item M10g_latticeArea in this mission); latticeDiscr — ours (definition item M10f_latticeDiscr in this mission). Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. Definition stack must be ported as platform definitions first; the statement alone is not submittable as a proved item.
-- source:
--   Alpöge archive, GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:27

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Definitions.Def_latticeArea
import Definitions.Def_latticeDiscr

open scoped Real

namespace AlpoegeClaudeRH

noncomputable def logPeriod (Λ : Submodule ℤ ℂ) : ℝ :=
  Real.log (latticeArea Λ / π) + (1 / 6) * Real.log ‖latticeDiscr Λ‖

end AlpoegeClaudeRH


