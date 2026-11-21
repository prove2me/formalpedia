-- Prove2me | Definitions.Def_latticeG2
-- name    : latticeG2
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:58:45.746015+00:00
-- url     : https://prove2.me/theorems/23f6a442-1e9f-4589-994e-47b688a3cf06
-- title:
--   M10 — latticeG₂ (lattice G₂ function)
-- statement:
--   Definition of the lattice G₂ function: latticeG₂ Λ = 60 * eisensteinSum Λ 4, for a ℤ-submodule Λ of ℂ. This is a definition item (a function returning ℂ), without a milestone — a milestone needs a theorem item, so this definition item has none. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:17 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies: eisensteinSum — new definition item in this mission. Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. The definition is marked noncomputable on the platform because the archive achieves this via its enclosing noncomputable section, which does not survive per-item extraction; the mathematics is unchanged.

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_eisensteinSum

namespace AlpoegeClaudeRH

noncomputable def latticeG₂ (Λ : Submodule ℤ ℂ) : ℂ := 60 * eisensteinSum Λ 4

end AlpoegeClaudeRH


