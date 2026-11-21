-- Prove2me | Definitions.Def_latticeG3
-- name    : latticeG3
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:58:56.518342+00:00
-- url     : https://prove2.me/theorems/6dfbef07-e7ea-4824-8eb6-172e692d6aa5
-- title:
--   M10 — latticeG₃ (lattice G₃ function)
-- statement:
--   Definition of the lattice G₃ function: latticeG₃ Λ = 140 * eisensteinSum Λ 6, for a ℤ-submodule Λ of ℂ. This is a definition item (a function returning ℂ), without a milestone — a milestone needs a theorem item, so this definition item has none. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:19 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies: eisensteinSum — new definition item in this mission. Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. The definition is marked noncomputable on the platform because the archive achieves this via its enclosing noncomputable section, which does not survive per-item extraction; the mathematics is unchanged.

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_eisensteinSum

namespace AlpoegeClaudeRH

noncomputable def latticeG₃ (Λ : Submodule ℤ ℂ) : ℂ := 140 * eisensteinSum Λ 6

end AlpoegeClaudeRH


