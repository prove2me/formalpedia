-- Prove2me | Definitions.Def_latticeDiscr
-- name    : latticeDiscr
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:59:23.384465+00:00
-- url     : https://prove2.me/theorems/6ce66367-2c17-4a34-b73e-120e272908d1
-- title:
--   M10 — latticeDiscr (lattice discriminant)
-- statement:
--   Definition of the lattice discriminant: latticeDiscr Λ = latticeG₂ Λ ^ 3 − 27 * latticeG₃ Λ ^ 2, for a ℤ-submodule Λ of ℂ. This is a definition item (a function returning ℂ), without a milestone — a milestone needs a theorem item, so this definition item has none. Uses supporting defs latticeG₂ (:17) and latticeG₃ (:19) in the same file, not added as separate items here. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:21 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies — Formalpedia check, Nov 20, 2026: latticeG₂ — not checked; latticeG₃ — not checked. Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. Definition stack must be ported as platform definitions first; the statement alone is not submittable as a proved item.
-- source:
--   Alpöge archive, GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:21

import Mathlib.Analysis.Complex.Basic
import Definitions.Def_latticeG2
import Definitions.Def_latticeG3

namespace AlpoegeClaudeRH

noncomputable def latticeDiscr (Λ : Submodule ℤ ℂ) : ℂ := latticeG₂ Λ ^ 3 - 27 * latticeG₃ Λ ^ 2

end AlpoegeClaudeRH


