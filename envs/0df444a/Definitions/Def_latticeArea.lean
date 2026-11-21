-- Prove2me | Definitions.Def_latticeArea
-- name    : latticeArea
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:58:02.490014+00:00
-- url     : https://prove2.me/theorems/0c205f9e-3f5b-4903-b080-c8364095bde1
-- title:
--   M10 — latticeArea (lattice area / covolume)
-- statement:
--   Definition of the lattice area (covolume): latticeArea Λ = ZLattice.covolume Λ, for a ℤ-submodule Λ of ℂ. This is a definition item (a function returning ℝ), without a milestone — a milestone needs a theorem item, so this definition item has none. ZLattice.covolume — check Mathlib vs archive-defined before porting. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:25 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies — Formalpedia check, Nov 20, 2026: ZLattice.covolume — not checked. Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. Definition stack must be ported as platform definitions first; the statement alone is not submittable as a proved item.
-- source:
--   Alpöge archive, GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:25

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume

namespace AlpoegeClaudeRH

noncomputable def latticeArea (Λ : Submodule ℤ ℂ) : ℝ := ZLattice.covolume Λ

end AlpoegeClaudeRH


