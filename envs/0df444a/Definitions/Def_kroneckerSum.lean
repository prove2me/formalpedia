-- Prove2me | Definitions.Def_kroneckerSum
-- name    : kroneckerSum
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:58:11.353043+00:00
-- url     : https://prove2.me/theorems/7fad65ac-b93e-43b9-870d-874f53c2d195
-- title:
--   M10 — kroneckerSum (Kronecker sum)
-- statement:
--   Definition of the Kronecker sum: kroneckerSum τ s = ∑' p : ℤ × ℤ, if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s), for τ in the upper half-plane ℍ and s real. This is a definition item (a function returning ℝ), without a milestone — a milestone needs a theorem item, so this definition item has none. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:35–36 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies — Formalpedia check, Nov 20, 2026: none beyond Mathlib (tsum, Complex) — not checked on Formalpedia. Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. Definition stack must be ported as platform definitions first; the statement alone is not submittable as a proved item.
-- source:
--   Alpöge archive, GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:35

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped UpperHalfPlane

namespace AlpoegeClaudeRH

noncomputable def kroneckerSum (τ : ℍ) (s : ℝ) : ℝ :=
  ∑' p : ℤ × ℤ, if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)

end AlpoegeClaudeRH


