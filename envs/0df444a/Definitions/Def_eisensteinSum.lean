-- Prove2me | Definitions.Def_eisensteinSum
-- name    : eisensteinSum
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-11-21T00:58:33.025906+00:00
-- url     : https://prove2.me/theorems/71e3565c-c26d-48df-9da9-97357c51a994
-- title:
--   M10 — eisensteinSum (Eisenstein sum)
-- statement:
--   Definition of the Eisenstein sum: eisensteinSum Λ n = ∑' l : Λ, ((l : ℂ) ^ n)⁻¹, for a ℤ-submodule Λ of ℂ and n a natural number. This is a definition item (a function returning ℂ), without a milestone — a milestone needs a theorem item, so this definition item has none. Archive source: GroundTheory/HeightsAndTheta/Heights/ChowlaSelberg/Statements.lean:15 (namespace GroundTheory.Heights₂.Heights.ChowlaSelberg). Dependencies: none beyond Mathlib (tsum). Statement read from the Alpöge archive (alpo.ge, SHA-256 verified). Claim NOT verified — no independent lake build Main + #print axioms has been published. The definition is marked noncomputable on the platform because the archive achieves this via its enclosing noncomputable section, which does not survive per-item extraction; the mathematics is unchanged.

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs

namespace AlpoegeClaudeRH

noncomputable def eisensteinSum (Λ : Submodule ℤ ℂ) (n : ℕ) : ℂ := ∑' l : Λ, ((l : ℂ) ^ n)⁻¹

end AlpoegeClaudeRH


