-- Prove2me | Definitions.Def_EthierKurtz_WFState
-- name    : EthierKurtz_WFState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:15:40.553201+00:00
-- url     : https://prove2.me/theorems/42bb6ed6-9fd4-4a7e-80ae-dbe61a749054
-- title:
--   Wright–Fisher simplex state space
-- statement:
--   The compact d-coordinate simplex of nonnegative real vectors whose coordinate sum is at most one; the omitted final coordinate is one minus that sum.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 2, equation (2.15), printed p. 375 (PDF p. 384).

import Mathlib

/-! Definition-only reuse of the exact `WFState` abbreviation in the historical
standalone Theorems/EthierKurtzGeneticModels.lean. That completed file is
preserved and not rebuilt. Do not import both standalone modules together,
just as with the book's definition-only semigroup reuse module. -/
open scoped BigOperators
namespace EthierKurtz

/-- The first d allele frequencies; Chapter 8 (2.15), Chapter 10 (1.16).
Nonnegativity and sum ≤ 1 already imply that every coordinate is ≤ 1. -/
abbrev WFState (d : ℕ) :=
  {p : Fin d → ℝ // (∀ i, 0 ≤ p i) ∧ ∑ i, p i ≤ 1}

end EthierKurtz


