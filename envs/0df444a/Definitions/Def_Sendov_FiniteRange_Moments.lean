-- Prove2me | Definitions.Def_Sendov_FiniteRange_Moments
-- name    : Sendov_FiniteRange_Moments
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T17:53:36.73452+00:00
-- url     : https://prove2.me/theorems/3dd540b6-118d-4c65-819b-c685da883d85
-- title:
--   Moments
-- statement:
--   Definitions and structural lemmas for Moments, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Moments.lean

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
namespace Sendov
open MeasureTheory Finset
noncomputable def mom (n : ℕ) (α : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ range (k + 1), ∑ l ∈ range (i + 1),
    ((k.choose i : ℝ) * (i.choose l) * (-2 * c n α) ^ l * A n α ^ (i - l))
      / ((2 * i - l + 4 : ℕ) : ℝ)
end Sendov


