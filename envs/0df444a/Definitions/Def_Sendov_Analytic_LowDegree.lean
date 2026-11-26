-- Prove2me | Definitions.Def_Sendov_Analytic_LowDegree
-- name    : Sendov_Analytic_LowDegree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T18:54:56.234152+00:00
-- url     : https://prove2.me/theorems/2ae03033-3eaa-44e9-a3f5-085c7035d63e
-- title:
--   Low Degree
-- statement:
--   Definitions and structural lemmas for Low Degree, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/LowDegree.lean

import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
namespace Sendov
noncomputable def lowX (a t : ℝ) : ℝ := a + (1 - a ^ 2) * t
noncomputable def lowJ (m : ℕ) (a : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, lowX a t ^ m
end Sendov


