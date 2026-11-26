-- Prove2me | Definitions.Def_Sendov_Conjecture
-- name    : Sendov_Conjecture
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T20:05:03.236806+00:00
-- url     : https://prove2.me/theorems/3bbcd052-1285-4ff4-8ec8-9e64f9ba9b14
-- title:
--   Conjecture
-- statement:
--   Definitions and structural lemmas for Conjecture, from Terence Tao (teorth/sendov; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sendov's conjecture and the Phelps-Rodriguez conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
set_option autoImplicit false
namespace Sendov
open Polynomial
noncomputable def rotate (ω : ℂ) (p : ℂ[X]) : ℂ[X] := p.comp (C ω * X)
end Sendov


