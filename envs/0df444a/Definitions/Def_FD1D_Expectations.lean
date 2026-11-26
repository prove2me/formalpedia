-- Prove2me | Definitions.Def_FD1D_Expectations
-- name    : FD1D_Expectations
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:40:01.080135+00:00
-- url     : https://prove2.me/theorems/4daec5ad-5658-4b13-850f-cfad3b271353
-- title:
--   Expectations
-- statement:
--   Definitions and structural lemmas for Expectations, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Expectations.lean

import Definitions.Def_FD1D_Markov
set_option autoImplicit true
namespace FD1D
noncomputable section
open scoped BigOperators
namespace FiniteLaw
variable {α : Type*} [Fintype α]
end FiniteLaw
namespace FiniteKernel
variable {α : Type*} [Fintype α]
end FiniteKernel
end
end FD1D


