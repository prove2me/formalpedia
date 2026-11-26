-- Prove2me | Definitions.Def_Spectral_Cayley_Unitary
-- name    : Spectral_Cayley_Unitary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:52:41.843177+00:00
-- url     : https://prove2.me/theorems/06735c0a-0b9e-56a8-a6a3-cabd83472f06
-- title:
--   Unitary
-- statement:
--   Definitions and structural lemmas for Unitary, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Unitary.lean

import Definitions.Def_Spectral_Cayley_Basic
set_option autoImplicit false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


