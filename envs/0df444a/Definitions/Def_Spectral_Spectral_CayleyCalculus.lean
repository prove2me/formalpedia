-- Prove2me | Definitions.Def_Spectral_Spectral_CayleyCalculus
-- name    : Spectral_Spectral_CayleyCalculus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:01:02.615539+00:00
-- url     : https://prove2.me/theorems/43507963-dc8b-53eb-a154-976e3a669a1b
-- title:
--   Cayley Calculus
-- statement:
--   Definitions and structural lemmas for Cayley Calculus, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/CayleyCalculus.lean

import Definitions.Def_Spectral_Cayley_Basic
import Definitions.Def_Spectral_PVM_Unbounded
set_option autoImplicit false
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]


