-- Prove2me | Definitions.Def_SZ_SqrtThree
-- name    : SZ_SqrtThree
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:43:05.336728+00:00
-- url     : https://prove2.me/theorems/aee9efe3-fd2c-4f37-8ee2-a433aea9a78f
-- title:
--   Sqrt Three
-- statement:
--   Definitions and structural lemmas for Sqrt Three, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SqrtThree.lean

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_CoverGame
set_option autoImplicit false
namespace SZ
noncomputable def digitY (i : ℕ) : ℤ := 2 - digitB i
noncomputable def witX : ℝ := digitReal 3 digitA
noncomputable def witY : ℝ := digitReal 3 digitY
noncomputable def witXi : ℝ := (4 + witX) / 3
end SZ


