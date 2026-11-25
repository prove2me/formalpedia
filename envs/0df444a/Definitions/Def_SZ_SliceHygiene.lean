-- Prove2me | Definitions.Def_SZ_SliceHygiene
-- name    : SZ_SliceHygiene
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T00:43:19.789809+00:00
-- url     : https://prove2.me/theorems/e18afb76-bae1-4721-8062-4e161993d290
-- title:
--   Slice Hygiene
-- statement:
--   Definitions and structural lemmas for Slice Hygiene, from Ralf Stephan (rwst/Square-Roots; see pinned CC0-1.0 LICENSE and source headers)'s pinned Even integral parts of powers of square roots and Dubickas Problem 3 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/SliceHygiene.lean

import Definitions.Def_SZ_Slice
import Mathlib.Tactic.Push
set_option autoImplicit false
namespace SZ
namespace Slice
variable {S : Slice}
noncomputable def stt (S : Slice) (j k₀ : ℤ) : ℕ → ℤ × ℤ
  | 0 => (-S.p * j * (S.m : ℤ), (S.p * k₀ + 1) * (S.m : ℤ))
  | k + 1 => ((S.m : ℤ) * ((stt S j k₀ k).1 - S.dA (S.w0 j k₀) k),
              (S.m : ℤ) * ((stt S j k₀ k).2 - S.dB (S.w0 j k₀) k))
end Slice
end SZ


