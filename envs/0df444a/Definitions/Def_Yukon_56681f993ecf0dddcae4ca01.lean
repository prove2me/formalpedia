-- Prove2me | Definitions.Def_Yukon_56681f993ecf0dddcae4ca01
-- name    : Yukon_56681f993ecf0dddcae4ca01
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:37:23.409239+00:00
-- url     : https://prove2.me/theorems/7bcbcf08-cad6-4905-a3ee-ded64101ed39
-- title:
--   YukonModule.ArkLib.ToMathlib.Polynomial.DegreeLT.part0
-- statement:
--   Source module ArkLib.ToMathlib.Polynomial.DegreeLT.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ToMathlib/Polynomial/DegreeLT.lean
--
--   provider-v8:373cf46c38318d0382a2287e40e502303541aa78e101ff3aab5bda9ab5afac16
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODozNzNjZjQ2YzM4MzE4ZDAzODJhMjI4N2U0MGU1MDIzMDM1NDFhYTc4ZTEwMWZmM2FhYjViZGE5YWI1YWZhYzE2IiwiaGFzaCI6IjMyOWI5MGQ0YTA2YjRhYWEyY2FhMDQ3Njc2NzQxOTNlNTVmYzczMTdkOTdmZmFjN2M1ZjNiY2ZkMzg0ZjI1YjciLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzU2NjgxZjk5M2VjZjBkZGRjYWU0Y2EwMSIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

import Mathlib.RingTheory.Polynomial.Basic


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# `Polynomial.degreeLT` boundary facts

Lemmas about `Polynomial.degreeLT R n` (the submodule of polynomials of degree `< n`) at
the boundary `n = 0`, where it collapses to the zero submodule.

These are reusable for any construction that maps `degreeLT` through a linear map — e.g.
Reed-Solomon codes (`ReedSolomon.code α n = (degreeLT F n).map (evalOnPoints α)`), folded
RS codes, and similar code families. Candidate for upstream PR to Mathlib.
-/

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- `Polynomial.degreeLT R 0 = ⊥`: the only polynomial with degree strictly less than `0`
(in `WithBot ℕ`) is the zero polynomial.

Not `@[simp]` to avoid disrupting existing simp-based proofs that unfold `degreeLT` directly. -/
theorem degreeLT_zero : degreeLT R 0 = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Polynomial.mem_degreeLT, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
      Polynomial.degree_eq_bot] at hp
  exact hp ▸ Submodule.zero_mem _

end Polynomial


