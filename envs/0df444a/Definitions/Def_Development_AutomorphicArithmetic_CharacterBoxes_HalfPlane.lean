-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
-- name    : Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:35.203867+00:00
-- url     : https://prove2.me/theorems/ba26d2df-d72b-4916-8051-84f0350346f7
-- title:
--   Half Plane
-- statement:
--   Definitions and structural lemmas for Half Plane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CharacterBoxes/HalfPlane.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
def Claim.HalfPlane : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0
def Claim.Strip : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
def Claim.Zeta : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2


