-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_SeriesState
-- name    : ReciprocityTheory_DualLattices_SeriesState
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:54.762353+00:00
-- url     : https://prove2.me/theorems/547924d3-5d90-4335-998a-d6d6162ca73a
-- title:
--   Series State
-- statement:
--   Definitions and structural lemmas for Series State, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/SeriesState.lean

import Definitions.Def_ReciprocityTheory_DualLattices_SqZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
universe u
variable {R₀ : Type u} [CommRing R₀]
def PairingPropertiesStatement (B : BX R₀) : Prop :=
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R), N • x = 0 → N • y = 0 → ∃ z, B.IsPairing N x y z) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y z' → z = z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x x' y : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x' y z' → B.IsPairing N (x + x') y w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y y' : B.G R) (z z' w : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N x y' z' → B.IsPairing N x (y + y') w → w = z * z') ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z z' : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N y x z' → z * z' = 1) ∧
  (∀ (R : LAlg R₀) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), B.IsPairing N x y z → z ^ N = 1) ∧
  (∀ (R S : LAlg R₀) (f : LHom R S) (N : ℕ) (x y : B.G R) (z : (R : Type u)ˣ),
    B.IsPairing N x y z → B.IsPairing N (B.map f x) (B.map f y) (Units.map (f.1 : R →* S) z)) ∧
  (∀ (R : LAlg R₀) (N p : ℕ) (x y : B.G R) (z : (R : Type u)ˣ), N • x = 0 → (N * p) • y = 0 →
    B.IsPairing (N * p) x y z → B.IsPairing N x (p • y) z)
end ReciprocityTheory.PGsh


