-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:08.847827+00:00
-- url     : https://prove2.me/theorems/dbe091c6-dea2-4434-bae9-d52215774bed
-- title:
--   Exists Upper Lower
-- statement:
--   Definitions and structural lemmas for Exists Upper Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsUpperLower.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.CompanionTheory.HeckeMult
variable {R : Type} [CommRing R]
def CongOne {n : ℕ} (I : Ideal R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I
def bordered {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
  Fin.lastCases (motive := fun _ => R)
    (Fin.lastCases (motive := fun _ => R) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => R) (c i') (M i') j) i
section bordered
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)
end bordered
section conj
variable {K : Type} [Field K] [Algebra R K]
end conj
end GlobalTheory.CompanionTheory.HeckeMult


