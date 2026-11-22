-- Prove2me | Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- name    : Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OneNonUnit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:10.773034+00:00
-- url     : https://prove2.me/theorems/3546bc93-ad0c-4acb-959d-2763f98b391a
-- title:
--   One Non Unit
-- statement:
--   Definitions and structural lemmas for One Non Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/OneNonUnit.lean

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GaloisIrreducibility
open Matrix
namespace BorderedIndexCases
variable {R : Type} [CommRing R]
def bord {m : ℕ} (M : Matrix (Fin m) (Fin m) R) : Matrix (Fin (m+1)) (Fin (m+1)) R :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (M i)))
end BorderedIndexCases
open Matrix
namespace BorderedIndexCases
variable {R : Type} [CommRing R]
def Equi {s : ℕ} (A B : Matrix (Fin s) (Fin s) R) : Prop :=
  ∃ P Q : Matrix (Fin s) (Fin s) R, IsUnit P ∧ IsUnit Q ∧ P * A * Q = B
end BorderedIndexCases
open Matrix
namespace BorderedIndexCases
variable {R : Type} [CommRing R] [IsLocalRing R]
end BorderedIndexCases
end Formalism.GaloisIrreducibility


