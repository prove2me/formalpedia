-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularRowLatticeTriangularBasis
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:32:20.475896+00:00
-- url     : https://prove2.me/theorems/5eb7c1a2-face-42ca-958c-48de34e07910
-- title:
--   Block Triangular Row Lattice Triangular Basis
-- statement:
--   Definitions and structural lemmas for Block Triangular Row Lattice Triangular Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/BlockTriangularRowLatticeTriangularBasis.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta Matrix Formalism.UG
noncomputable section
namespace GlobalTheory.InertZeta.RowSpan
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}
def rowM (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (k : Fin N) : Fin (N + 2) → L :=
  ∑ l, U k l • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid l) + ∑ l, V k l • g (mid l)
section
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
end
def rowsP (a : ℤ) (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (y : L) :
    Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i =>
  Fin.cases (motive := fun _ => Fin (N + 2) → L)
    (if 0 ≤ a then (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 else g 0)
    (Fin.lastCases (motive := fun _ => Fin (N + 2) → L)
      (y • (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1))) (rowM g U V)) i
section
variable (a : ℤ) (g : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (U V : Matrix (Fin N) (Fin N) L) (y : L)
end
def vecOf (x₀ : L) (xm : Fin N → L) (xl : L) : Fin (N + 2) → L := fun i =>
  Fin.cases (motive := fun _ => L) x₀ (Fin.lastCases (motive := fun _ => L) xl xm) i
section
variable {g : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {g₀ U V C : Matrix (Fin N) (Fin N) L} {b : Fin N → L}
end
end GlobalTheory.InertZeta.RowSpan


