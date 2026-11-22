-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:37.023701+00:00
-- url     : https://prove2.me/theorems/f42a19b0-35d0-49e5-abba-4b5fc821db6d
-- title:
--   LWedge
-- statement:
--   Definitions and structural lemmas for LWedge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LWedge.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
def ql_U : (N : ℕ) → (Fin N → Finset (Fin n)) → Finset (Fin n)
  | 0, _ => ∅
  | N + 1, D => D 0 ∪ ql_U N (Fin.tail D)
def ql_sW (R : Type*) [CommRing R] : (N : ℕ) → (Fin N → Finset (Fin n)) → R
  | 0, _ => 1
  | N + 1, D => wedgeSign R (D 0) (ql_U N (Fin.tail D)) * ql_sW R N (Fin.tail D)
def wedgeCoeff (R : Type*) [CommRing R] {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) : R :=
  if ql_U N D = L then ql_sW R N D else 0
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)
def ql_P (R : Type*) [CommRing R] {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n))
    (i : Fin N → Finset (Fin n)) : R :=
  ∑ D : Fin N → Finset (Fin n), (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D L
end Formalism.InvariantFactorPaths.ColumnFamilies


