-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:50.685326+00:00
-- url     : https://prove2.me/theorems/9a42e46f-7b08-48c9-975e-77da64fa2a24
-- title:
--   Qs Rem Iff Add
-- statement:
--   Definitions and structural lemmas for Qs Rem Iff Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsRemIffAdd.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsMnTranspose
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
def qs_rem (D : Finset ℤ) (K : ℤ → Finset (Fin n)) (m : ↥D → Fin n) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ D then (K c).erase (m ⟨c, h⟩) else K c
def qs_add (D : Finset ℤ) (J : ℤ → Finset (Fin n)) (a : ↥D → Fin n) : ℤ → Finset (Fin n) :=
  fun c => if h : c ∈ D then insert (a ⟨c, h⟩) (J c) else J c
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)
end Formalism.InvariantFactorPaths.ColumnFamilies


