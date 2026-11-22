-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LaplaceExpansionColumn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:00.733188+00:00
-- url     : https://prove2.me/theorems/86d29457-6686-497e-ad97-3a5e16f398e8
-- title:
--   Laplace Expansion Column
-- statement:
--   Definitions and structural lemmas for Laplace Expansion Column, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/LaplaceExpansionColumn.lean

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
def ql_sr (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R :=
  ∏ a ∈ A, ∏ k ∈ K, (if k < a then (-1 : R) else 1)
def wedgeSign (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R := if Disjoint A K then ql_sr R A K else 0
def ql_w (R : Type*) [CommRing R] (A K I : Finset (Fin n)) : R := if A ∪ K = I then wedgeSign R A K else 0
variable {R : Type*} [CommRing R]
variable (g : Matrix (Fin n) (Fin n) R)
end Formalism.InvariantFactorPaths.ColumnFamilies


