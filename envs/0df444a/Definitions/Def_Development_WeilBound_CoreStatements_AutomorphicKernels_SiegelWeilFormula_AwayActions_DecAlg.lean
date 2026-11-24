-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:05.020459+00:00
-- url     : https://prove2.me/theorems/06007cf3-4de8-4527-a950-8edeeffe0b75
-- title:
--   Dec Alg
-- statement:
--   Definitions and structural lemmas for Dec Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
def jF (n : ℕ) (ε : ℤ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks 0 1 ((ε : R) • 1) 0
def nM (t : Matrix (Fin n) (Fin n) R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R := fromBlocks 1 t 0 1
variable (c : R →+* R) (ε : ℤ)
end PositivityTheory.SiegelWeilFormula.KAway
end


