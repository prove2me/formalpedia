-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:55.624795+00:00
-- url     : https://prove2.me/theorems/501fe5f0-388b-49c0-9b45-e6eec0a816cc
-- title:
--   Lattice Elementary Divisors
-- statement:
--   Definitions and structural lemmas for Lattice Elementary Divisors, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LatticeElementaryDivisors.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
namespace GlobalTheory.LatticeMinuscule
open Matrix
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
end GlobalTheory.LatticeMinuscule


