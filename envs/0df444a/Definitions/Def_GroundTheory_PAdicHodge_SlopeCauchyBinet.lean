-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_SlopeCauchyBinet
-- name    : GroundTheory_PAdicHodge_SlopeCauchyBinet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:46.994312+00:00
-- url     : https://prove2.me/theorems/3f2ecac1-a604-4634-8f7e-f728563d736e
-- title:
--   Slope Cauchy Binet
-- statement:
--   Definitions and structural lemmas for Slope Cauchy Binet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SlopeCauchyBinet.lean

import Mathlib
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_ExistsMaxMinorNeZeroOfLinearIndependentAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.PAdicHodge
open Matrix Finset Equiv
abbrev KSubset (n k : ℕ) := {s : Finset (Fin n) // s.card = k}
def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n := s.1.orderEmbOfFin s.2
variable {R : Type*} [CommRing R]
section CauchyBinet
variable {k n : ℕ}
end CauchyBinet
section Minors
variable {m n k : ℕ}
def maxMinor (B : Matrix (Fin n) (Fin k) R) (s : KSubset n k) : R :=
  (B.submatrix s.emb id).det
def compound (k : ℕ) (P : Matrix (Fin m) (Fin n) R) : Matrix (KSubset m k) (KSubset n k) R :=
  Matrix.of fun s t => (P.submatrix s.emb t.emb).det
end Minors
section Independence
variable {n k : ℕ}
end Independence
end GroundTheory.PAdicHodge


