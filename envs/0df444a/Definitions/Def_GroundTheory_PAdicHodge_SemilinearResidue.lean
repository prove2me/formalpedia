-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
-- name    : GroundTheory_PAdicHodge_SemilinearResidue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:11.172311+00:00
-- url     : https://prove2.me/theorems/0280bd40-241a-4831-9341-e60edd5992cb
-- title:
--   Semilinear Residue
-- statement:
--   Definitions and structural lemmas for Semilinear Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/SemilinearResidue.lean

import Mathlib
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
open Polynomial Module Finset
namespace SemilinearResidue
section Poly
variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
noncomputable def recPoly (q : ℕ) (c : ℕ → k) (ε : k) : ℕ → k[X]
  | 0 => C (c 0) * X ^ q - C ε
  | i + 1 => recPoly q c ε i ^ q + C (c (i + 1)) * X ^ q
variable {e : ℕ}
end Poly
section Vec
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}
end Vec
end SemilinearResidue
end GroundTheory.PAdicHodge


