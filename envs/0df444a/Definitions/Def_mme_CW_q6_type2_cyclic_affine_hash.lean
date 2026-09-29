-- Prove2me | Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
-- name    : mme_CW_q6_type2_cyclic_affine_hash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T22:22:40.308354+00:00
-- url     : https://prove2.me/theorems/309b1e12-a676-4cac-8766-0b920fd99d3f
-- title:
--   Affine Salem--Spencer hash for cyclic q=6 type-2 edges
-- statement:
--   This is the three-mode affine hash used for a cyclic triple of q=6 type-2 edges. The three constituent base offsets are specialized to $(2q,0,q)$. Consequently the first combined hash has zero affine offset, while the second and third have offsets $12q$ and $6q$; supported mixtures still satisfy the arithmetic-progression identity.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; affine specialization of the cyclic Salem--Spencer hash.

import Mathlib.Data.ZMod.Basic
import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

namespace MME

set_option autoImplicit false

def cwQ6Type2CyclicAffineHash (p N L G : ℕ) (q : (Fin 3 → Fin (2 * N) → ZMod p) × ZMod p) (i : Fin 3) (e : CWQ6Type2CyclicEdge N L G) : ZMod p :=
  match i with
  | ⟨0, _⟩ => cwQ6DoubledXHash (2 * q.2) (q.1 0) (e.1.1 0) + 4 * cwQ6DoubledZHash 0 (q.1 1) (e.2.1.1 2) - 2 * cwQ6DoubledYHash q.2 (q.1 2) (e.2.2.1 1)
  | ⟨1, _⟩ => cwQ6DoubledYHash (2 * q.2) (q.1 0) (e.1.1 1) - 2 * cwQ6DoubledXHash 0 (q.1 1) (e.2.1.1 0) + 4 * cwQ6DoubledZHash q.2 (q.1 2) (e.2.2.1 2)
  | ⟨2, _⟩ => cwQ6DoubledZHash (2 * q.2) (q.1 0) (e.1.1 2) + cwQ6DoubledYHash 0 (q.1 1) (e.2.1.1 1) + cwQ6DoubledXHash q.2 (q.1 2) (e.2.2.1 0)
  | ⟨r + 3, h⟩ => absurd h (by omega)

end MME


