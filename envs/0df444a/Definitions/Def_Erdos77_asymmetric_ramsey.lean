-- Prove2me | Definitions.Def_Erdos77_asymmetric_ramsey
-- name    : Erdos77_asymmetric_ramsey
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-09-26T12:25:41.18176+00:00
-- url     : https://prove2.me/theorems/41e2a15a-6aec-410b-9e71-d6a398d12f8f
-- title:
--   Off-diagonal Ramsey number
-- statement:
--   For positive integers k and ell, this is the least number of vertices such that every red-blue coloring contains either a red clique of size k or a blue clique of size ell.
-- source:
--   Gupta, Ndiaye, Norin, and Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026.

import Mathlib

namespace Erdos77

/-- The asymmetric Ramsey number: the least order forcing a clique of size `k`
or an independent set of size `ell`. -/
noncomputable def asymmetricRamsey (k ell : Nat) : Nat :=
  sInf {n : Nat | ∀ G : SimpleGraph (Fin n),
    (∃ s : Finset (Fin n), G.IsNClique k s) ∨
    (∃ s : Finset (Fin n), Gᶜ.IsNClique ell s)}

end Erdos77


