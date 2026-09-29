-- Prove2me | Definitions.Def_Erdos77_asymmetric_ramsey_v2
-- name    : Erdos77_asymmetric_ramsey_v2
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-09-26T12:26:15.450393+00:00
-- url     : https://prove2.me/theorems/e8a26bcf-6da8-4626-b254-34e3183161ef
-- title:
--   Asymmetric Ramsey number
-- statement:
--   For natural numbers k and ell, asymmetricRamsey k ell is the least number of vertices such that every graph on that many vertices contains a clique of size k or an independent set of size ell.
-- source:
--   Standard asymmetric Ramsey number definition; used to state Gupta, Ndiaye, Norin, and Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026v2, Theorem 1.

import Mathlib

namespace Erdos77

/-- The asymmetric Ramsey number: the least order forcing a clique of size `k`
or an independent set of size `ell`. -/
noncomputable def asymmetricRamsey (k ell : Nat) : Nat :=
  sInf {n : Nat | forall G : SimpleGraph (Fin n),
    Or (Exists fun s : Finset (Fin n) => G.IsNClique k s)
      (Exists fun s : Finset (Fin n) => (Compl.compl G).IsNClique ell s)}

end Erdos77


