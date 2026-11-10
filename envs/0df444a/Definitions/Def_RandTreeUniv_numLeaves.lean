-- Prove2me | Definitions.Def_RandTreeUniv_numLeaves
-- name    : RandTreeUniv_numLeaves
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:10:23.926546+00:00
-- url     : https://prove2.me/theorems/e699a7bf-0035-4a64-9c19-c2869f8d7d61
-- title:
--   Number of leaves
-- statement:
--   The number of **leaves** of a graph $T$ is the number of vertices of degree exactly $1$. For trees it is the usual count of leaves, used in the split of $\mathcal T\setminus\mathcal T_1$ into trees with at most $e^{\Delta^5}\alpha$ leaves ($\mathcal T_2$) and with more ($\mathcal T_3$).
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §4, p.21 (PDF 22)

import Mathlib

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- The number of leaves (vertices of degree 1) of a graph (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §4, p.21 (PDF 22), "at most
`exp(∆⁵)α` leaves"). -/
noncomputable def numLeaves {V : Type*} [Fintype V] (T : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun v => T.degree v = 1).card

end RandTreeUniv


