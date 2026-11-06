-- Prove2me | Definitions.Def_BlockBochner_blockUnion
-- name    : BlockBochner_blockUnion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:27.464002+00:00
-- url     : https://prove2.me/theorems/480a826d-bb11-4117-8ade-2cac9e6ee0b5
-- title:
--   The retained sites $T=T_1\sqcup\dots\sqcup T_m$
-- statement:
--   For blocks $T_1,\dots,T_m\subseteq V$, $T=\bigcup_aT_a$; for disjoint blocks this is the disjoint union $T_1\sqcup\dots\sqcup T_m$.
--
--   **Formalization Note** Blocks are indexed by `Fin m`; disjointness is a hypothesis of the theorems.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.2, p.3; Theorem 3, p.4

import Mathlib

namespace BlockBochner

/-- **The retained sites `T = T₁ ⊔ ⋯ ⊔ T_m`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.2, p.3 and Theorem 3, p.4: the union of the
blocks `T₁, …, T_m`.

**Formalization Note** Blocks are indexed by `Fin m`; disjointness is a hypothesis of the theorems
that use it. -/
def blockUnion {V : Type*} [DecidableEq V] {m : ℕ} (T : Fin m → Finset V) : Finset V :=
  Finset.univ.biUnion T

end BlockBochner


