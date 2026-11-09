-- Prove2me | Definitions.Def_InflMaxAdapt_Policy_seeds
-- name    : InflMaxAdapt_Policy_seeds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:58.910678+00:00
-- url     : https://prove2.me/theorems/10c8ab2a-b4b8-4950-86fa-f61bd3fe3d2c
-- title:
--   Seed set $S(\pi)$ of a policy
-- statement:
--   The **seed set** of a policy $\pi$ is $S(\pi) = \{v_1, \dots, v_k\}$, the set of vertices probed by $\pi$ for the given external randomness and realization. A vertex probed several times is counted once.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_InflMaxAdapt_Policy_run

namespace InflMaxAdapt

/-- The set of seeds `S(π) = {v_1, …, v_k}` probed by a policy (Section 1.1, printed p.2 = PDF
p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), for external randomness `ω` and cascade map `C` of the realization. A repeated seed
is counted once. -/
def Policy.seeds {V : Type} [DecidableEq V] {k : ℕ} {Ω : Type} (π : Policy V k Ω) (ω : Ω)
    (C : V → Finset V) : Finset V :=
  Finset.univ.image (π.run ω C)

end InflMaxAdapt


