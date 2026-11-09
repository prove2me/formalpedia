-- Prove2me | Definitions.Def_TermCycDich_HasRCycle
-- name    : TermCycDich_HasRCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:34.46075+00:00
-- url     : https://prove2.me/theorems/c0d3278a-397b-437f-b622-82a713c58b7c
-- title:
--   Yes-instance of Terminal Cyclability
-- statement:
--   The annotated graph $(G, R)$ is a **yes-instance of Terminal Cyclability** (T-Cycle) if $G$ has an $R$-cycle, that is, a simple cycle through all red vertices.
--
--   This is the predicate decided by every algorithm of the mission.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1, p.1 (PDF 3)

import Mathlib
import Definitions.Def_TermCycDich_IsRCycle

namespace TermCycDich

/-- `(G, R)` is a **yes-instance of Terminal Cyclability**: `G` has an `R`-cycle, a simple cycle
through every red vertex.

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), Section 1, p.1 (PDF 3): "The task is then to find a simple cycle in G containing all
vertices in R. This question, known as Terminal Cyclability or T-Cycle [...]".

**Formalization Note** The cycle is any closed walk `p : G.Walk u u` (any base point `u`) with
`IsRCycle G R p`. -/
def HasRCycle {V : Type} (G : SimpleGraph V) (R : Set V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), IsRCycle G R p

end TermCycDich


