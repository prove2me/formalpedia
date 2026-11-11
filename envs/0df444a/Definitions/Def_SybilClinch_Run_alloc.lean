-- Prove2me | Definitions.Def_SybilClinch_Run_alloc
-- name    : SybilClinch_Run_alloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:06.950957+00:00
-- url     : https://prove2.me/theorems/b543d5a2-48c4-46dd-87ef-bfd1669b6fa1
-- title:
--   Cumulative allocation $X_I(p)$ of a set of identities
-- statement:
--   For a set $I$ of identities, $X_I(p)=\sum_{i\in I}x_i(p)$ is its cumulative allocation through clock price $p$, constant after the run ends. For $I$ the whole profile it is the aggregate allocation $X$ of (8).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, (8), p.9 (PDF p.11); §4.6, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_SybilClinch_Run

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, (8), printed p.9 (PDF p.11), and §4.6, printed p.21 (PDF p.23): the cumulative
allocation `X_I(p) = Σ_{i ∈ I} xᵢ(p)` of a set `I` of identities through clock price `p`
(constant after the run ends). For `I = ids` it is the aggregate allocation `X`. -/
def Run.alloc (R : Run) (I : Finset ℕ) (p : ℝ) : ℝ := ∑ i ∈ I, R.x i p

end SybilClinch


