-- Prove2me | Definitions.Def_SybilClinch_OneSidedProfile
-- name    : SybilClinch_OneSidedProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:05.194144+00:00
-- url     : https://prove2.me/theorems/f7eed656-c95b-4726-8280-e6ffaeb2297e
-- title:
--   One-sided profile of sell-$Y$ identities
-- statement:
--   A one-sided profile is a finite set of identities, identity $i$ reporting a clock value $v_i$ (units of $Y$ per unit of $X$) and a budget $q_i$ (units of $Y$).
--
--   **Formalization Note** Values lie in $\mathbb R\cup\{+\infty\}$ so that the infinite clock value $1/0$ of the reverse auction is representable; the one-sided results of §4 assume finite values.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, p.8 (PDF p.10); §5.2, footnote 2, p.27 (PDF p.29)

import Mathlib

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.1, printed p.8 (PDF p.10): a one-sided profile of sell-`Y` identities `ids`, identity
`i` reporting value `v i` and budget `q i`.

**Formalization Note.** Values live in `WithTop ℝ` so that the infinite clock value `1/0 = +∞` of
the reverse auction (§5.2, footnote 2, printed p.27) is representable; in the one-sided results of
§4 values are finite (`≠ ⊤`), as the paper states (p.28). -/
structure OneSidedProfile where
  /-- The finite set of identities. -/
  ids : Finset ℕ
  /-- The reported clock values `vᵢ`. -/
  v : ℕ → WithTop ℝ
  /-- The reported budgets `qᵢ`. -/
  q : ℕ → ℝ

end SybilClinch


