-- Prove2me | Definitions.Def_SybilClinch_ExactSettle
-- name    : SybilClinch_ExactSettle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:58.816895+00:00
-- url     : https://prove2.me/theorems/9276f9ba-b144-437f-8efb-3672dca7cd5d
-- title:
--   Exact-settlement feasibility
-- statement:
--   An outcome of a reported profile is **exact-settlement feasible** if every identity satisfies its constraint (1) or (2) ($0\le S_i\le$ reported budget, $R_i\ge0$) and the net pool flows (3) satisfy
--   $$X_{\rm pool}<x_0,\qquad Y_{\rm pool}=C(X_{\rm pool}),$$
--   equivalently, the terminal pool reserves $(x_0-X_{\rm pool},\,y_0+Y_{\rm pool})$ lie on the reserve curve. Every unit paid to an identity is supplied by an opposite-side identity or the pool; no outside subsidy is used and no token is discarded.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, Definition 2.2, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_SybilClinch_AdmissibleAMM_C
import Definitions.Def_SybilClinch_flowX
import Definitions.Def_SybilClinch_flowY

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, Definition 2.2 (Exact-settlement feasibility), printed p.6 (PDF p.8).

An outcome `f` of the reported profile (identities `ids`, reports `rep`) is exact-settlement
feasible if every identity satisfies (1)/(2) (`0 ≤ sold ≤ bud`, `recv ≥ 0`) and the net pool flows
(3) satisfy `X_pool < x₀` and `Y_pool = C(X_pool)`, i.e. the terminal reserves
`(x₀ − X_pool, y₀ + Y_pool)` lie on the reserve curve. -/
def ExactSettle (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) (f : ℕ → Fill) : Prop :=
  (∀ i ∈ ids, 0 ≤ (f i).sold ∧ (f i).sold ≤ (rep i).bud ∧ 0 ≤ (f i).recv) ∧
    flowX ids rep f < A.x0 ∧ flowY ids rep f = A.C (flowX ids rep f)

end SybilClinch


