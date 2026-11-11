-- Prove2me | Definitions.Def_SybilClinch_Run_bud
-- name    : SybilClinch_Run_bud
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:02.524781+00:00
-- url     : https://prove2.me/theorems/53447284-f87a-45d0-8c1e-b59be5de2dbb
-- title:
--   Effective remaining budget $b_i$
-- statement:
--   At clock price $p$, after the events at $p$, the effective remaining budget of identity $i$ is $b_i=q_i-y_i$ while the identity remains in the auction. Ineligible reports ($v_i<p_\star$) are removed; an identity that exits at its value without the run stopping has its unspent budget cancelled; and every unspent budget is cancelled at termination, so effective budgets are zero at and after the terminal state. Hence $b_i(p)=q_i-y_i(p)$ when $p<p_f$ and $p<v_i$, and $b_i(p)=0$ otherwise.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, p.9 (PDF p.11); §3.5, p.12 (PDF p.14); §4.6, (45), p.22 (PDF p.24)

import Mathlib
import Definitions.Def_SybilClinch_Run_pay
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, printed p.9 (PDF p.11), §3.5, printed p.12 (PDF p.14), and §4.6, (45), printed p.22
(PDF p.24): the effective remaining budget `bᵢ` at clock price `p` after the events at `p`.

While the identity remains in the auction, `bᵢ = qᵢ − yᵢ`. Ineligible reports (`vᵢ < p⋆`) are
removed; an identity that exits at its value `vᵢ` without the run stopping has its unspent budget
cancelled; and at termination every unspent budget is cancelled, effective budgets being zero at
and after the terminal state.

**Formalization Note.** Hence `bᵢ(p) = qᵢ − yᵢ(p)` exactly when `i ∈ ids`, `p < p_f` and `p < vᵢ`,
and `bᵢ(p) = 0` otherwise. (An identity with `vᵢ = p < p_f` exits at `p` with the stopping test
failing, so its budget is cancelled at `p`; ineligible identities have `vᵢ < p⋆ ≤ p`.) -/
noncomputable def Run.bud (M : TargetMech) (P : OneSidedProfile) (R : Run) (i : ℕ) (p : ℝ) : ℝ :=
  if i ∈ P.ids ∧ p < R.pf ∧ (p : WithTop ℝ) < P.v i then P.q i - R.pay M i p else 0

end SybilClinch


