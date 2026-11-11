-- Prove2me | Definitions.Def_SybilClinch_Run_budPre
-- name    : SybilClinch_Run_budPre
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:17.758748+00:00
-- url     : https://prove2.me/theorems/b15dc33b-33f8-42ad-a314-0e7c483dcfa2
-- title:
--   Effective budget before the events at a price
-- statement:
--   At an event price $p$, the effective budget of identity $i$ before any operation at $p$ is $q_i-y_i(p^-)$ if the identity has not exited before $p$ ($p\le v_i$), and $0$ otherwise; here $y_i(p^-)$ is the left limit. At the initial price $p_\star$ every eligible identity has $b_i=q_i$ and ineligible identities are removed.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2 and §3.4, pp.9–11 (PDF pp.11–13)

import Mathlib
import Definitions.Def_SybilClinch_Run_pay
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2 and §3.4, printed pp.9–11 (PDF pp.11–13): the effective budget of identity `i` at
clock price `p` *before* the events at `p` are processed (the left limit of the path). At the
initial price every eligible identity (`vᵢ ≥ p⋆`) has `bᵢ = qᵢ`, ineligible ones are removed.

**Formalization Note.** `qᵢ − yᵢ(p⁻)` if `i ∈ ids` and `p ≤ vᵢ` (the identity has not exited
before `p`), else `0`; `yᵢ(p⁻)` is `Function.leftLim`, which is `0` at `p = p⋆` because payments
vanish below `p⋆`. -/
noncomputable def Run.budPre (M : TargetMech) (P : OneSidedProfile) (R : Run) (i : ℕ) (p : ℝ) :
    ℝ :=
  if i ∈ P.ids ∧ (p : WithTop ℝ) ≤ P.v i then P.q i - Function.leftLim (R.pay M i) p else 0

end SybilClinch


