-- Prove2me | Definitions.Def_SybilClinch_Run_preExit
-- name    : SybilClinch_Run_preExit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:40:23.646322+00:00
-- url     : https://prove2.me/theorems/6d1a5725-b58b-4a8b-aee1-a9cb4604a05b
-- title:
--   Exiting identities at an event price
-- statement:
--   At clock price $p$, the exiting identities are $\mathrm{Exit}=\{i:v_i=p,\ b_i>0\}$, evaluated on pre-event budgets. At the initial price these are the identities with $v_i=p_\star$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (12), and §3.4, pp.9–11 (PDF pp.11–13)

import Mathlib
import Definitions.Def_SybilClinch_Run_budPre

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (12), and §3.4, printed pp.9–11 (PDF pp.11–13): the exiting identities at an event
price `p`, `Exit = {i : vᵢ = p, bᵢ > 0}` on the pre-event budgets (at `p = p⋆` these are the
identities with `vᵢ = p⋆`). -/
noncomputable def Run.preExit (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) :
    Finset ℕ :=
  P.ids.filter (fun i => P.v i = (p : WithTop ℝ) ∧ 0 < R.budPre M P i p)

end SybilClinch


