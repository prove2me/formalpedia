-- Prove2me | Definitions.Def_SybilClinch_Run_Terminates
-- name    : SybilClinch_Run_Terminates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:42:42.533017+00:00
-- url     : https://prove2.me/theorems/52d1d551-684a-4b8c-909f-1ea0a5d4d4aa
-- title:
--   Termination condition at a clock price
-- statement:
--   The run ends at clock price $p$ if the stopping allocation (20) is executed at $p$, or if after all fixed-price operations at $p$ no active identity remains (which includes the case that all effective budgets are exhausted). Capacity saturation is not a terminal condition.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.5, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_SybilClinch_Run_stopTest

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.5, printed p.12 (PDF p.14): the run ends at clock price `p` if (1) the stopping
allocation is executed at `p`, or (2) after all fixed-price operations at `p` no active identity
remains (which covers (3), all effective budgets exhausted).

**Formalization Note.** Activity after the operations at `p` is read before the terminal
cancellation: `vᵢ > p` and `qᵢ − yᵢ(p) > 0`. -/
def Run.Terminates (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) : Prop :=
  R.stopTest M P p ∨ ∀ i ∈ P.ids, ¬ ((p : WithTop ℝ) < P.v i ∧ 0 < P.q i - R.pay M i p)

end SybilClinch


