-- Prove2me | Definitions.Def_SybilClinch_Run_preResid
-- name    : SybilClinch_Run_preResid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:14.633715+00:00
-- url     : https://prove2.me/theorems/1cf5abd2-7a56-4209-b0df-3ddd2efe689a
-- title:
--   Residual supply after the lump at an event price
-- statement:
--   At clock price $p$, after incorporating the entire target lump (19) and before any fixed-price operation, the residual supply is $S=T(p,X^-,Y^-)-X^-$, where $(X^-,Y^-)$ is the aggregate state just before $p$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, (19), p.11 (PDF p.13)

import Mathlib
import Definitions.Def_SybilClinch_Run_pay
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.4, (19), printed p.11 (PDF p.13): the residual supply at an event price `p` after
incorporating the entire target lump and before any fixed-price operation:
`S = T(p, X⁻, Y⁻) − X⁻`, where `(X⁻, Y⁻)` is the state just before `p` (left limits).

**Formalization Note.** Evaluating the right-continuous target at `p` on the pre-event state
incorporates the whole jump `ΔT` of (19). -/
noncomputable def Run.preResid (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) : ℝ :=
  M.T p (∑ i ∈ P.ids, Function.leftLim (R.x i) p) (∑ i ∈ P.ids, Function.leftLim (R.pay M i) p) -
    ∑ i ∈ P.ids, Function.leftLim (R.x i) p

end SybilClinch


