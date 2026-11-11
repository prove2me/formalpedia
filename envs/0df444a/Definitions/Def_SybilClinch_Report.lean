-- Prove2me | Definitions.Def_SybilClinch_Report
-- name    : SybilClinch_Report
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:46.71104+00:00
-- url     : https://prove2.me/theorems/b8e2b9d2-f3a2-4b32-a197-a95f234eaff3
-- title:
--   Order report $(\text{direction},\ \text{value},\ \text{budget})$
-- statement:
--   A reported (or true) type consists of a direction, a value and a budget. For a sell-$Y$ identity $i$ it is $(v_i,q_i)$: $v_i$ is the value of one unit of $X$ in units of $Y$, and $q_i$ the budget in $Y$. For a sell-$X$ identity it is $(u_i,r_i)$: $u_i$ is the value of one unit of $X$ in units of $Y$, and $r_i$ the budget in $X$. Both directions use the same price scale ($Y$ per $X$).
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, p.5 (PDF p.7)

import Mathlib
import Definitions.Def_SybilClinch_Dir

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.1, printed p.5 (PDF p.7): a reported (or true) order type. For a sell-`Y` identity it is
`(vᵢ, qᵢ)`: value `vᵢ` of one unit of `X` in units of `Y`, budget `qᵢ` in `Y`. For a sell-`X`
identity it is `(uᵢ, rᵢ)`: value `uᵢ` of one unit of `X` in units of `Y`, budget `rᵢ` in `X`.

**Formalization Note.** `val` is `vᵢ` or `uᵢ` and `bud` is `qᵢ` or `rᵢ`, according to `dir`. Both
directions use the same price scale (`Y` per `X`), as in the paper. -/
structure Report where
  /-- The direction of the order. -/
  dir : Dir
  /-- The value `vᵢ` (sell-`Y`) or `uᵢ` (sell-`X`), in units of `Y` per unit of `X`. -/
  val : ℝ
  /-- The budget `qᵢ` (in `Y`, sell-`Y`) or `rᵢ` (in `X`, sell-`X`). -/
  bud : ℝ

end SybilClinch


