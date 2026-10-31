-- Prove2me | Definitions.Def_RobustToDynamics_RLDLP
-- name    : RobustToDynamics_RLDLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:37:29.122302+00:00
-- url     : https://prove2.me/theorems/42347650-f2b2-4da3-9fd4-bc7283823d80
-- title:
--   A rational R-LD-LP instance $(A,b,c,G)$
-- statement:
--   A robust-to-linear-dynamics linear program (R-LD-LP) with rational data is
--   $$
--   \min_{x\in\mathbb R^n}\{c^Tx : G^kx\in P \text{ for } k=0,1,2,\dots\},\qquad P=\{x: Ax\le b\},
--   $$
--   display (2.2). Its input is the constraint data $(A,b,G)$ together with the objective $c\in\mathbb Q^n$.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, §2, (2.1)–(2.2), p.5

import Mathlib
import Definitions.Def_RobustToDynamics_LDData

namespace RobustToDynamics

/-- **A rational R-LD-LP instance `(A, b, c, G)`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, §2, (2.1)–(2.2), p.5:
"min_{x∈Rn} {cT x : Gk x ∈ P for k = 0, 1, 2, . . .}"; "The input to an R-LD-LP is fully defined
by c ∈ Rn, A ∈ Rm×n, b ∈ Rm, G ∈ Rn×n" (rational, footnote 3).

**Formalization Note.** The instance is the data `(A, b, G)` (`LDData`) together with an
objective `c ∈ ℚⁿ`. -/
structure RLDLP where
  /-- the constraint data `(A, b, G)` -/
  data : LDData
  /-- the objective vector `c ∈ ℚⁿ` -/
  c : Fin data.n → ℚ

end RobustToDynamics


