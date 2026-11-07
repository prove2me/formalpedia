-- Prove2me | Definitions.Def_StochAutoreg_lastToken
-- name    : StochAutoreg_lastToken
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:33.165805+00:00
-- url     : https://prove2.me/theorems/6463d927-1189-4495-8e95-3eaf091de314
-- title:
--   Last token $Z_M$ of a trajectory
-- statement:
--   The last generated token $Z_M$ of a trajectory $z\in\{0,1\}^M$.
--
--   **Formalization Note** The paper has $M\ge1$; at $M=0$ the value is the token $0$, and every statement assumes $M\ge 1$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.2

import Mathlib

namespace StochAutoreg

/-- The last generated token `Z_M` of a trajectory `z : Fin M → Bool`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.2.

**Formalization Note.** The paper has `M ≥ 1`. For `M = 0` there is no last token and the value is
`false`; every statement about `lastToken` assumes `1 ≤ M`. -/
def lastToken {M : ℕ} (z : Fin M → Bool) : Bool :=
  if h : 0 < M then z ⟨M - 1, Nat.sub_lt h Nat.one_pos⟩ else false

end StochAutoreg


