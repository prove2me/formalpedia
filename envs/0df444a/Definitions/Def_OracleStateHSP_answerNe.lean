-- Prove2me | Definitions.Def_OracleStateHSP_answerNe
-- name    : OracleStateHSP_answerNe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:17.414234+00:00
-- url     : https://prove2.me/theorems/a1f79fd0-78e2-40b2-b3c5-a7ca4d617ea9
-- title:
--   Answer-difference matrix $1_{s(x) \ne s(y)}$
-- statement:
--   For $s : X \to E$, $1_{s(x)\ne s(y)}$ is the $X \times X$ matrix whose $(x, y)$ entry is $1$ if $s(x) \ne s(y)$ and $0$ otherwise.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, §4.1, p.36, before Theorem 4.4

import Mathlib

namespace OracleStateHSP

/-- The `X × X` matrix `1_{s(x) ≠ s(y)}` whose `(x, y)` entry is `1` if `s(x) ≠ s(y)` and `0`
otherwise (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, §4.1, p.36, before Theorem 4.4). -/
def answerNe {X E : Type*} [DecidableEq E] (s : X → E) : Matrix X X ℂ :=
  Matrix.of fun x y => if s x = s y then 0 else 1

end OracleStateHSP


