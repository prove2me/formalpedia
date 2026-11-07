-- Prove2me | Definitions.Def_KarpLiptonOM_Tape
-- name    : KarpLiptonOM_Tape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:30.051342+00:00
-- url     : https://prove2.me/theorems/e5198d42-ed0c-4ceb-a3ef-b8da4fe09b65
-- title:
--   Turing-machine tape (left part, scanned square, right part)
-- statement:
--   A **tape** of a Turing machine with tape symbols $\Gamma$ consists of the contents to the left of the head (nearest square first), the scanned square, and the contents to the right of the head. The blank symbol is a separate value, distinct from every symbol of $\Gamma$.
--
--   This is the configuration format of the published one-tape model `CookPvsNP`, used here for the two tapes (work tape and query tape) of an oracle Turing machine.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (machines); tape format of CookPvsNP_defs

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace KarpLiptonOM

/-- A tape of a Turing machine, in the style of the published Cook model (`CookPvsNP.Cfg`): the
squares left of the head (nearest first), the scanned square, and the squares to its right; `none`
is the blank. Used for the work tape and the query tape of oracle machines
(Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20: "oracle machines are deterministic"). -/
structure Tape (Γ : Type) where
  /-- squares to the left of the head, nearest first -/
  left : List (Option Γ)
  /-- the scanned square -/
  head : Option Γ
  /-- squares to the right of the head -/
  right : List (Option Γ)

end KarpLiptonOM


