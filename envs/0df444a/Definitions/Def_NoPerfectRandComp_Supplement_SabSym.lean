-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_SabSym
-- name    : NoPerfectRandComp_Supplement_SabSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:12:14.176413+00:00
-- url     : https://prove2.me/theorems/8cb8e5c1-3026-41e4-b50a-04ae7e747b1c
-- title:
--   Sabotage alphabet $\{0,1,*,\dagger\}$
-- statement:
--   The four letters of sabotaged inputs: the two Boolean letters $0, 1$ and the two **wildcards** $*$ and $\dagger$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.2, p.4

import Mathlib

namespace NoPerfectRandComp

namespace Supplement

/-- The four-letter alphabet `{0, 1, ∗, †}` of sabotaged inputs (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.2, p.4):
a Boolean letter `bit b`, or one of the two wildcards `star` (`∗`) and `dagger` (`†`). -/
inductive SabSym where
  | bit (b : Bool)
  | star
  | dagger
  deriving DecidableEq

end Supplement

end NoPerfectRandComp


