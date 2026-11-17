-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_andF
-- name    : NoPerfectRandComp_Supplement_andF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:07:23.099469+00:00
-- url     : https://prove2.me/theorems/09bae7f2-3a15-47da-9818-fa0dbd436d15
-- title:
--   $\mathrm{AND}_k$
-- statement:
--   The AND function on $k$ bits: $\mathrm{AND}_k(x) = x_1\wedge\cdots\wedge x_k$, which is $1$ exactly when every bit is $1$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §9, p.37; Lemma 10.5, p.52

import Mathlib

namespace NoPerfectRandComp

namespace Supplement

/-- The function `AND_k` on `k` bits (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §9, p.37 and Lemma 10.5, p.52): one exactly
when every bit is one. -/
def andF (k : ℕ) (x : Fin k → Bool) : Bool :=
  decide (∀ i, x i = true)

end Supplement

end NoPerfectRandComp


