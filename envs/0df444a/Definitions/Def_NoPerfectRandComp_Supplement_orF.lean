-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_orF
-- name    : NoPerfectRandComp_Supplement_orF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:07:38.056755+00:00
-- url     : https://prove2.me/theorems/3682b48d-529c-4c7b-96bc-b891a6407e16
-- title:
--   $\mathrm{OR}_k$
-- statement:
--   The OR function on $k$ bits: $\mathrm{OR}_k(x) = x_1\vee\cdots\vee x_k$, which is $1$ exactly when some bit is $1$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §9, p.37

import Mathlib

namespace NoPerfectRandComp

namespace Supplement

/-- The function `OR_k` on `k` bits (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §9, p.37): one exactly when some bit is one. -/
def orF (k : ℕ) (x : Fin k → Bool) : Bool :=
  decide (∃ i, x i = true)

end Supplement

end NoPerfectRandComp


