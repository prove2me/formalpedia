-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_xorF
-- name    : NoPerfectRandComp_Supplement_xorF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:07:08.563067+00:00
-- url     : https://prove2.me/theorems/f0936934-d9d1-487a-84a1-e3ff86ea1145
-- title:
--   Parity $\mathrm{XOR}_k$
-- statement:
--   The parity function on $k$ bits:
--   $$
--   \mathrm{XOR}_k(x) = x_1\oplus\cdots\oplus x_k,
--   $$
--   which is $1$ exactly when an odd number of the bits are $1$.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.1, p.4

import Mathlib

namespace NoPerfectRandComp

namespace Supplement

/-- The parity function `XOR_k` on `k` bits (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4): one exactly when an odd
number of the bits are one. -/
def xorF (k : ℕ) (x : Fin k → Bool) : Bool :=
  decide ((Finset.univ.filter (fun i => x i = true)).card % 2 = 1)

end Supplement

end NoPerfectRandComp


