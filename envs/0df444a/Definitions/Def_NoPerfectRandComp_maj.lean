-- Prove2me | Definitions.Def_NoPerfectRandComp_maj
-- name    : NoPerfectRandComp_maj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:05.807176+00:00
-- url     : https://prove2.me/theorems/a175b13a-aead-4b64-b9d2-c70747c65831
-- title:
--   Majority $\mathrm{Maj}_k$
-- statement:
--   The **majority** function on $k$ bits is one exactly when more than half of its input bits are one:
--   $$
--   \mathrm{Maj}_k(x) = 1 \iff 2\,|\{i : x_i = 1\}| > k .
--   $$
--   It is used at odd $k$, where there are no ties.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §2.1, p.4

import Mathlib

namespace NoPerfectRandComp

/-- Majority `Maj_k` on `k` bits (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §2.1, p.4): one exactly when more than half of the
bits are one. Used at odd `k`, where there are no ties. -/
def maj (k : ℕ) (x : Fin k → Bool) : Bool :=
  decide (k < 2 * (Finset.univ.filter (fun i => x i = true)).card)

end NoPerfectRandComp


