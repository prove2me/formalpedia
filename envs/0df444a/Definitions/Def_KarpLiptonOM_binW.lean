-- Prove2me | Definitions.Def_KarpLiptonOM_binW
-- name    : KarpLiptonOM_binW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:38:02.678948+00:00
-- url     : https://prove2.me/theorems/7b228224-c43a-4e2a-a3d3-6c1e3260f95f
-- title:
--   Fixed-width binary code of a number
-- statement:
--   For $b, v \in \mathbb N$, the $b$-bit binary code of $v$ is the string of the $b$ lowest binary digits of $v$, most significant first. It is used to write wire indices in the fixed circuit encoding.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (fixed encoding of circuits)

import Mathlib

namespace KarpLiptonOM

/-- The binary code of `v` with exactly `b` bits, most significant first (a building block of the
fixed circuit encoding, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20). -/
def binW (b v : ℕ) : List Bool := List.ofFn (fun j : Fin b => v.testBit (b - 1 - j))

end KarpLiptonOM


