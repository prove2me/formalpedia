-- Prove2me | Definitions.Def_CompNonlocal_decDyadic
-- name    : CompNonlocal_decDyadic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:06.249165+00:00
-- url     : https://prove2.me/theorems/df734089-0ca0-41ca-bb27-6b6cba82b86d
-- title:
--   Decoding a signed dyadic rational
-- statement:
--   A fixed self-delimiting bit format for real outputs: a sign bit, a unary length $k$, then $2k$ bits of a natural number $m$; the value is $\pm m/2^k$. The decoder returns the value and the unread rest of the string. Every signed dyadic rational is decodable, so decoded values are dense in $\mathbb R$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definitions 14, 15, pp.33–34

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- Self-delimiting decoding of a signed dyadic rational from the front of a bit string, returning
the value and the unread rest. Głuch, Morimae, *From Computational Nonlocality to Public-Key
Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), has algorithms
output real numbers and vectors (Definition 14, p.33: "outputs a vector r̂_S ∈ B³"; Definition 15,
p.34: "outputs r̃_J(T) ∈ [−1, 1]") without fixing a bit format; this one is fixed for the mission.

**Formalization Note** The format is: a sign bit `b` (`true` = negative), a unary `k` (`k` ones and
a zero), then `2k` bits read as a natural number `m` in binary (most significant first); the value
is `±m / 2^k`. Every signed dyadic rational has such a code, so every real is a limit of decodable
values. A string that ends early is read with the bits it has. -/
noncomputable def decDyadic : Str → ℝ × Str
  | [] => (0, [])
  | b :: rest =>
    let k := (rest.takeWhile fun c => c).length
    let r := rest.drop (k + 1)
    let m := (r.take (2 * k)).foldl (fun acc c => 2 * acc + if c then 1 else 0) 0
    ((if b then -1 else 1) * ((m : ℕ) : ℝ) / 2 ^ k, r.drop (2 * k))

end CompNonlocal


