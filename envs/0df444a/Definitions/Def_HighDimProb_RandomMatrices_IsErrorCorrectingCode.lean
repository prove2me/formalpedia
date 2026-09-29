-- Prove2me | Definitions.Def_HighDimProb_RandomMatrices_IsErrorCorrectingCode
-- name    : HighDimProb_RandomMatrices_IsErrorCorrectingCode
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:21:42.1779+00:00
-- url     : https://prove2.me/theorems/df2fe9b3-f446-45d1-a049-1438d8942193
-- title:
--   Encoding/decoding maps that correct $r$ errors
-- statement:
--   This is **Definition 4.3.3** (Error correcting code), the object Theorem 4.3.5 constructs.
--
--   Fix integers $k, n, r$. Maps $E : \{0,1\}^k \to \{0,1\}^n$ (encoding) and
--   $D : \{0,1\}^n \to \{0,1\}^k$ (decoding) **correct $r$ errors** if, for every message
--   $x \in \{0,1\}^k$ and every received string $y \in \{0,1\}^n$ that differs from the codeword
--   $E(x)$ in at most $r$ bits (Hamming distance, companion definition `hammingDist`),
--   $D(y) = x$: decoding always recovers the original message despite up to $r$ corrupted bits.
--
--   **Formalization Note** Only the correction property is encoded as a proposition on the pair
--   $(E, D)$; no injectivity of $E$ is asserted separately (it follows from the correction
--   property applied at $y = E(x)$, since $d_H(E(x), E(x)) = 0 \le r$, but is not needed as a
--   hypothesis).
-- source:
--   Vershynin, High-Dimensional Probability (2018), Definition 4.3.3, p. 87 (PDF p. 95)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_hammingDist

namespace HighDimProb.RandomMatrices

/-- **Definition 4.3.3** (Error correcting code), Vershynin, *High-Dimensional Probability*
(2018), p. 87-88. Fix integers `k, n, r`. Maps `E : {0,1}^k → {0,1}^n` and `D : {0,1}^n →
{0,1}^k` are encoding and decoding maps that can correct `r` errors if `D(y) = x` for every
word `x ∈ {0,1}^k` and every string `y ∈ {0,1}^n` that differs from `E(x)` in at most `r` bits
(Hamming distance `≤ r`). -/
def IsErrorCorrectingCode {k n r : ℕ} (E : (Fin k → Bool) → (Fin n → Bool))
    (D : (Fin n → Bool) → (Fin k → Bool)) : Prop :=
  ∀ x : Fin k → Bool, ∀ y : Fin n → Bool, hammingDist y (E x) ≤ r → D y = x

end HighDimProb.RandomMatrices


