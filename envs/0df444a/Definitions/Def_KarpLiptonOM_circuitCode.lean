-- Prove2me | Definitions.Def_KarpLiptonOM_circuitCode
-- name    : KarpLiptonOM_circuitCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:40:56.21239+00:00
-- url     : https://prove2.me/theorems/d6a3b074-848a-44d8-9c29-1e7c60d39094
-- title:
--   Fixed encoding of a circuit by a string of length $\ell(n, s)$
-- statement:
--   A circuit $C$ with $n$ inputs and at most $s$ gates is encoded by the string formed by the codes of its gates (in order) followed by empty slots of zeros, one for each of the $s - \mathrm{size}(C)$ missing gates. The code has length exactly $\ell(n, s)$, distinct circuits get distinct codes, and both recognizing codes and evaluating the encoded circuit take polynomial time.
--
--   **Formalization Note** The paper fixes "an encoding" without specifying it; this concrete one is used in Lemma A.3.9's "lexicographically first circuit".
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (fixed encoding of circuits)

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit
import Definitions.Def_KarpLiptonOM_gateCode

namespace KarpLiptonOM

/-- The fixed encoding of a circuit with `n` inputs and at most `s` gates by a string of length
exactly `ℓ(n, s)` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20): the codes of its gates (wire fields of
`Nat.size (n + s)` bits) followed by `s − size` empty slots of zeros.

**Formalization Note** On circuits with at most `s` gates the code has length `circuitLen n s` and
is injective; whether a string is such a code, and the circuit's value, are decidable in polynomial
time. A string "encodes a circuit" when it is `circuitCode n s C` for some `C` with at most `s` gates. -/
def circuitCode (n s : ℕ) (C : Circuit n) : List Bool :=
  (C.gates.map (gateCode (Nat.size (n + s)))).flatten ++
    List.replicate ((s - C.gates.length) * (3 + 2 * Nat.size (n + s))) false

end KarpLiptonOM


