-- Prove2me | Definitions.Def_KarpLiptonOM_Supplement_sseInst
-- name    : KarpLiptonOM_Supplement_sseInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:38:59.509525+00:00
-- url     : https://prove2.me/theorems/6e29db74-f661-423a-b9a7-884c4ffbdc8d
-- title:
--   Instance encoding of set size estimation: $1^n0\,1^s0\,\langle C\rangle\,\mathrm{bin}(m)$
-- statement:
--   An instance of set size estimation is a pair $(C, m)$ of a Boolean circuit $C$ and a positive integer $m$ written in binary. For a circuit $C$ with $n$ inputs and at most $s$ gates, its binary string is
--
--   $$
--   1^n\,0\,1^s\,0\,\langle C\rangle_{n,s}\,\mathrm{bin}(m),
--   $$
--
--   where $\langle C\rangle_{n,s}$ is the paper's fixed code of circuits with $n$ inputs and at most $s$ gates, a string of length exactly $\ell(n,s)$, and $\mathrm{bin}(m)$ is the binary expansion of $m$, most significant bit first, without leading zeros.
--
--   The unary prefix fixes $n$ and $s$, the circuit code has a fixed length and every gate code begins with a presence bit, and $\mathrm{bin}(m)$ begins with $1$ when $m\ge 1$; so the string determines the instance, and it can be decoded in polynomial time. Writing $n$ and $s$ in unary makes the instance at least as long as the circuit's description.
--
--   **Formalization Note** The circuit code is the published `KarpLiptonOM.circuitCode` and $\mathrm{bin}(m)$ is `binW (Nat.size m) m`.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.3 ("Approximate counting"), p.22; circuit encoding §A.2.1, p.20

import Mathlib
import Definitions.Def_KarpLiptonOM_Circuit
import Definitions.Def_KarpLiptonOM_circuitCode
import Definitions.Def_KarpLiptonOM_binW

namespace KarpLiptonOM.Supplement

/-- The binary string encoding an instance `(C, m)` of set size estimation (SSE, Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.3,
"Approximate counting", p.22): a circuit `C` with `n` inputs and at most `s` gates and an
integer `m` given in binary. The string is `1ⁿ 0 1ˢ 0`, followed by the fixed circuit code
`circuitCode n s C` (length `ℓ(n, s)`, §A.2.1, p.20), followed by `m` in binary, most
significant bit first, without leading zeros (`binW (Nat.size m) m`).

**Formalization Note** `n` and `s` are written in unary, as a circuit description lists its inputs
and gates, so the instance length is at least `n + s`. On circuits with at most `s` gates and
`m ≥ 1` the encoding is injective (the unary prefix fixes `n` and `s`, the code has the fixed
length `ℓ(n, s)` and every gate code starts with a presence bit `1`, and the binary code of
`m ≥ 1` starts with `1`), and it is decodable in polynomial time. -/
def sseInst (n s : ℕ) (C : Circuit n) (m : ℕ) : List Bool :=
  List.replicate n true ++ false :: (List.replicate s true ++ false ::
    (circuitCode n s C ++ binW (Nat.size m) m))

end KarpLiptonOM.Supplement


