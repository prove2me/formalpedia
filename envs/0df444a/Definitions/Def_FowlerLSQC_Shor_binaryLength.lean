-- Prove2me | Definitions.Def_FowlerLSQC_Shor_binaryLength
-- name    : FowlerLSQC_Shor_binaryLength
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:20.93911+00:00
-- url     : https://prove2.me/theorems/46e9cbdd-711c-499a-9e77-a20b7fdfdd44
-- title:
--   Binary length $L$ of $N$
-- statement:
--   For a natural number $N$, its **binary length** $L$ is the number of binary digits of $N$. For $N\ge1$ it is the unique $L$ with
--   $$
--   2^{L-1}\le N<2^{L},
--   $$
--   i.e. $L=\lfloor\log_2 N\rfloor+1$.
--
--   In Shor's algorithm the $k$-register has $2L$ qubits, so the quantum Fourier transform acts on $2^{2L}$ basis states, and every outcome $j$ is compared with $c\,2^{2L}/r$.
--
--   **Formalization Note** The book writes "$L=\ln_2 N$ be the binary length of $N$"; $\ln_2$ is a slip for $\log_2$, and the defining phrase "binary length" is Mathlib's `Nat.size N`. For $N$ not a power of two this also equals $\lceil\log_2 N\rceil$.
-- source:
--   Fowler, Towards Large-Scale Quantum Computation, arXiv:quant-ph/0506126v1, Ch. 7, p.75 (PDF p.93)

import Mathlib

namespace FowlerLSQC.Shor

/-- The binary length `L` of a natural number `N`, Fowler, *Towards Large-Scale Quantum
Computation*, arXiv:quant-ph/0506126v1, Ch. 7, p.75 (PDF 93): "Let L = ln2 N be the binary length
of N". It is the number of binary digits of `N`, so `2^(L − 1) ≤ N < 2^L` for `N ≥ 1`.

**Formalization Note** The book's "ln2 N" is a slip for log₂ N; the defining phrase is "the
binary length of N", which is Mathlib's `Nat.size N` (`= Nat.log 2 N + 1` for `N ≥ 1`). For an `N`
that is not a power of two this also equals `⌈log₂ N⌉`. -/
def binaryLength (N : ℕ) : ℕ := Nat.size N

end FowlerLSQC.Shor


