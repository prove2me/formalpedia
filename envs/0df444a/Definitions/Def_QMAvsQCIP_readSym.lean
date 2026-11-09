-- Prove2me | Definitions.Def_QMAvsQCIP_readSym
-- name    : QMAvsQCIP_readSym
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:14.351056+00:00
-- url     : https://prove2.me/theorems/9a898a4d-dc39-4a31-8c3b-1a937e0bf307
-- title:
--   Binary encoding of symbols
-- statement:
--   A block of $B=\lceil\log_2 q^\lambda\rceil$ bits $b_0,\dots,b_{B-1}$ denotes the integer $N=\sum_j b_j2^j$. If $N<q^\lambda$, the block encodes the symbol $a\in\Sigma=\mathbb F_q^\lambda$ whose base-$q$ digits are $a_k=\lfloor N/q^k\rfloor \bmod q$ (so $N=\sum_k a_kq^k$); otherwise it encodes no symbol.
--
--   This fixes how symbol registers $|a\rangle$ of the predicate-preimage state, and the decoder's output, are written in qubits.
--
--   **Formalization Note** The paper leaves this encoding implicit. Every symbol has exactly one code, and distinct accepted blocks denote distinct symbols.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 2, p.18; Eq. (3)

import Definitions.Def_QMAvsQCIP_Sym
import Definitions.Def_QMAvsQCIP_symBits

set_option autoImplicit false

namespace QMAvsQCIP

/-- The fixed binary **symbol encoding**: a block of `⌈log₂ q^λ⌉` bits `b_0, …, b_{B−1}` is read as
the integer `N = ∑_j b_j 2^j` (little-endian); if `N < q^λ` it denotes the symbol
`a ∈ Σ = F_q^λ` with base-`q` digits `a_k = ⌊N / q^k⌋ mod q`, i.e. `N = ∑_k a_k q^k`, and
otherwise no symbol (`none`).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 2, p.18 (PDF p.21) and Eq. (3): the `a(λ) = 2q⌈log₂ |Σ|⌉`-qubit state holds `2q`
registers of `⌈log₂ |Σ|⌉` qubits, each spanned by symbols `|a⟩`, `a ∈ Σ`.

**Formalization Note.** The paper leaves the encoding of symbols by bit strings implicit; this
one is injective on the strings it accepts, and every symbol has exactly one code. -/
def readSym (lam q : ℕ) (bits : Fin (symBits lam q) → Bool) : Option (Sym lam q) :=
  let N : ℕ := ∑ j : Fin (symBits lam q), if bits j then 2 ^ j.val else 0
  if N < q ^ lam then some (fun k => ((N / q ^ k.val % q : ℕ) : ZMod q)) else none

end QMAvsQCIP


