-- Prove2me | Definitions.Def_DoublyEffIP_ppCode
-- name    : DoublyEffIP_ppCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:46.948646+00:00
-- url     : https://prove2.me/theorems/524d74a1-b62a-4ab5-beb8-08dd49b6db93
-- title:
--   Public parameters $\mathrm{pp}=(n,T,S,\sigma)$
-- statement:
--   The **public parameters** of a protocol are the input length $n$, the time bound $T=T(n)$, the space bound $S=S(n)$ and the soundness parameter $\sigma$. Both parties receive them, as the word
--
--   $$
--   \mathrm{pp}=\langle n\rangle\,\langle T\rangle\,\langle S\rangle\,\langle\sigma\rangle ,
--   $$
--
--   the concatenation of their self-delimited binary numerals.
--
--   The paper's protocols "have explicit access to the input parameters pp"; fixing them to these four numbers means a machine receives no information beyond them, so no constructibility of $T$ or $S$ is needed and no advice can be smuggled in.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4, p.10; proof of Theorem 5, p.15

import Mathlib
import Definitions.Def_DoublyEffIP_encBin

set_option autoImplicit false

namespace DoublyEffIP

/-- **The public parameters** `pp = (n, T(n), S(n), σ)` — Chen–Hong–Kalai–Xi, *Towards a Doubly
Efficient IP = PSPACE*, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.4,
p.10 ("both parties have explicit access to the input parameters pp"), and the proof of
Theorem 5, p.15 ("Both parties select the appropriate parameters").

The word given to every machine of a protocol before its other inputs: the input length `n`, the
time bound `T`, the space bound `S` and the soundness parameter `σ`, each in self-delimited binary.

**Formalization Note.** Only these four numbers are public parameters, so no machine receives
advice beyond them; no time- or space-constructibility of `T` or `S` is assumed. -/
def ppCode (n T S σ : ℕ) : List Bool := encBin n ++ encBin T ++ encBin S ++ encBin σ

end DoublyEffIP


