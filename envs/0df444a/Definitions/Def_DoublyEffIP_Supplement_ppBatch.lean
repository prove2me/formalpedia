-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_ppBatch
-- name    : DoublyEffIP_Supplement_ppBatch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:42:48.536141+00:00
-- url     : https://prove2.me/theorems/9c701a04-545b-4ce2-957a-cd000fca283a
-- title:
--   Public parameters of $\mathrm{Batch}(t,k)$
-- statement:
--   The public parameters of $\mathrm{Batch}(t,k)$ are the word $\langle\sigma\rangle\langle S\rangle\langle T\rangle\langle t\rangle\langle k\rangle$ of self-delimited binary numerals; for the augmented language, $\langle\Phi\rangle$ is appended. The machine $M$ is built into the protocol.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Theorem 7, p.19 (Batch(t, k) := (P(x), V)[S,T,t,k,⟨Φ⟩]); Protocol 1, p.21

import Mathlib
import Definitions.Def_DoublyEffIP_encBin

set_option autoImplicit false

namespace DoublyEffIP.Supplement

/-- **The public parameters of `Batch(t, k)`** — `Batch(t, k) := (P(x), V)[S,T,t,k,⟨Φ⟩]`
(Theorem 7, p.19; Protocol 1, p.21) with the soundness parameter `σ`, in Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…).

The word `⟨σ⟩ ⟨S⟩ ⟨T⟩ ⟨t⟩ ⟨k⟩` of self-delimited binary numerals; Theorem 7 appends `⟨Φ⟩`.

**Formalization Note.** Only these numbers (and `⟨Φ⟩`) are public parameters; the machine `M` is
built into the protocol. -/
def ppBatch (S T t k σ : ℕ) : List Bool := encBin σ ++ encBin S ++ encBin T ++ encBin t ++ encBin k

end DoublyEffIP.Supplement


