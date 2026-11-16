-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_DescribesRows
-- name    : DoublyEffIP_Supplement_DescribesRows
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:36:01.455039+00:00
-- url     : https://prove2.me/theorems/add92454-f1c8-4f4d-84e5-09fb6c2fccdb
-- title:
--   Description $\langle Q\rangle$ of a set of rows
-- statement:
--   Let $T_Q$ be a generator of set-description circuits and $p=\lceil\log_2 k\rceil$. A bit string $\langle Q\rangle$ **describes** the rows $s_0,\dots,s_{m-1}$ if the circuit $G$ that $T_Q$ generates on the shape $(m,1^{|\langle Q\rangle|},1^p)$ satisfies
--
--   $$
--   G\big(i,\langle Q\rangle\big)=s_i\qquad\text{for all } i<m ,
--   $$
--
--   with $i$ and $s_i<2^p$ written as $p$-bit strings. This is Definition 4: $\langle S\rangle$ describes $S=\{s_1,\dots,s_k\}\subset\{0,1\}^p$ if its $p$-space uniform implementation circuit satisfies $G(i,\langle S\rangle)=s_i$.
--
--   **Formalization Note** $G$ is a Boolean circuit, taken as an arithmetic circuit over $\mathrm{GF}(2)$ (XOR, AND and constants express every Boolean gate with constant overhead); its generator gate is read as $0$. Rows are $0$-based.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3.2, p.9, Definition 4

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_Circuit
import Definitions.Def_DoublyEffIP_Supplement_evalCircuit
import Definitions.Def_DoublyEffIP_Supplement_IsImpl
import Definitions.Def_DoublyEffIP_Supplement_setShape
import Definitions.Def_DoublyEffIP_Supplement_bitsIn
import Definitions.Def_DoublyEffIP_Supplement_numBits
import Definitions.Def_TreeEdgeRankPC_Transducer

set_option autoImplicit false

open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **A description of a set of rows** — Definition 4 (Descriptions of Sets) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…),
Section 3.2, p.9: "A bit string ⟨S⟩ ∈ {0,1}^B is a description of a set S = {s_1, …, s_k} ⊂
{0,1}^p if there exists a (multi-output) p-space uniform circuit G : [k] × {0,1}^B → {0,1}^p of
fan-in 2, called its implementation circuit, such that G(i, ⟨S⟩) = s_i for all i ∈ [k]."

`DescribesRows TQ k m descQ s`: with `p = ⌈log₂ k⌉` (the bits of a row index of a `k`-row matrix),
the circuit `G` that `TQ` outputs on the shape `(m, |descQ|, p)` maps `(i, descQ)` to the `p`-bit
binary form of `s i`, for every `i < m`, and each `s i < 2^p`.

**Formalization Note.** `G` is a Boolean circuit, taken as an arithmetic circuit over `GF(2)`
(Remark 2, p.9: Boolean circuits extend to arithmetic ones; XOR, AND and the constants give every
Boolean gate with constant overhead in size and depth); its `gen` gate is read as `0`. The index
`i ∈ [m]` enters as `p` bits, least significant first. Rows are `0`-based. -/
def DescribesRows (TQ : Transducer) (k m : ℕ) (descQ : List Bool) (s : Fin m → ℕ) : Prop :=
  ∃ G : Circuit, IsImpl TQ (setShape m descQ.length (Nat.clog 2 k)) G ∧
    ∀ i : Fin m, s i < 2 ^ Nat.clog 2 k ∧
      evalCircuit (0 : ZMod 2) G (bitsIn (ZMod 2) (numBits (Nat.clog 2 k) i.val ++ descQ)) =
        bitsIn (ZMod 2) (numBits (Nat.clog 2 k) (s i))

end DoublyEffIP.Supplement


