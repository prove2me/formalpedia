-- Prove2me | Definitions.Def_WildeQIT_QErasure_QCode
-- name    : WildeQIT_QErasure_QCode
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:20.891971+00:00
-- url     : https://prove2.me/theorems/9358fe37-0f9a-4768-b444-e67a56660f48
-- title:
--   Quantum communication code (encoder and decoder)
-- statement:
--   A **quantum communication code** of block length $n$ for a channel $\mathcal N_{A'\to B}$ consists of
--
--   1. an encoding channel $\mathcal E_{A_1\to A'^n}$ from Alice's system $A_1$ to the $n$ channel inputs, and
--   2. a decoding channel $\mathcal D_{B^n\to B_1}$ from the $n$ channel outputs to a system $B_1$ of the same dimension as $A_1$.
--
--   The reference system $R$ with which Alice's system is entangled also has the dimension of $A_1$.
--
--   **Formalization Note** $A_1$, $B_1$ and $R$ are indexed by `Fin m` with $m=\dim\mathcal H_{A_1}$; channel inputs and outputs by `Fin n → a` and `Fin n → b`. Both maps are published `WildeQIT.QChannel`s.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.1, (24.1) and Figure 24.1, pp. 658–659

import Definitions.Def_WildeQIT_QChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.1, pp. 658–659, (24.1)
and Figure 24.1 (a quantum communication code for entanglement transmission).
-/

namespace WildeQIT.QErasure

/-- **Quantum communication code** of block length `n` for a channel `N_{A′→B}` (Wilde, *From
Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.1, pp. 658–659): an encoder
`E_{A₁→A′ⁿ}` from Alice's system `A₁` to the `n` channel inputs, and a decoding channel
`D_{Bⁿ→B₁}` from the `n` channel outputs to a system `B₁` "of the same dimension as `A₁`".

**Formalization Note.** `A₁` and `B₁` (and the reference `R`, which has the same dimension as `A₁`)
are indexed by `Fin m`, where `m = dim H_{A₁}`. The `n` channel inputs `A′ⁿ` are indexed by
`Fin n → a` and the outputs `Bⁿ` by `Fin n → b`. Encoder and decoder are arbitrary quantum channels,
in the published Kraus form `WildeQIT.QChannel`. -/
structure QCode (a b : Type) [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (n m : ℕ) where
  /-- The encoder `E_{A₁→A′ⁿ}`. -/
  enc : QChannel (Fin m) (Fin n → a)
  /-- The decoder `D_{Bⁿ→B₁}`. -/
  dec : QChannel (Fin n → b) (Fin m)

end WildeQIT.QErasure


