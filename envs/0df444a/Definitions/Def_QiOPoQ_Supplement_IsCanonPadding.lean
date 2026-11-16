-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsCanonPadding
-- name    : QiOPoQ_Supplement_IsCanonPadding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:51:15.520635+00:00
-- url     : https://prove2.me/theorems/0fc5fd6f-09d5-4422-bc25-5a6ce80dd98c
-- title:
--   Notation 5.1: canonical padded circuits $X_b$
-- statement:
--   A padding $X_b$ assigns to each bit $b$ and each shape a circuit, so that $X_b$ depends on $b$ and $\mathrm{shape}(C)$ alone. It is admissible if for every shape $(s,1,a,1)$ the circuit $X_b$ has shape $(s+1,1,a,1)$, the gate count of $X\circ C$ and $I\circ C$, and implements exactly the channel $X^b(\cdot)$; and if $(b,\mathrm{shape})\mapsto X_b$ is computable in deterministic polynomial time.
--
--   **Formalization Note** The paper leaves the padding open, so the theorems hold for every admissible padding.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 5.1, p.22

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_bitFlip
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_Supplement_encShape

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

variable {G : GateSet}

/-- **Notation 5.1, third bullet: the padded circuits `X_b`.** Gheorghiu, Gupte, Havlíček, Liu,
*Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289
(sha256 fe2f9210…), Notation 5.1, p.22: "For b ∈ {0, 1}, let X_b be a circuit implementing the
channel X^b(·), with the same number of input, ancilla, and output wires as C. Further, let X_b be
padded to have the same gate count as X ∘ C and I ∘ C. Choose the descriptions and padding of X_b
canonically from b and this common shape alone."

`Xp b sh` is `X_b` for a circuit `C` of shape `sh = shape(C)`. For every shape `(s, 1, a, 1)` (the
shapes of `C_BQP` circuits) `X_b` has shape `(s + 1, 1, a, 1)` and channel exactly `X^b(·)`; and
`(b, sh) ↦ X_b` is computed in deterministic polynomial time.

**Formalization Note.** The padding is left open by the paper, so every padding with these
properties is allowed (the theorems quantify over all of them). "Canonically from b and the common
shape alone" is that `X_b` is a function of `(b, shape(C))`. -/
def IsCanonPadding (Xp : Bool → ℕ × ℕ × ℕ × ℕ → Circ G) : Prop :=
  (∀ b s a, shape (Xp b (s, 1, a, 1)) = (s + 1, 1, a, 1)) ∧
    (∀ b s a, chanAs (Xp b (s, 1, a, 1)) 1 1 = bitFlip b) ∧
    ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ b sh, g (pair [b] (encShape sh)) = encCirc (Xp b sh)

end QiOPoQ.Supplement


