-- Prove2me | Definitions.Def_QiOPoQ_IsPadding
-- name    : QiOPoQ_IsPadding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:04:37.800185+00:00
-- url     : https://prove2.me/theorems/b004ec46-27dc-4335-9a47-4c87df006fff
-- title:
--   Notation 4.1: the padded circuits $C_{b,\lambda}$
-- statement:
--   With $(s,\lambda,n_{\mathrm{anc}},1)$ the shape of $V_\lambda$, a family $\{C_{b,\lambda}\}$ is a **padding** if for every $b,\lambda$:
--
--   1. $C_{b,\lambda}$ has shape $(2s+2\lambda+1,\ 1,\ \lambda+n_{\mathrm{anc}},\ 1)$;
--   2. its output qubit is its first wire;
--   3. its channel is exactly $X^b(\cdot)$;
--   4. $(b,1^\lambda)\mapsto C_{b,\lambda}$ is computable in deterministic polynomial time.
--
--   The paper leaves the padding open ("Pad $C_{b,\lambda}$ so that it has the required gate count"), so every family with these properties is allowed. The gate count is that of the circuits $D_x$ of Lemma 4.4.
--
--   **Formalization Note** The behaviour is required at the level of the channel; every circuit that applies $X^b$ to the first qubit and acts trivially elsewhere has it. Polynomial-time constructibility is what lets the challenger compute $C_{b_i,\lambda}$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 4.1, p.17; Lemma 4.4, p.18

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_diamond
import Definitions.Def_QiOPoQ_bitFlip
import Definitions.Def_QiOPoQ_encCirc

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity

variable {G : GateSet}

/-- **Notation 4.1, third bullet: the padded circuits `C_{b,λ}`.** arXiv:2609.40289,
Notation 4.1, p.17: "For b ∈ {0, 1}, define C_{b,λ} to be a circuit of shape
(2s + 2λ + 1, 1, λ + n_anc, 1), such that it applies X^b to the first input qubit and acts
trivially on the remaining input and ancilla qubits. Let the first qubit be the designated output
qubit. Pad C_{b,λ} so that it has the required gate count."

`IsPadding V Cb`: `C_{b,λ}` has shape `(2s + 2λ + 1, 1, λ + n_anc, 1)` with `(s, ·, n_anc, ·)` the
shape of `V_λ`, its output register is wire `0`, its channel is exactly `X^b(·)`, and
`(b, λ) ↦ C_{b,λ}` is computed in deterministic polynomial time from `(b, 1^λ)`.

**Formalization Note.** The padding is left open by the paper, so every padding with these
properties is allowed. The behaviour is required at the level of the channel (`chanAs … 1 1 =
X^b(·)`), which every circuit applying `X^b` to the first qubit and acting trivially elsewhere
has. Polynomial-time constructibility is required because the challenger computes `C_{b_i,λ}`
(Figure 6); Lemma 4.4 states it ("efficiently constructible by a classical PPT algorithm"). -/
def IsPadding (V : ℕ → Circ G) (Cb : Bool → ℕ → Circ G) : Prop :=
  (∀ b n, shape (Cb b n) = (2 * (V n).gates.length + 2 * n + 1, 1, n + (V n).nanc, 1)) ∧
    (∀ b n, (Cb b n).out.map Fin.val = [0]) ∧
    (∀ b n, chanAs (Cb b n) 1 1 = bitFlip b) ∧
    ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ b n, g (pair [b] (unary n)) = encCirc (Cb b n)

end QiOPoQ


