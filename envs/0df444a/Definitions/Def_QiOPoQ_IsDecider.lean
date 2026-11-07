-- Prove2me | Definitions.Def_QiOPoQ_IsDecider
-- name    : QiOPoQ_IsDecider
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:50.593102+00:00
-- url     : https://prove2.me/theorems/0a6da472-8419-4704-9e5a-626dfc12425e
-- title:
--   Notation 4.1: the uniformly generated decider circuits $V_\lambda$
-- statement:
--   A language $L$ is **decided by** the uniformly generated pseudodeterministic circuits $\{V_\lambda\}$ if
--
--   1. $V_\lambda$ has $\lambda$ input wires (the instance register);
--   2. its output register is a single ancilla wire, "an initially zero ancilla, separate from its $\lambda$-qubit instance register" (proof of Lemma 4.4);
--   3. $1^\lambda\mapsto V_\lambda$ is computable in deterministic polynomial time;
--   4. there is a negligible $\mu$ such that on every $x\in\{0,1\}^\lambda$, measuring the output gives $L(x)$ with probability at least $1-\mu(\lambda)$.
--
--   **Formalization Note** Other output qubits of an amplified circuit may be counted as junk; only $s$ and $n_{\mathrm{anc}}$ of $V_\lambda$ enter Notation 4.1. The hardness $L\notin$ i.o.P/poly is a separate hypothesis.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 4.1, p.17; proof of Lemma 4.4, p.18

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_encCirc

set_option autoImplicit false

namespace QiOPoQ

open QAdvFew.PoQOracle QAlgorithms.Complexity

variable {G : GateSet}

open Classical in
/-- **Notation 4.1, second bullet: the decider circuits `V_λ`.** Gheorghiu, Gupte, Havlíček,
Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Notation 4.1, p.17: "Let L ∈ BQP \ i.o.P/poly be a language
decided by the uniformly generated pseudodeterministic circuits {V_λ}λ∈N. That is, for every
input x ∈ {0, 1}^λ, V_λ outputs L(x) at the designated output bit with error at most negl(λ).
Let V_λ have shape (s, n_in, n_anc, n_out)." Proof of Lemma 4.4, p.18: "We choose the designated
output qubit of V_λ to be an initially zero ancilla, separate from its λ-qubit instance register;
its remaining ancillas form the workspace register."

`IsDecider G L V`: `V_λ` has the `λ` input wires of the instance register; its output register is
one ancilla wire; `λ ↦ V_λ` is generated from `1^λ` by a deterministic polynomial-time algorithm;
and for one negligible `μ`, on every `x ∈ {0,1}^λ` the measured output bit is `L(x)` with
probability at least `1 − μ(λ)`. (The hardness `L ∉ i.o.P/poly` is a separate hypothesis.)

**Formalization Note.** The output register is the designated output bit alone (the other output
qubits of an amplified circuit can be counted as junk; only `s` and `n_anc` enter Notation 4.1). -/
def IsDecider (G : GateSet) (L : Set Str) (V : ℕ → Circ G) : Prop :=
  (∀ n, (V n).nin = n) ∧ (∀ n, ∃ w, (V n).out = [w] ∧ n ≤ w.val) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n, g (unary n) = encCirc (V n)) ∧
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n (x : Str), x.length = n →
      1 - μ n ≤ runProb (V n) x [decide (x ∈ L)]

end QiOPoQ


