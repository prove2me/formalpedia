-- Prove2me | Definitions.Def_QMAvsQCIP_QQVerifier
-- name    : QMAvsQCIP_QQVerifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:47.223193+00:00
-- url     : https://prove2.me/theorems/d3cdd153-c949-41d7-9ff6-d29da14a983c
-- title:
--   Quantum query verifier with classical messages (QCIP$^{\mathrm{bb}}$)
-- statement:
--   A **quantum query verifier exchanging classical messages** with finite oracle domain $Z$ has a private register $Z\times\{0,1\}\times[d]$ (query input, answer qubit, a workspace of any finite dimension $d$) starting in a fixed basis state, and runs $R$ rounds of $\ell$-bit messages each way. In round $j\le R$ it
--
--   1. applies (for $j\ge1$) a unitary determined by the prover's last reply;
--   2. applies a list of operations, each an arbitrary unitary or one oracle query $U_O|z,o,w\rangle=|z,o\oplus O(z),w\rangle$;
--   3. measures (for $j<R$) its outgoing message, or (for $j=R$) its decision, in the computational basis.
--
--   Local computation and workspace are unrestricted; only rounds, messages and queries are counted.
--
--   **Formalization Note** The initial basis state plays the role of $|0\rangle$. A received message acts as a message-controlled unitary (XOR into fresh qubits is a special case); an outgoing message is a function of the computational basis label (measuring a sub-register is a special case). Rounds and message lengths are fixed by padding, so the total communication including the decision is $2R\ell+1$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Definitions 3 and 5, pp.16–17; Section 3.1, p.14

import Mathlib

set_option autoImplicit false

namespace QMAvsQCIP

/-- A **quantum query verifier exchanging classical messages** (one member `V_λ` of a QCIP^bb
verifier family) with oracle domain `Z` (finite). Its private register is
`Z × {0,1} × [d]`: the query input register, the answer qubit, and a workspace of any finite
dimension `d`; it starts in the basis state `init`. The interaction has `R` rounds of `ℓ`-bit
messages each way. In round `j ≤ R` the verifier first (for `j ≥ 1`) applies the unitary
`recv (j−1) b` determined by the prover's last reply `b`, then the operations `ops j` in order —
`some U` an arbitrary unitary, `none` one oracle query
`U_O |z, o, w⟩ = |z, o ⊕ O(z), w⟩` — and finally (for `j < R`) measures its outgoing message
`a_j = sendOf r` in the computational basis, or (for `j = R`) measures the decision
`decOf r`. Acceptance is `qqAccept`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Definition 3, p.16 (PDF p.19): "A query algorithm is a family (A_λ)_{λ≥1}
of finite classical or quantum oracle circuits, with no uniformity or size requirement … its
local computation and workspace may be arbitrarily large but finite. For each λ, the circuit
description is fixed for all input oracles O : Z_λ → {0,1}. A quantum query verifier may query O
in superposition and starts with private workspace in |0⟩, independently of the witness or
prover"; Definition 5, p.17 (PDF p.20): "On every input oracle and against every prover, V_λ
makes at most T(λ) oracle queries, and the parties exchange at most c(λ) classical bits over at
most r(λ) rounds. Both parties may keep private quantum memory but start uncorrelated";
Section 3.1, p.14: "we purify each party's local computation while measuring outgoing messages".

**Formalization Note.** Local computation is unrestricted: any unitaries on the register. The
initial basis state `init` plays the role of `|0⟩` (any basis state is mapped to it by a
permutation). A received message is applied as a message-controlled unitary (XOR into fresh
qubits is a special case); an outgoing message, and the decision, is the computational-basis
measurement of a function of the basis label (measuring a message sub-register is a special
case). Rounds and message lengths are fixed by padding (p.14); the total communication counted
with the decision is `2Rℓ + 1`. Queries: `qqQueries`. -/
structure QQVerifier (Z : Type) [Fintype Z] [DecidableEq Z] where
  /-- workspace dimension -/
  d : ℕ
  /-- number of rounds -/
  R : ℕ
  /-- message length (both directions) -/
  ℓ : ℕ
  /-- the initial basis state -/
  init : Z × Bool × Fin d
  /-- the unitary applied on receiving prover reply number `j` -/
  recv : Fin R → (Fin ℓ → Bool) → Matrix.unitaryGroup (Z × Bool × Fin d) ℂ
  /-- the operations of round `j`: `some U` a unitary, `none` an oracle query -/
  ops : Fin (R + 1) → List (Option (Matrix.unitaryGroup (Z × Bool × Fin d) ℂ))
  /-- the outgoing message read off a basis state -/
  sendOf : Z × Bool × Fin d → Fin ℓ → Bool
  /-- the decision read off a basis state -/
  decOf : Z × Bool × Fin d → Bool

end QMAvsQCIP


