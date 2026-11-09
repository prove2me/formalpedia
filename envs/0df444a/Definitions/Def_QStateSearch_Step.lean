-- Prove2me | Definitions.Def_QStateSearch_Step
-- name    : QStateSearch_Step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:28.481094+00:00
-- url     : https://prove2.me/theorems/2170f501-3bd1-4c57-8c04-f35c001b0fba
-- title:
--   Steps of a classical-message verifier
-- statement:
--   A verifier is a chronological list of steps on the register $\{0,1\}\times[D]\times W$, each of one of four kinds:
--
--   1. **unitary** $U$: a private unitary gate;
--   2. **query**: one oracle-query slot; slot $s$ applies the controlled call of the oracle $O_s$ used at that slot;
--   3. **verifier message** $\{K_a\}_{a\in[m]}$: the verifier sends a classical message $a\in\{0,\dots,m-1\}$; outcome $a$ occurs and the unnormalized state is multiplied by $K_a$;
--   4. **prover message** of padded length $b$: the verifier receives a reply $z\in\{0,\dots,2^b-1\}$ and applies a unitary $U_z$ (for instance, writing $z$ into fresh workspace qubits).
--
--   Measuring an outgoing message register in the computational basis, as the paper requires, is the instrument $K_a=|a\rangle\langle a|\otimes I$; general instruments are allowed. Private measurements are deferred, so the state stays pure on each branch.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, pp.8–10

import Mathlib
import Definitions.Def_QStateSearch_Reg

namespace QStateSearch

/-- One step of a classical-message verifier on the register `Reg D W`.

* `unitary U` — a private unitary gate;
* `query` — one oracle-query slot (`controlled-O_s` for the oracle `O_s` of the slot);
* `vmsg m K` — the verifier sends a classical message `a ∈ Fin m`: outcome `a` occurs and the
  verifier's (unnormalized) state is multiplied by `K a`;
* `pmsg b U` — the verifier receives a padded `b`-bit prover message `z ∈ Fin (2 ^ b)` and
  applies the unitary `U z`.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, pp.8–10: "They exchange only classical strings. Formally, every outgoing
message register is measured … in the computational basis before it is transmitted. … For
slot t, let B_t be the sum of the padded lengths of the prover messages … Private measurements
may be deferred, while the measurements that create transmitted classical messages are kept
explicit."

**Formalization Note.** A verifier message is a general instrument `{K_a}` (one Kraus operator
per outcome, with `∑ₐ K_aᴴ K_a = 1` required in `Verifier`); measuring an outgoing register in
the computational basis is the case `K_a = |a⟩⟨a| ⊗ I`. A received message `z` is written into
the workspace by the unitary `U z` (for instance a string of X gates on fresh qubits).
Private measurements are deferred, so states are pure. Adaptivity on earlier outcomes is
carried by the quantum state (an outcome can be copied into `W` by `K a`). -/
inductive Step (D : ℕ) (W : Type) [Fintype W] [DecidableEq W] where
  | unitary (U : Matrix.unitaryGroup (Reg D W) ℂ)
  | query
  | vmsg (m : ℕ) (K : Fin m → Matrix (Reg D W) (Reg D W) ℂ)
  | pmsg (b : ℕ) (U : Fin (2 ^ b) → Matrix.unitaryGroup (Reg D W) ℂ)

end QStateSearch


