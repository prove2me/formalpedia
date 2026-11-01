-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_muxRot
-- name    : ShendeQSD_Synthesis_muxRot
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:41.830356+00:00
-- url     : https://prove2.me/theorems/a03ad912-36f7-4d47-91ee-d64fde610aec
-- title:
--   Multiplexed rotation (multiplexed $R_y$ or $R_z$ gate)
-- statement:
--   Let $R$ be a family of one-qubit rotations ($R_y$ or $R_z$) and let $\theta$ assign an angle $\theta_s$ to each basis state $|s\rangle$ of a select register. The **multiplexed rotation** applies $R(\theta_s)$ to a single target qubit when the select register carries $|s\rangle$, and leaves the select register unchanged:
--
--   $$
--   |t\rangle|s\rangle\longmapsto \big(R(\theta_s)|t\rangle\big)|s\rangle .
--   $$
--
--   Its matrix is block diagonal in the select register. These gates (called uniformly controlled rotations by other authors) are the non-generic building blocks of the Quantum Shannon Decomposition. The module also defines `muxRotQ`, the same gate on a $(k+1)$-qubit register with the target on the top wire and the selects on the $k$ wires below it.
--
--   **Formalization Note** In `muxRot` the index is `Bool × σ`, target first and select register `σ` second; this is the orientation of Theorems 10 and 13 (target = most significant qubit). Theorems 4 and 8 draw the target at the bottom; the operator is the same up to the order of the tensor factors. In `muxRotQ`, wire $0$ is the target and wires $1,\dots,k$ are the selects, `θ : Qubits k → ℝ`.
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §3.2, pp. 10–11 (and the multiplexor notation, p. 8)

import Definitions.Def_QAlgorithms_Defs_Basic

namespace ShendeQSD.Synthesis

open QAlgorithms

/-- **A multiplexed rotation (multiplexed `R_k` gate).**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§3.2, p. 10: "We shall call these gates multiplexed R_z (or R_y) gates, as, e.g., the rightmost
would apply a different R_z gate to the data qubit for each classical configuration of the select
bits"; p. 8: a multiplexor "preserves any bitstring state |b⟩ carried by" its select qubits.

`muxRot R θ` applies the one-qubit gate `R (θ s)` to the target qubit when the select register
carries `|s⟩`, and leaves the select register unchanged.

**Formalization Note.** The index `Bool × σ` puts the **target** (data) qubit first and the select
register `σ` second; the matrix is block diagonal in `σ`. This is the orientation of Theorems 10
and 13 (target = the top, most significant qubit). Theorems 4 and 8 draw the target at the bottom;
the operator is the same up to the order of the tensor factors. -/
def muxRot {σ : Type*} [DecidableEq σ] (R : ℝ → Matrix Bool Bool ℂ) (θ : σ → ℝ) :
    Matrix (Bool × σ) (Bool × σ) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 then R (θ p.2) p.1 q.1 else 0

/-- **The split of a `(k+1)`-qubit basis string into its top qubit and the rest.**
`splitTop y = (y 0, (y 1, …, y k))`: wire `0` (most significant) first, wires `1, …, k` after it. -/
def splitTop {k : ℕ} (y : Qubits (k + 1)) : Bool × Qubits k :=
  (y 0, Fin.tail y)

/-- **A multiplexed rotation on a `(k+1)`-qubit register.**
Shende, Bullock, Markov, arXiv:quant-ph/0406176v5, §3.2, pp. 10–11: the multiplexed `R_k` gate
with `k` select bits, as an operator on `Qubits (k+1)`.

**Formalization Note.** The target is wire `0` (most significant) and the selects are wires
`1, …, k`; `θ : Qubits k → ℝ` gives the angle for each bitstring on the selects. It is
`muxRot R θ` transported along `splitTop`. -/
def muxRotQ {k : ℕ} (R : ℝ → Matrix Bool Bool ℂ) (θ : Qubits k → ℝ) :
    Matrix (Qubits (k + 1)) (Qubits (k + 1)) ℂ :=
  (muxRot R θ).submatrix splitTop splitTop

end ShendeQSD.Synthesis


