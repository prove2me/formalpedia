-- Prove2me | Definitions.Def_TorchFire_OSS_prepCircuit
-- name    : TorchFire_OSS_prepCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:35:01.178736+00:00
-- url     : https://prove2.me/theorems/00e9bce0-1c04-489f-a8e7-4bb61dc71dbd
-- title:
--   The coset-state preparation circuit of Construction 4.6 and $\mathrm{OSS.GenQKey}$
-- statement:
--   **Construction 4.6** ([SZ25, Construction 31]): on registers $X,Y,U$ of $n,r,k$ qubits, apply $H^{\otimes n}$ to $X$, query $P$ from $X$ to $YU$, then query $P^{-1}$ from $YU$ to $X$. The module defines the circuit as a matrix, its output vector on $|0^n\rangle|0^r\rangle|0^k\rangle$, the state of $YU$, and **$\mathrm{OSS.GenQKey}^O$** of Construction 4.7 (ii): the circuit followed by a measurement of $Y$, as a classical–quantum state on (key $y$) × (signing register $U$).
--
--   Milestone M1 (Construction 4.6 and (8)) states what this circuit outputs.
--
--   **Formalization Note** The $P^{-1}$ query writes the $n$ value bits of the answer into $X$; on every input the circuit produces, $P^{-1}$ is not $\perp$.
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), Construction 4.6 p.20; Construction 4.7 (ii) p.21

import Mathlib
import Definitions.Def_TorchFire_OSS_OneSample
import Definitions.Def_TorchFire_Model_traceDist

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

open Matrix TorchFire.Model

namespace TorchFire.OSS

variable {lam : ℕ}

/-- **The coset-state preparation circuit of Construction 4.6** (Chatterjee–Mukherjee–Pathak–Podder,
*Quantum Fire with Delegated Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593, p.20,
[SZ25, Construction 31]) on registers `X, Y, U` of `n, r, k` qubits:

  `H^{⊗n}_X`, then "Query `P` from `X` to `YU`", then "Query `P⁻¹` from `YU` to `X`".

The two queries are the XOR oracle unitaries `|x, y, u⟩ ↦ |x, y ⊕ P(x)_Y, u ⊕ P(x)_U⟩` and
`|x, y, u⟩ ↦ |x ⊕ P⁻¹(y, u), y, u⟩`.

**Formalization Note** The `P⁻¹` query writes the `n` value bits of the answer into `X` (the circuit
of p.20 has an `n`-qubit `X`); on every input this circuit produces `P⁻¹` is not `⊥`, and on a `⊥`
input the value bits are zero. -/
noncomputable def prepCircuit (ω : OneSample lam) :
    Matrix (Bits (n lam) × Bits (r lam) × Bits (k lam))
      (Bits (n lam) × Bits (r lam) × Bits (k lam)) ℂ :=
  basisMat (fun s => (s.1 + (Pinv ω s.2).getD 0, s.2)) *
  basisMat (fun s => (s.1, s.2.1 + (P ω s.1).1, s.2.2 + (P ω s.1).2)) *
  hadOn (fun s : Bits (n lam) × Bits (r lam) × Bits (k lam) => (s.1, s.2))

/-- The output of the circuit on `|0^n⟩_X |0^r⟩_Y |0^k⟩_U`, as a vector. -/
noncomputable def prepOutput (ω : OneSample lam) :
    Bits (n lam) × Bits (r lam) × Bits (k lam) → ℂ :=
  (prepCircuit ω).mulVec (ket (0, 0, 0))

/-- The state of `YU` after the circuit (`X` traced out), i.e. `Tr_X` of the output. -/
noncomputable def prepYU (ω : OneSample lam) :
    Matrix (Bits (r lam) × Bits (k lam)) (Bits (r lam) × Bits (k lam)) ℂ :=
  traceOutVia (fun p : (Bits (r lam) × Bits (k lam)) × Bits (n lam) => (p.2, p.1.1, p.1.2))
    (ketbra (prepOutput ω))

/-- **`OSS.GenQKey^O`** (Construction 4.7 (ii), p.21): run Construction 4.6 and measure `Y`. The
result is the cq-state on (classical key `y`) × (signing register `R = U`): the state of `YU`
dephased in `Y`. Its block at `y` is `Pr[Y = y] · ρ_{U|Y=y}`. -/
noncomputable def genQKeyCQ (ω : OneSample lam) :
    Matrix (Bits (r lam) × Bits (k lam)) (Bits (r lam) × Bits (k lam)) ℂ :=
  Matrix.of fun p p' => if p.1 = p'.1 then prepYU ω p p' else 0

end TorchFire.OSS


