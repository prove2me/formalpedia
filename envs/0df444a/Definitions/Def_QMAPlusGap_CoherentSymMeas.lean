-- Prove2me | Definitions.Def_QMAPlusGap_CoherentSymMeas
-- name    : QMAPlusGap_CoherentSymMeas
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:23.230067+00:00
-- url     : https://prove2.me/theorems/388c4f62-ef0b-457d-93d0-54e38d2ee789
-- title:
--   Circuits implementing $\{P^{(R)}_{\mathrm{sym}},I-P^{(R)}_{\mathrm{sym}}\}$ to accuracy $2^{-t}$
-- statement:
--   Let $\mathcal H=(\mathbb C^2)^{\otimes q}$ and consider a layered circuit $U$ over the gate set H, S, T, X, CNOT on $Rq$ data wires (the $R$ registers of $\mathcal H^{\otimes R}$), $a$ ancilla wires and one final flag wire. The circuit **implements the symmetric-subspace measurement to accuracy $2^{-t}$** if for every $\varphi\in\mathcal H^{\otimes R}$
--   $$
--   \Big\|U\big(\varphi\otimes|0^a\rangle\otimes|0\rangle\big)-\Big(P^{(R)}_{\mathrm{sym}}\varphi\otimes|0^a\rangle\otimes|1\rangle+\big(I-P^{(R)}_{\mathrm{sym}}\big)\varphi\otimes|0^a\rangle\otimes|0\rangle\Big)\Big\|\le2^{-t}\|\varphi\| .
--   $$
--   Reading the flag wire then performs $\{P^{(R)}_{\mathrm{sym}},I-P^{(R)}_{\mathrm{sym}}\}$ up to error $2^{-t}$ and leaves the post-measurement state on the data wires.
--
--   **Formalization Note** Register $r$, qubit $j$ is data wire $rq+j$; the circuit semantics is the published `ShiShallow.runLayered`; norms are Euclidean.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), §4.5, p.25

import Mathlib
import Definitions.Def_ShiShallow_Core
import Definitions.Def_QMAPlusGap_symProj
import Definitions.Def_ArgmaxDeFinetti_vnorm

set_option autoImplicit false

open Matrix

namespace QMAPlusGap

/-- The data block of a basis string of `R·q + (a + 1)` wires, read as `R` registers of `q` qubits: register
`r`, qubit `j` is wire `r·q + j` (via `finProdFinEquiv`). -/
def dataRegs {R q a : ℕ} (y : ShiShallow.Bits (R * q + (a + 1))) : Fin R → ShiShallow.Bits q :=
  fun r j => y (Fin.castAdd (a + 1) (finProdFinEquiv (r, j)))

/-- The input `φ ⊗ |0^a⟩ ⊗ |0⟩`: a vector `φ` of `H^{⊗R}` (`H = (ℂ²)^{⊗q}`) on the data wires, all `a` ancillas
and the final flag wire in `|0⟩`. -/
def symMeasInput {R q a : ℕ} (φ : (Fin R → ShiShallow.Bits q) → ℂ) :
    ShiShallow.QState (R * q + (a + 1)) :=
  fun y => if ∀ l : Fin (a + 1), y (Fin.natAdd (R * q) l) = false then φ (dataRegs y) else 0

/-- The ideal output `(P φ) ⊗ |0^a⟩ ⊗ |1⟩ + ((I − P) φ) ⊗ |0^a⟩ ⊗ |0⟩` with `P = P_sym^{(R)}`: the coherent
two-outcome measurement `{P_sym^{(R)}, I − P_sym^{(R)}}` with its outcome on the flag (last) wire. -/
noncomputable def symMeasTarget {R q a : ℕ} (φ : (Fin R → ShiShallow.Bits q) → ℂ) :
    ShiShallow.QState (R * q + (a + 1)) :=
  fun y =>
    if ∀ l : Fin a, y (Fin.natAdd (R * q) (Fin.castSucc l)) = false then
      (if y (Fin.natAdd (R * q) (Fin.last a)) then (symProj R *ᵥ φ) (dataRegs y)
        else ((1 - symProj R) *ᵥ φ) (dataRegs y))
    else 0

/-- A layered circuit `c` on `R·q` data wires, `a` ancillas and one flag wire **implements the
symmetric-subspace measurement `{P_sym^{(R)}, I − P_sym^{(R)}}` to accuracy `2^{−t}`**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), §4.5, p.25: for
every vector `φ` of `H^{⊗R}`, `∥c(φ ⊗ |0^a⟩|0⟩) − (Pφ ⊗ |0^a⟩|1⟩ + (I−P)φ ⊗ |0^a⟩|0⟩)∥ ≤ 2^{−t} ∥φ∥`
(Euclidean norms). Reading the flag wire then performs the measurement up to error `2^{−t}` and leaves the
post-measurement state on the data wires. -/
def CoherentSymMeas (R q t a : ℕ) (c : ShiShallow.Layered (R * q + (a + 1))) : Prop :=
  ∀ φ : (Fin R → ShiShallow.Bits q) → ℂ,
    ArgmaxDeFinetti.vnorm (ShiShallow.runLayered c (symMeasInput φ) - symMeasTarget φ) ≤ (1 / 2 : ℝ) ^ t * ArgmaxDeFinetti.vnorm φ

end QMAPlusGap


