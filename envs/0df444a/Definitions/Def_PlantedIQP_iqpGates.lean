-- Prove2me | Definitions.Def_PlantedIQP_iqpGates
-- name    : PlantedIQP_iqpGates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:38.257425+00:00
-- url     : https://prove2.me/theorems/354b659b-4486-4071-8bb4-e86a67643af3
-- title:
--   The IQP gate set $\{H,Z,CZ,CCZ\}$ and circuits written by a classical program
-- statement:
--   Degree-3 IQP circuits are built from Hadamard gates and the diagonal gates $Z$, $CZ$ and $CCZ$ acting on the qubits named by the coefficients $F_i$, $F_{ij}$, $F_{ijk}$. The **IQP gate set** is $\{H,Z,CZ,CCZ\}$ with $CCZ=\mathrm{diag}(1,\dots,1,-1)$ on three qubits.
--
--   A circuit written by a classical program is read from its output words: the number of gates, then for each gate a code ($0=H$, $1=Z$, $2=CZ$, $3=CCZ$) and its wires. A measured bit string $z\in\{0,1\}^n$ is identified with the vector of $\mathbb F_2^n$ with the same bits.
--
--   **Formalization Note** Circuits, gates, $H$, $Z$, controlled gates, states and measurement probabilities are the published `QAlgorithms` layer; only $CCZ$ is local.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Section 3.1, p.19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_PlantedIQP_CubicPoly

set_option autoImplicit false

namespace PlantedIQP

/-!
# The IQP gate set `{H, Z, CZ, CCZ}` and circuits written out by a classical program

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Section 3.1, p.19: "Degree-3 IQP circuits are
therefore diagonal quantum circuits composed of Z, CZ, and CCZ gates acting on the qubits specified
in the coefficients F_i, F_ij, and F_ijk, respectively. Applying an IQP circuit C_f to an initial
|+ⁿ⟩ state yields the polynomial phase state […] The amplitudes of |f⟩ in the Hadamard basis
a_f(x) := ⟨x| H^{⊗n} |f⟩".

**Formalization Note.**
* Circuits, gates, `embedOp`, `hadamard`, `pauliZ`, `controlled`, `ket`, `act`, `prob` are the
  published `QAlgorithms` layer (`QAlgorithms_Defs_Basic`, `_Gates`, `_Circuit`). The gate set has
  the four gates `H`, `Z`, `CZ = controlled Z` and `CCZ = diag(1, …, 1, −1)` on three qubits
  (`cczGate`, local).
* Registers are `Qubits n = Fin n → Bool`; wire `i` carries coordinate `i` of 𝔽₂ⁿ, and
  `bitsToVec` is the bridge `Bool → ZMod 2`.
* A gate list written by a classical program is read from its output words `out` (cell contents as
  natural numbers): `out 0` is the number of gates; gate `k` occupies cells `2 + 4k, …, 2 + 4k + 3`,
  holding the gate's code (`0 = H`, `1 = Z`, `2 = CZ`, `3 = CCZ`) and its wires in gate order.
-/

open QAlgorithms

/-- The controlled-controlled-`Z` gate on three qubits: phase `−1` on `|111⟩`. -/
noncomputable def cczGate : Gate :=
  ⟨3, Matrix.diagonal fun b => if b 0 && b 1 && b 2 then -1 else 1⟩

/-- The four IQP gates by code: `0 ↦ H`, `1 ↦ Z`, `2 ↦ CZ`, `3 ↦ CCZ`. -/
noncomputable def iqpGate : Fin 4 → Gate
  | 0 => Gate.ofMatrix1 hadamard
  | 1 => Gate.ofMatrix1 pauliZ
  | 2 => Gate.ofMatrix2 (controlled pauliZ)
  | 3 => cczGate

/-- The gate set `{H, Z, CZ, CCZ}`. -/
def iqpGates : Set Gate := Set.range iqpGate

/-- The words `out` written by a classical program encode the circuit `c`: `out 0` is its length,
and gate `k` has its code at `out (2 + 4k)` and its wires at `out (2 + 4k + 1 + a)`. -/
def EncodesCircuit {n : ℕ} (out : ℕ → ℕ) (c : Circuit iqpGates n) : Prop :=
  out 0 = c.length ∧
    ∀ (k : ℕ) (hk : k < c.length), ∃ t : Fin 4,
      out (2 + 4 * k) = t ∧ (c.get ⟨k, hk⟩).gate = iqpGate t ∧
        ∀ a : Fin (c.get ⟨k, hk⟩).gate.arity,
          (((c.get ⟨k, hk⟩).wires a : Fin n) : ℕ) = out (2 + 4 * k + 1 + a)

/-- The bridge from a measured bit string to a vector of 𝔽₂ⁿ. -/
def bitsToVec {n : ℕ} (z : Qubits n) : Vec n := fun i => if z i then 1 else 0

end PlantedIQP


