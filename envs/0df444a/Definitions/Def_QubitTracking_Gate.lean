-- Prove2me | Definitions.Def_QubitTracking_Gate
-- name    : QubitTracking_Gate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:41.133193+00:00
-- url     : https://prove2.me/theorems/f1279bdc-6a09-4777-ae87-2e363878d892
-- title:
--   Gates and circuits with superposition access to classical oracles
-- statement:
--   A **gate** on a finite set of qubit wires $\iota$ is one of:
--
--   1. an arbitrary one-qubit unitary on one wire;
--   2. an arbitrary two-qubit unitary on two distinct wires;
--   3. one **query** to a named classical oracle $\mathcal O_k:\mathbb F_2^{a}\to\mathbb F_2^{c}$, the standard unitary $|q\rangle_{\mathrm{in}}|y\rangle_{\mathrm{out}}\mapsto|q\rangle|y\oplus\mathcal O_k(q)\rangle$ on pairwise distinct input and output wires.
--
--   Each gate has a matrix in the computational basis of the wires (the gate tensored with the identity on the other wires), given an assignment of functions to the oracle names. A **circuit** is a list of gates applied in order, and its matrix is the product $M_{g_r}\cdots M_{g_1}$.
--
--   This is the common computational model of the spacetime provers, the game adversaries, the extractors and the oracle algorithms of the mission.
--
--   **Formalization Note** Every one- or two-qubit unitary counts as one gate, so a circuit over any fixed universal gate set of one- and two-qubit gates is a circuit of the same size.
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), §3.2 (p.22), §3.4 (p.24, the standard oracle StO)

import Definitions.Def_QubitTracking_Bits

set_option autoImplicit false

open Matrix

namespace QubitTracking

/-- An assignment of classical oracles to the oracle names `k : κ`: oracle `k` is a function
`𝔽₂^{inLen k} → 𝔽₂^{outLen k}`. -/
abbrev OracleAssign (κ : Type) (inLen outLen : κ → ℕ) : Type :=
  (k : κ) → Bits (Fin (inLen k)) → Bits (Fin (outLen k))

/-- A gate on qubit wires `ι` (Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through
Space and Time*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), §3.2, p.22, "a quantum circuit
… taken from some fixed universal quantum gate set", and §3.4, p.24, the standard oracle
`StO |x⟩|u⟩ = |x⟩|u + 𝒪(x)⟩`):
* `one c U`: an arbitrary one-qubit unitary `U` on wire `c`;
* `two c₁ c₂ U`: an arbitrary two-qubit unitary `U` on wires `c₁, c₂` (first, second qubit);
* `query k inp out`: one query to oracle `k`, the standard XOR unitary
  `|q⟩_{inp}|y⟩_{out} ↦ |q⟩|y ⊕ 𝒪_k(q)⟩`.

**Formalization Note** Every one- or two-qubit gate counts as one gate, so every circuit over a
fixed universal gate set of one- and two-qubit gates is a circuit of the same size here. -/
inductive Gate (ι : Type) (κ : Type) (inLen outLen : κ → ℕ) : Type
  | one (c : ι) (U : Matrix.unitaryGroup (Bits (Fin 1)) ℂ)
  | two (c₁ c₂ : ι) (U : Matrix.unitaryGroup (Bits (Fin 2)) ℂ)
  | query (k : κ) (inp : Fin (inLen k) → ι) (out : Fin (outLen k) → ι)

namespace Gate

variable {ι ι' : Type} {κ : Type} {inLen outLen : κ → ℕ}

/-- Relabel the wires of a gate along `e : ι → ι'`. -/
def map (e : ι → ι') : Gate ι κ inLen outLen → Gate ι' κ inLen outLen
  | one c U => one (e c) U
  | two c₁ c₂ U => two (e c₁) (e c₂) U
  | query k inp out => query k (e ∘ inp) (e ∘ out)

/-- The wire `c` is one of the wires the gate acts on. -/
def Touches : Gate ι κ inLen outLen → ι → Prop
  | one c' _, c => c = c'
  | two c₁ c₂ _, c => c = c₁ ∨ c = c₂
  | query _ inp out, c => (∃ j, inp j = c) ∨ (∃ j, out j = c)

/-- The gate is well formed: a two-qubit gate acts on two distinct wires, and the input and
output wires of a query are pairwise distinct. -/
def WellFormed : Gate ι κ inLen outLen → Prop
  | one _ _ => True
  | two c₁ c₂ _ => c₁ ≠ c₂
  | query _ inp out => Function.Injective (Sum.elim inp out)

/-- The gate queries oracle `k`. -/
def Queries : Gate ι κ inLen outLen → κ → Prop
  | one _ _, _ => False
  | two _ _ _, _ => False
  | query k _ _, k' => k = k'

end Gate

open Classical in
/-- The matrix, in the computational basis of the wires `ι`, of the unitary `U` on the `k` wires
`w : Fin k → ι` tensored with the identity on all other wires:
`⟨f|M|g⟩ = ⟨f∘w|U|g∘w⟩` if `f` and `g` agree off the range of `w`, and `0` otherwise. -/
noncomputable def onWires {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} (w : Fin k → ι)
    (U : Matrix (Bits (Fin k)) (Bits (Fin k)) ℂ) : Matrix (Bits ι) (Bits ι) ℂ :=
  fun f g => if (∀ i, (∀ j, w j ≠ i) → f i = g i) then U (f ∘ w) (g ∘ w) else 0

open Classical in
/-- The matrix of the standard query unitary `|q⟩_{inp}|y⟩_{out} ↦ |q⟩|y ⊕ h(q)⟩` for a classical
function `h : 𝔽₂^a → 𝔽₂^c`, on input wires `inp` and output wires `out` (identity elsewhere). -/
noncomputable def queryMat {ι : Type} [Fintype ι] [DecidableEq ι] {a c : ℕ}
    (h : Bits (Fin a) → Bits (Fin c)) (inp : Fin a → ι) (out : Fin c → ι) :
    Matrix (Bits ι) (Bits ι) ℂ :=
  fun f g => if (∀ i, (∀ j, out j ≠ i) → f i = g i) ∧ (∀ j, f (out j) = g (out j) + h (g ∘ inp) j)
    then 1 else 0

/-- Reindex the two-qubit wires `c₁, c₂` as a function `Fin 2 → ι` (`0 ↦ c₁`, `1 ↦ c₂`). -/
def pairWires {ι : Type} (c₁ c₂ : ι) : Fin 2 → ι := ![c₁, c₂]

/-- The matrix of a gate, given the oracle assignment `orc` that answers its queries. -/
noncomputable def Gate.mat {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} {inLen outLen : κ → ℕ}
    (orc : OracleAssign κ inLen outLen) : Gate ι κ inLen outLen → Matrix (Bits ι) (Bits ι) ℂ
  | .one c U => onWires (fun _ : Fin 1 => c) (U : Matrix (Bits (Fin 1)) (Bits (Fin 1)) ℂ)
  | .two c₁ c₂ U => onWires (pairWires c₁ c₂) (U : Matrix (Bits (Fin 2)) (Bits (Fin 2)) ℂ)
  | .query k inp out => queryMat (orc k) inp out

/-- The matrix of a circuit, the gates applied in list order (first gate first):
`M_{g_r} ⋯ M_{g_2} M_{g_1}`. -/
noncomputable def circMat {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} {inLen outLen : κ → ℕ}
    (orc : OracleAssign κ inLen outLen) (gs : List (Gate ι κ inLen outLen)) :
    Matrix (Bits ι) (Bits ι) ℂ :=
  gs.foldl (fun acc g => g.mat orc * acc) 1

end QubitTracking


