-- Prove2me | Definitions.Def_OptLocalHamSim_IsNN
-- name    : OptLocalHamSim_IsNN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:33:55.255807+00:00
-- url     : https://prove2.me/theorems/843a6ef1-679f-4443-8b12-63924650db00
-- title:
--   Nearest-neighbor circuits (one-qubit gates and adjacent CNOTs), $\iota_0$, $\mathcal T$ and $\log(2+n\mathcal T/\epsilon)$
-- statement:
--   A circuit on the wires of the lattice ($q$ data qubits and $K$ ancillas per site) is **nearest-neighbor** if every gate of every layer is either an arbitrary one-qubit unitary or a CNOT whose two wires sit at sites $x,y$ with $\mathrm{dist}(x,y)\le1$ (equal or adjacent sites). Fan-out gates and other two-qubit unitaries are not allowed. Depth counts layers of gates on disjoint wires and size counts gates (the published `ConstDepthUnitary` circuit model; the first layer acts first).
--
--   The embedding
--
--   $$
--   \iota_0|\psi\rangle:=|0\rangle_{\mathrm{anc}}|\psi\rangle
--   $$
--
--   initializes all ancillas in the all-zero state. The time count and the logarithmic scale of eq. (5) are
--
--   $$
--   \mathcal T:=\max\{1,\lceil J|T|\rceil\},\qquad \log\bigl(2+n\mathcal T/\epsilon\bigr).
--   $$
--
--   This fixes the resource model in which depth $O(\mathcal TM)$ is claimed: exact single-qubit gates, nearest-neighbor CNOTs, and a constant number of ancillas at every site.
--
--   **Formalization Note** The paper never defines "nearest-neighbor circuit" formally; this is its coarse-site model (p.12: "exact single-qubit gates and nearest-neighbor CNOTs"; p.37: "a fixed number of ancillary qubits per original site"; eq. (155): "gates between equal or adjacent coarse sites"). The module also proves that the CNOT and SWAP matrices are unitary.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §1.1, Problems 1–2, p.5; p.12; eq. (5), p.11; eq. (155), pp.51–52; §5.3, p.37

import Mathlib
import Definitions.Def_ConstDepthUnitary_Gate
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_OptLocalHamSim_Site

namespace OptLocalHamSim

/-- The CNOT matrix on two qubits `(control, target)`: `|a, b⟩ ↦ |a, b ⊕ a⟩`. -/
def cnotMat : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun x y => if x = (y.1, xor y.2 y.1) then 1 else 0

/-- The SWAP matrix on two qubits: `|a, b⟩ ↦ |b, a⟩`. -/
def swapMat : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun x y => if x = (y.2, y.1) then 1 else 0

theorem cnotMat_mem : cnotMat ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [cnotMat, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.star_apply]

theorem swapMat_mem : swapMat ∈ Matrix.unitaryGroup (Bool × Bool) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [swapMat, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.star_apply]

/-- The CNOT gate as a two-qubit unitary; the first wire of `Gate.two p q _ cnot` is the control. -/
def cnot : Matrix.unitaryGroup (Bool × Bool) ℂ := ⟨cnotMat, cnotMat_mem⟩

/-- The SWAP gate as a two-qubit unitary. -/
def swap : Matrix.unitaryGroup (Bool × Bool) ℂ := ⟨swapMat, swapMat_mem⟩

variable {D : ℕ} {L : Fin D → ℕ} {q K : ℕ}

/-- A gate of the **nearest-neighbor** model on the lattice wires: an arbitrary one-qubit unitary, or a
CNOT between two wires at equal or adjacent sites (ℓ¹ site distance at most one). Fan-out gates and
other two-qubit unitaries are excluded.

Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission, held version, sha256 44a9768a…: p.12 ("The resource
bounds use exact single-qubit gates and nearest-neighbor CNOTs"), p.37 ("A fixed number of ancillary
qubits per original site suffices"), and eq. (155), p.51–52 ("gates between equal or adjacent coarse
sites have constant physical range"). -/
def IsNNGate : ConstDepthUnitary.Gate (Wire L q K) → Prop
  | .one _ _ => True
  | .two p p' _ u => u = cnot ∧ l1dist (wireSite p) (wireSite p') ≤ 1
  | .fanout _ _ _ _ => False

/-- A **nearest-neighbor circuit** on the wires `Wire L q K` (`q` data qubits and `K` ancillas at every
site): every gate of every layer is a one-qubit unitary or a CNOT between wires at sites of ℓ¹ distance
at most one.

**Formalization Note** The paper never defines "nearest-neighbor circuit" formally. This is its
coarse-site model: one-qubit gates and adjacent CNOTs, a fixed number `K` of ancillas per site
(p.37), and gates between equal or adjacent (coarse) sites (eq. (155)). The circuit model is the
published `ConstDepthUnitary.Circuit`: the head layer acts first, depth is the number of layers,
size is the number of gates. -/
def IsNN (C : ConstDepthUnitary.Circuit (Wire L q K)) : Prop :=
  ∀ l ∈ C, ∀ g ∈ l.gates, IsNNGate g

/-- The embedding `ι₀|ψ⟩ := |0⟩_anc|ψ⟩` that initializes all ancillary qubits in the all-zero state
(Problem 1, p.5), as a matrix from data basis states to wire basis states. -/
def iota0 : Matrix (Wire L q K → Bool) (Dat L q → Bool) ℂ :=
  Matrix.of fun w d => if (∀ x, w (Sum.inl x) = d x) ∧ (∀ a, w (Sum.inr a) = false) then 1 else 0

/-- The time count `𝒯 := max{1, ⌈J|T|⌉}`, eq. (5), p.11. -/
noncomputable def timeCount (J T : ℝ) : ℕ := max 1 ⌈J * |T|⌉₊

/-- The logarithmic scale `log(2 + n𝒯/ϵ)` of eq. (5), p.11, without the constant `c₀`. -/
noncomputable def logScale (n 𝒯 : ℕ) (ε : ℝ) : ℝ := Real.log (2 + (n : ℝ) * 𝒯 / ε)

end OptLocalHamSim


