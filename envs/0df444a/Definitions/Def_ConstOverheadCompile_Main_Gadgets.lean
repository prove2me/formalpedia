-- Prove2me | Definitions.Def_ConstOverheadCompile_Main_Gadgets
-- name    : ConstOverheadCompile_Main_Gadgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:24.349724+00:00
-- url     : https://prove2.me/theorems/778f7900-6d5e-439d-a335-1f9c97557e74
-- title:
--   The state-injection and phase-halving gadgets of Figure 1
-- statement:
--   Write $|+\rangle=(|0\rangle+|1\rangle)/\sqrt2$, so that the **resource state** is $R(\theta)|+\rangle=(|0\rangle+e^{i\theta}|1\rangle)/\sqrt2$.
--
--   1. The **state-injection gadget** for angle $\theta$ acts on two wires: wire $0$ carries the data $|\psi\rangle$ and wire $1$ the resource $R(\theta)|+\rangle$. It applies CNOT with control wire $0$ and target wire $1$, measures wire $1$ in the computational basis, and, only on outcome $1$, applies $R(2\theta)$ to wire $0$. It is an adaptive circuit over $\mathcal G\cup\{R(2\theta)\}$.
--   2. The **phase-halving gadget** for angle $\theta$ is the unitary circuit on four wires, $0$ = catalyst $R(\theta)|+\rangle$, $1=|\psi\rangle$, $2=|\phi\rangle$, $3$ = ancilla $|0\rangle$, with gates in time order ($a\to b$ means control $a$, target $b$):
--   $$\mathrm{CNOT}(1\to0),\ \mathrm{CNOT}(2\to0),\ \mathrm{CNOT}(0\to1),\ \mathrm{CNOT}(0\to2),\ \mathrm{Tof}(1,2\to3),\ \mathrm{CNOT}(0\to3),\ R(2\theta)_3,\ \mathrm{CNOT}(0\to3),\ \mathrm{Tof}(1,2\to3),\ \mathrm{CNOT}(0\to2),\ \mathrm{CNOT}(0\to1).$$
--   It is a circuit over $\mathcal G\cup\{\mathrm{Toffoli},R(2\theta)\}$.
--
--   The two gadgets are the building blocks of the paper's compilation algorithm: injection consumes a resource state to apply $R(\theta)$, and phase halving uses one $R(2\theta)$ and a catalyst to apply $R(\theta)$ twice.
--
--   **Formalization Note** Product vectors $u\otimes v$ and $u_0\otimes u_1\otimes u_2\otimes u_3$ are functions on bit strings, wire $0$ first. The gate list was read off the rendered Figure 1 (p.6) and agrees with the case analysis of Appendix B.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.6 Figure 1 and Eqs. (12)–(13); pp.17–18 Appendix B

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_AdaptiveCircuit

namespace ConstOverheadCompile.Main

open QAlgorithms

/-! ### Vectors on one and on several qubits -/

/-- The computational basis vector `|b⟩` of one qubit. -/
def basisVec (b : Bool) : Bool → ℂ := fun a => if a = b then 1 else 0

/-- The state `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def plusVec : Bool → ℂ := fun _ => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The resource state `R(θ)|+⟩ = (|0⟩ + e^{iθ}|1⟩)/√2` (p.6). -/
noncomputable def resourceVec (θ : ℝ) : Bool → ℂ := (rot θ).mulVec plusVec

/-- The product vector `u ⊗ v` on two qubits (wire 0 carries `u`). -/
def vec2 (u v : Bool → ℂ) : Qubits 2 → ℂ := fun x => u (x 0) * v (x 1)

/-- The product vector `u₀ ⊗ u₁ ⊗ u₂ ⊗ u₃` on four qubits (wire `i` carries `uᵢ`). -/
def vec4 (u₀ u₁ u₂ u₃ : Bool → ℂ) : Qubits 4 → ℂ :=
  fun x => u₀ (x 0) * u₁ (x 1) * u₂ (x 2) * u₃ (x 3)

/-! ### Gate applications on chosen wires -/

/-- A single-qubit gate `M` of the gate set `S` placed on wire `q`. -/
def app1 {S : Set Gate} {n : ℕ} (M : Matrix Bool Bool ℂ) (h : Gate.ofMatrix1 M ∈ S)
    (q : Fin n) : GateApp S n :=
  ⟨Gate.ofMatrix1 M, h, (⟨fun _ => q, fun i j _ => Subsingleton.elim i j⟩ : Fin 1 ↪ Fin n)⟩

/-- CNOT (in the gate set `S`) with control on wire `a` and target on wire `t ≠ a`. -/
def cnotApp {S : Set Gate} {n : ℕ} (h : Gate.ofMatrix2 cnot ∈ S) (a t : Fin n)
    (hat : a ≠ t) : GateApp S n :=
  ⟨Gate.ofMatrix2 cnot, h, (⟨![a, t], by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd hij hat
    · exact absurd hij.symm hat
    · rfl⟩ : Fin 2 ↪ Fin n)⟩

/-- Toffoli (in the gate set `S`) with controls on wires `a`, `b` and target on wire `t`. -/
def toffoliApp {S : Set Gate} {n : ℕ} (h : toffoli ∈ S) (w : Fin 3 ↪ Fin n) : GateApp S n :=
  ⟨toffoli, h, w⟩

/-! ### The state-injection gadget (Figure 1, left) -/

/-- The gates available to the state-injection gadget for angle `θ`: `𝒢` and the correction
`R(2θ)`. -/
def injectionGates (θ : ℝ) : Set Gate := CliffordT ∪ {Gate.ofMatrix1 (rot (2 * θ))}

/-- Figure 1 (left), p.6: wire 0 carries the data `|ψ⟩`, wire 1 the resource `R(θ)|+⟩`.
Apply CNOT (control wire 0, target wire 1), measure wire 1 in the computational basis, and on
outcome 1 apply `R(2θ)` to wire 0. -/
noncomputable def injectionGadget (θ : ℝ) : AdaptiveCircuit (injectionGates θ) 2 :=
  .gate (cnotApp (Or.inl (by simp [CliffordT])) 0 1 (by decide))
    (.measure 1 fun b =>
      match b with
      | false => .done
      | true => .gate (app1 (rot (2 * θ)) (Or.inr rfl) 0) .done)

/-! ### The phase-halving gadget (Figure 1, right) -/

/-- The gates available to the phase-halving gadget for angle `θ`: `𝒢`, Toffoli and `R(2θ)`. -/
def halvingGates (θ : ℝ) : Set Gate := CliffordT ∪ {toffoli, Gate.ofMatrix1 (rot (2 * θ))}

private theorem cnot_mem_halving (θ : ℝ) : Gate.ofMatrix2 cnot ∈ halvingGates θ :=
  Or.inl (by simp [CliffordT])

private theorem toffoli_mem_halving (θ : ℝ) : toffoli ∈ halvingGates θ :=
  Or.inr (Set.mem_insert _ _)

private theorem rot_mem_halving (θ : ℝ) : Gate.ofMatrix1 (rot (2 * θ)) ∈ halvingGates θ :=
  Or.inr (Set.mem_insert_of_mem _ rfl)

/-- The Toffoli wires `(1, 2 → 3)` of the phase-halving gadget. -/
def toffoliWires : Fin 3 ↪ Fin 4 := ⟨![1, 2, 3], by decide⟩

/-- Figure 1 (right), p.6, and Appendix B, pp.17–18: the phase-halving circuit on four wires,
0 = catalyst `R(θ)|+⟩`, 1 = `|ψ⟩`, 2 = `|φ⟩`, 3 = ancilla `|0⟩`. In time order (`a → b` is
control `a`, target `b`): CNOT(1→0), CNOT(2→0), CNOT(0→1), CNOT(0→2), Toffoli(1,2→3),
CNOT(0→3), `R(2θ)` on wire 3, CNOT(0→3), Toffoli(1,2→3), CNOT(0→2), CNOT(0→1). -/
noncomputable def phaseHalving (θ : ℝ) : Circuit (halvingGates θ) 4 :=
  [cnotApp (cnot_mem_halving θ) 1 0 (by decide),
   cnotApp (cnot_mem_halving θ) 2 0 (by decide),
   cnotApp (cnot_mem_halving θ) 0 1 (by decide),
   cnotApp (cnot_mem_halving θ) 0 2 (by decide),
   toffoliApp (toffoli_mem_halving θ) toffoliWires,
   cnotApp (cnot_mem_halving θ) 0 3 (by decide),
   app1 (rot (2 * θ)) (rot_mem_halving θ) 3,
   cnotApp (cnot_mem_halving θ) 0 3 (by decide),
   toffoliApp (toffoli_mem_halving θ) toffoliWires,
   cnotApp (cnot_mem_halving θ) 0 2 (by decide),
   cnotApp (cnot_mem_halving θ) 0 1 (by decide)]

end ConstOverheadCompile.Main


