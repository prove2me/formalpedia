-- Prove2me | Definitions.Def_ICSCompute_QCirc
-- name    : ICSCompute_QCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:46:34.898648+00:00
-- url     : https://prove2.me/theorems/d7f74dce-bd26-4f77-b103-5fa709e5999f
-- title:
--   Quantum circuits over $\{H,T,T^\dagger,\mathrm{CNOT},\mathrm{SWAP},\mathrm{Tof}\}$, their channels, matrices and unitarity
-- statement:
--   An **$n_{\mathrm{in}}$-to-$n_{\mathrm{out}}$ quantum circuit** acts on its $n_{\mathrm{in}}$ input qubits together with ancilla qubits initialized to $|0\rangle$, applies a sequence of gates from the fixed gate set $\{H, T, T^\dagger\}\cup\{\mathrm{CNOT},\mathrm{SWAP}\}\cup\{\mathrm{Tof}\}$, and outputs its first $n_{\mathrm{out}}$ wires, discarding the rest. With $G$ the product of its gates, the **channel** it implements is
--   $$\mathcal C_C(\rho) = \operatorname{Tr}_{\text{discarded}}\big(G(\rho\otimes|0^{a}\rangle\langle 0^{a}|)G^\dagger\big).$$
--   For $n$-to-$n$ circuits the **matrix** of $C$ is the work-$|0\rangle$ block $U_C(y,x) = \langle y,0^a|G|x,0^a\rangle$, and $C$ is a **unitary circuit** if $U_C$ is unitary: then the work registers are returned to $|0\rangle$ on every input and $C(|\psi\rangle\langle\psi|) = U_C|\psi\rangle\langle\psi|U_C^\dagger$. The size of $C$ is its number of gates plus its number of wires.
--
--   **Formalization Note** Circuits are in normal form: measurement and classical control are deferred to gates on fresh ancillas, which leaves the channel unchanged and changes the size by a constant factor. The gate list is the published `QAlgorithms.Circuit` over the local `gateSet`; `qubitMat` is the $2\times2$ matrix of a one-qubit circuit. The matrix, not only the channel, is fixed, because the phases of the $U_{i,a}$ matter (App. A, p.42).
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), §3, circuit conventions, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_ICSCompute_splitQ

namespace ICSCompute

open QAlgorithms

/-- The Toffoli gate `|a, b, c⟩ ↦ |a, b, c ⊕ (a ∧ b)⟩` on three qubits (controls = wires 0, 1). -/
def toffoli : Matrix (Qubits 3) (Qubits 3) ℂ :=
  Matrix.of fun y z => if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then 1 else 0

/-- The Hadamard gate `H` as an arity-1 gate. -/
noncomputable def gateH : Gate := Gate.ofMatrix1 hadamard
/-- The gate `T = diag(1, e^{iπ/4})` as an arity-1 gate. -/
noncomputable def gateTT : Gate := Gate.ofMatrix1 gateT
/-- The gate `T†`, the adjoint of `T`, as an arity-1 gate. -/
noncomputable def gateTdg : Gate := Gate.ofMatrix1 (Matrix.conjTranspose gateT)
/-- The CNOT gate (control = gate wire 0) as an arity-2 gate. -/
def gateCNOT : Gate := Gate.ofMatrix2 cnot
/-- The SWAP gate as an arity-2 gate. -/
def gateSWAP : Gate := Gate.ofMatrix2 swapGate
/-- The Toffoli gate as an arity-3 gate. -/
def gateTof : Gate := ⟨3, toffoli⟩

/-- The paper's fixed gate set `{H, T, T†} ∪ {CNOT, SWAP} ∪ {Tof}` (§3, p.14 (PDF p.16)). -/
noncomputable def gateSet : Set Gate := {gateH, gateTT, gateTdg, gateCNOT, gateSWAP, gateTof}

/-- `ρ ⊗ |0ᵏ⟩⟨0ᵏ|` on `S(m + k)`: `k` ancilla qubits in `|0⟩` appended after the `m` qubits of
`ρ` (§3, p.14; Lemma 4.1, p.20). -/
def padZero {m : ℕ} (k : ℕ) (ρ : Matrix (Qubits m) (Qubits m) ℂ) :
    Matrix (Qubits (m + k)) (Qubits (m + k)) ℂ :=
  Matrix.reindex (splitQ m k).symm (splitQ m k).symm
    (Matrix.kronecker ρ (Matrix.single (fun _ : Fin k => false) (fun _ : Fin k => false) 1))

theorem padZero_add {m : ℕ} (k : ℕ) (ρ σ : Matrix (Qubits m) (Qubits m) ℂ) :
    padZero k (ρ + σ) = padZero k ρ + padZero k σ := by
  ext x y
  simp [padZero, Matrix.add_kronecker]

theorem padZero_smul {m : ℕ} (k : ℕ) (c : ℂ) (ρ : Matrix (Qubits m) (Qubits m) ℂ) :
    padZero k (c • ρ) = c • padZero k ρ := by
  ext x y
  simp [padZero, Matrix.smul_kronecker]

/-- **Quantum circuit** from `nIn` to `nOut` qubits over the paper's gate set (Shmueli, *What Can
Be Computed with Indefinite Causal Structure?*, arXiv:2610.40573, version of 2026-11-03, sha256
d3e36399…b606, §3, p.14 (PDF p.16)): the input qubits occupy wires `0, …, nIn − 1`, `anc`
ancilla wires start in `|0⟩`, the gates of `gates` are applied in order, and the first `nOut`
wires are the output; the remaining wires are discarded.

**Formalization Note** Normal form with deferred measurement: a computational-basis
measurement is a CNOT onto a fresh `|0⟩` ancilla that is then discarded, and classical control
becomes quantum control, which preserves the implemented channel and changes the size by a
constant factor. The paper's theorems are existential in the output circuit, so this smaller
syntax only strengthens them. The gate list is the published `QAlgorithms.Circuit` (gates on
distinct wires, applied head first). -/
structure QCirc (nIn nOut : ℕ) where
  /-- The number of ancilla wires, initialized to `|0⟩`. -/
  anc : ℕ
  /-- The gates, over the paper's gate set, on the `nIn + anc` wires. -/
  gates : Circuit gateSet (nIn + anc)
  /-- The output is the first `nOut` wires. -/
  out_le : nOut ≤ nIn + anc

/-- The split of the circuit's wires into the `nOut` output wires and the discarded rest. -/
def QCirc.outSplit {nIn nOut : ℕ} (C : QCirc nIn nOut) :
    Qubits (nIn + C.anc) ≃ Qubits nOut × Qubits (nIn + C.anc - nOut) :=
  (Equiv.arrowCongr (finCongr (by have := C.out_le; omega)) (Equiv.refl Bool)).trans
    (splitQ nOut (nIn + C.anc - nOut))

/-- **The channel `𝒞_C` implemented by a circuit** (§3, p.14; Definition 4.5, p.19):
`ρ ↦ Tr_discarded(G (ρ ⊗ |0^anc⟩⟨0^anc|) G†)`, with `G` the product of the gates. -/
def QCirc.channel {nIn nOut : ℕ} (C : QCirc nIn nOut) :
    Matrix (Qubits nIn) (Qubits nIn) ℂ →ₗ[ℂ] Matrix (Qubits nOut) (Qubits nOut) ℂ where
  toFun ρ := Matrix.of fun y y' => ∑ d : Qubits (nIn + C.anc - nOut),
    (C.gates.unitary * padZero C.anc ρ * (C.gates.unitary).conjTranspose)
      (C.outSplit.symm (y, d)) (C.outSplit.symm (y', d))
  map_add' ρ σ := by
    ext y y'
    simp [padZero_add, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c ρ := by
    ext y y'
    simp [padZero_smul, Finset.mul_sum]

/-- **The matrix `U_C` of an `m`-qubit circuit** (§3, p.14): the work-`|0⟩` block
`U_C(y, x) = ⟨y, 0^anc| G |x, 0^anc⟩` of the gate product `G`. -/
def QCirc.mat {m : ℕ} (C : QCirc m m) : Matrix (Qubits m) (Qubits m) ℂ :=
  Matrix.of fun y x =>
    C.gates.unitary ((splitQ m C.anc).symm (y, fun _ => false))
      ((splitQ m C.anc).symm (x, fun _ => false))

/-- **Unitary circuit** (Shmueli, arXiv:2610.40573, §3, p.14 (PDF p.16)): "an n-qubit unitary
circuit is an n to n quantum circuit such that there exists a unitary matrix `U_C` … such that
`C(|ψ⟩⟨ψ|) = U_C |ψ⟩⟨ψ| U_C†`", where "a unitary circuit may use additional work registers,
provided these registers are returned to `|0⟩` on every input to the stated unitary".

**Formalization Note** Since the gate product `G` is unitary, the work-`|0⟩` block `C.mat` is
unitary exactly when `G |x, 0⟩ = (U_C |x⟩) |0⟩` for every `x` with `U_C = C.mat`, i.e. the work
wires return to `|0⟩` and the circuit implements `ρ ↦ U_C ρ U_C†`. This fixes `U_C` with its
phase (the paper's App. A, p.42: "These phases matter here"). -/
def QCirc.IsUnitary {m : ℕ} (C : QCirc m m) : Prop :=
  C.mat ∈ Matrix.unitaryGroup (Qubits m) ℂ

/-- The size `|C|` of a circuit: its gate count plus its number of wires (§3, p.14: "The circuit
description includes its register sizes and gate count"). -/
def QCirc.size {nIn nOut : ℕ} (C : QCirc nIn nOut) : ℕ :=
  C.gates.length + nIn + C.anc

/-- The `2 × 2` matrix `U_C` of a single-qubit circuit, indexed by `Bool` (`false` = `|0⟩`). -/
def qubitMat (C : QCirc 1 1) : Matrix Bool Bool ℂ :=
  C.mat.submatrix (fun b => fun _ => b) (fun b => fun _ => b)

end ICSCompute


