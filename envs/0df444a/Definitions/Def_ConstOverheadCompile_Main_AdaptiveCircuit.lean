-- Prove2me | Definitions.Def_ConstOverheadCompile_Main_AdaptiveCircuit
-- name    : ConstOverheadCompile_Main_AdaptiveCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:41.521068+00:00
-- url     : https://prove2.me/theorems/9ce31f80-b193-40cb-9243-7573fe35b451
-- title:
--   Adaptive circuits, their worst-case gate count, their channels with ancillas, and diamond-distance closeness
-- statement:
--   An **adaptive circuit** on $n$ wires over a gate set $S$ is a finite tree. Each node either stops, or applies a gate of $S$ to a tuple of distinct wires and continues, or measures one wire $q$ in the computational basis and continues with a subtree that depends on the outcome $b\in\{0,1\}$. The branching is the classical feed-forward: later gates may depend on all earlier outcomes. The measured wire remains in the collapsed state.
--
--   1. The **worst-case gate count** $\mathrm{maxGates}(A)$ is the largest number of gates on any root-to-leaf branch. Measurements are not gates.
--   2. Each branch $p$ gives the operator $K_p$, the product, in time order, of the embedded gate matrices and of the projectors $|b\rangle\langle b|_q$ for the outcomes taken. The **channel** of $A$ is $\Phi_A(\rho)=\sum_p K_p\rho K_p^\dagger$.
--   3. If $A$ acts on $n+a$ wires, the first $n$ are data and the last $a$ are ancillas. The **data channel** starts every ancilla in $|0\rangle$ and traces the ancillas out at the end:
--   $$\Phi^{\mathrm{data}}_A(\rho)=\mathrm{Tr}_{\mathrm{anc}}\big[\Phi_A(\rho\otimes|0^a\rangle\langle0^a|)\big]=\sum_{j\in\{0,1\}^a}\sum_p K_{p,j}\rho K_{p,j}^\dagger,\qquad K_{p,j}=(I\otimes\langle j|)K_p(I\otimes|0^a\rangle).$$
--   4. Two maps $\Phi,\Psi$ on $n$ qubits are **$\varepsilon$-close in diamond distance** if for every reference dimension $m$ and every density operator $\rho$ on $\mathbb C^m\otimes(\mathbb C^2)^{\otimes n}$,
--   $$\big\|(\mathrm{id}_m\otimes\Phi)(\rho)-(\mathrm{id}_m\otimes\Psi)(\rho)\big\|_1\le\varepsilon .$$
--   This is $\|\Phi-\Psi\|_\diamond\le\varepsilon$ with the full trace norm (Wilde, Def. 9.1.3), which is at least the half-normalized diamond distance.
--
--   These objects express "an adaptive circuit that uses $O(G)$ gates in the worst case" and "implements a circuit to within diamond distance $\varepsilon$".
--
--   **Formalization Note** The channels are defined together with their extension $\mathrm{id}_m\otimes(\cdot)$ to each reference system `Fin m`, and closeness is stated as a universal bound rather than through the supremum `WildeQIT.diamondNorm`, which avoids the junk value of `sSup` on an unbounded set. Kraus operators are listed branch by branch, outcome $0$ before outcome $1$.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.1 (adaptive quantum circuit), p.2 (Theorem 1 and the following paragraph), p.8 Remark 5, p.16 Eq. (65); diamond norm: Wilde, Quantum Information Theory, 2nd ed., Def. 9.1.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_WildeQIT_traceDist
import Definitions.Def_WildeQIT_IsDensityOperator

namespace ConstOverheadCompile.Main

open QAlgorithms
open scoped Kronecker Matrix

/-- p.1 ("an adaptive quantum circuit (i.e., one in which we can perform intermediate measurements
and have future quantum gates depend on these measurement outcomes)"), p.2 and Remark 5, p.8:
an adaptive circuit on `n` wires over the gate set `S`, as a finite tree. A node either stops,
applies a gate of `S` to distinct wires and continues, or measures wire `q` in the computational
basis and continues with a subtree chosen by the outcome. Classical feed-forward is the
branching: every later gate may depend on every earlier outcome. The measured wire stays in the
collapsed state; no separate record register exists. -/
inductive AdaptiveCircuit (S : Set Gate) (n : ℕ) where
  /-- Stop. -/
  | done : AdaptiveCircuit S n
  /-- Apply one gate of `S`, then continue. -/
  | gate (g : GateApp S n) (next : AdaptiveCircuit S n) : AdaptiveCircuit S n
  /-- Measure wire `q` in the computational basis; continue with `next b` on outcome `b`. -/
  | measure (q : Fin n) (next : Bool → AdaptiveCircuit S n) : AdaptiveCircuit S n

namespace AdaptiveCircuit

variable {S : Set Gate} {n : ℕ}

/-- The worst-case gate count ("in the worst case", Theorem 1): the maximum, over all execution
branches, of the number of gates applied on that branch. Measurements are not gates. -/
def maxGates : AdaptiveCircuit S n → ℕ
  | done => 0
  | gate _ k => 1 + maxGates k
  | measure _ k => max (maxGates (k false)) (maxGates (k true))

/-- The computational-basis projector `|b⟩⟨b|` on wire `q`, tensored with the identity on the
other wires. -/
def proj (q : Fin n) (b : Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.diagonal fun x => if x q = b then 1 else 0

/-- The Kraus operators of the circuit, one per root-to-leaf path: the ordered product (first
operation rightmost) of the embedded gate matrices and the projectors `|b⟩⟨b|` for the outcomes
`b` taken on that path. Branch `false` is listed before branch `true`. -/
def krausList : AdaptiveCircuit S n → List (Matrix (Qubits n) (Qubits n) ℂ)
  | done => [1]
  | gate g k => (krausList k).map fun K => K * embedOp g.gate.mat g.wires
  | measure q k =>
      (krausList (k false)).map (fun K => K * proj q false) ++
        (krausList (k true)).map (fun K => K * proj q true)

/-- The circuit's channel tensored with the identity on a reference system `Fin m`:
`(id_m ⊗ Φ_A)(ρ) = Σ_p (I_m ⊗ K_p) ρ (I_m ⊗ K_p)†`, summed over the paths `p`. -/
def channelRef (A : AdaptiveCircuit S n) (m : ℕ)
    (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ :=
  ((krausList A).map fun K =>
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K) * ρ * ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ K)ᴴ).sum

/-- For a path operator `K` on `n + a` wires and an ancilla string `j`, the data-register
operator `(I ⊗ ⟨j|) K (I ⊗ |0^a⟩)`: data are wires `0, …, n − 1`, ancillas wires
`n, …, n + a − 1`, every ancilla starts in `|0⟩`. -/
def ancillaCompress {a : ℕ} (K : Matrix (Qubits (n + a)) (Qubits (n + a)) ℂ) (j : Qubits a) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => K (Fin.append x j) (Fin.append y (fun _ => false))

/-- The channel that a circuit on `n + a` wires implements on its first `n` wires, with the `a`
ancillas initialized to `|0⟩` and traced out at the end, tensored with the identity on a
reference system `Fin m`:
`ρ ↦ Σ_j Σ_p (I_m ⊗ K_{p,j}) ρ (I_m ⊗ K_{p,j})†`, `K_{p,j} = (I ⊗ ⟨j|) K_p (I ⊗ |0^a⟩)`,
i.e. `ρ ↦ (id_m ⊗ Tr_anc)[(id_m ⊗ Φ_A)(ρ ⊗ |0^a⟩⟨0^a|)]`. -/
def dataChannelRef {a : ℕ} (A : AdaptiveCircuit S (n + a)) (m : ℕ)
    (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) :
    Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ :=
  ∑ j : Qubits a, ((krausList A).map fun K =>
    ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ancillaCompress K j) * ρ *
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ ancillaCompress K j)ᴴ).sum

end AdaptiveCircuit

/-- Diamond-distance closeness (Wilde, Def. 9.1.3, full trace norm, no factor 1/2) in universal
form: two maps `Φ, Ψ`, each given together with its extension `id_m ⊗ ·` to every reference
system `Fin m`, satisfy `‖Φ − Ψ‖_⋄ ≤ ε`, i.e. for every `m` and every density operator `ρ` on
`Fin m × Qubits n`, `‖(id_m ⊗ Φ)(ρ) − (id_m ⊗ Ψ)(ρ)‖₁ ≤ ε`. -/
def DiamondClose {n : ℕ}
    (Φ Ψ : (m : ℕ) → Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ →
      Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ) (ε : ℝ) : Prop :=
  ∀ (m : ℕ) (ρ : Matrix (Fin m × Qubits n) (Fin m × Qubits n) ℂ),
    WildeQIT.IsDensityOperator ρ → WildeQIT.traceDist (Φ m ρ) (Ψ m ρ) ≤ ε

end ConstOverheadCompile.Main


