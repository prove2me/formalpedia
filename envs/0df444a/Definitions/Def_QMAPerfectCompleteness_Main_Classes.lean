-- Prove2me | Definitions.Def_QMAPerfectCompleteness_Main_Classes
-- name    : QMAPerfectCompleteness_Main_Classes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:57.990037+00:00
-- url     : https://prove2.me/theorems/efa0e768-77dd-4904-8ec8-ca487eebf23a
-- title:
--   Verifiers, the acceptance operator (1) and the classes $\mathrm{QMA}_{\mathcal G}(c,s)$, QMA, $\mathrm{QMA}_1^{\mathcal G}$
-- statement:
--   A **verifier** over a gate set $\mathcal G$ is a circuit over $\mathcal G$ on a proof register $X$ of $m$ qubits and an ancilla register $Y$, with a designated output qubit whose value $1$ means acceptance. The case $m=0$ is allowed. With $V$ the unitary of the circuit and $\Pi_{\mathrm{acc}}$ the projector onto output $1$, the **acceptance operator** is
--
--   $$
--   E=(I_X\otimes\langle 0|_Y)\,V^\dagger\Pi_{\mathrm{acc}}V\,(I_X\otimes|0\rangle_Y).
--   $$
--
--   A **proof** is a density matrix $\rho$ on $X$: a positive semidefinite complex matrix with trace one. It is accepted with probability $\operatorname{Tr}(E\rho)$.
--
--   A **promise problem** is a pair $L=(L_{\mathrm{yes}},L_{\mathrm{no}})$ of disjoint sets of binary strings. For a gate set $\mathcal G$, the problem $L$ lies in $\mathrm{QMA}_{\mathcal G}(c,s)$ if a polynomial-time algorithm maps every input $x$ to a verifier $V_x$ over $\mathcal G$, with acceptance operator $E_x$, such that
--
--   1. if $x\in L_{\mathrm{yes}}$ then some proof is accepted with probability at least $c$, that is, $\lambda_{\max}(E_x)\ge c$;
--   2. if $x\in L_{\mathrm{no}}$ then every proof is accepted with probability at most $s$, that is, $E_x\preceq sI$.
--
--   The two classes of the main theorem are
--
--   $$
--   \mathrm{QMA}=\mathrm{QMA}_{\{H,\Lambda(P)\}}(2/3,1/3),\qquad
--   \mathrm{QMA}_1^{\mathcal G}=\mathrm{QMA}_{\mathcal G}(1,1/2).
--   $$
--
--   Nothing is required of $V_x$ on inputs outside the promise except that the algorithm produces it in polynomial time.
--
--   **Formalization Note** The promise type is the published `QAlgorithms.Complexity.PromiseProblem`, which contains only the two disjoint sets. The algorithm is a real multi-stack machine, `QAlgorithms.Complexity.PolyTimeComputable`, whose output is the code of the verifier. Every number in the code is in unary, so the running time of the machine bounds $m$, the number of ancillas and the number of gates by one polynomial in $|x|$. The source defines QMA for any universal gate set and notes that the choice does not matter; this definition uses the set with which its proof starts.
-- source:
--   Sabee Grewal, Dorian Rudolph, QMA has perfect completeness, STOC 2027 submission #490 (October 2026), §2, p. 6, Eq. (1), Definition 2.1; gate set $\{H,\Lambda(P)\}$, p. 7

import Definitions.Def_QMAPerfectCompleteness_Main_Gates

open Matrix
open scoped ComplexOrder

/-!
# Verifiers, acceptance operators and the classes `QMA_𝒢(c, s)`

Sabee Grewal, Dorian Rudolph, *QMA has perfect completeness*, STOC 2027 submission #490
(October 2026), §2, Eq. (1) and Definition 2.1 (p. 6).

Promise problems are the published `QAlgorithms.Complexity.PromiseProblem` (two disjoint sets of
binary strings, nothing else). The verifier generator is a real multi-stack machine
(`QAlgorithms.Complexity.PolyTimeComputable`, Mathlib's `Turing.TM2ComputableInPolyTime`) whose
output is the code of the verifier. All numbers in the code are in unary, so the machine's running
time bounds the proof size, the ancilla count and the gate count by one polynomial in `|x|`.
-/

namespace QMAPerfectCompleteness.Main

open QAlgorithms.Complexity (Str encNat PolyTimeComputable PromiseProblem)

/-- A verifier over the gate set `G` (§2, p. 6): a circuit on a proof register of `proofQubits`
qubits and an ancilla register of `ancillaQubits` qubits, with a designated output wire. Wires
`0, …, proofQubits - 1` are the proof register, the remaining wires the ancilla register. -/
structure Verifier (G : GateSet) where
  /-- The number `m` of proof qubits; `m = 0` is allowed. -/
  proofQubits : ℕ
  /-- The number of ancilla qubits. -/
  ancillaQubits : ℕ
  /-- The gate list; the head acts first. -/
  gates : List (Instr G (proofQubits + ancillaQubits))
  /-- The output qubit; value `1` (`true`) means acceptance. -/
  output : Fin (proofQubits + ancillaQubits)

namespace Verifier

variable {G : GateSet} (V : Verifier G)

/-- The computational basis of the whole verifier register (proof and ancilla). -/
abbrev Wire := Basis (V.proofQubits + V.ancillaQubits)

/-- The computational basis of the proof register. -/
abbrev Proof := Basis V.proofQubits

/-- The unitary of the verifier circuit. -/
noncomputable def unitary : Matrix V.Wire V.Wire ℂ := circuitMatrix V.gates

/-- The restriction of a register basis state to the proof wires. -/
def proofPart (w : V.Wire) : V.Proof := fun i => w (Fin.castAdd V.ancillaQubits i)

/-- The register basis state `|p⟩_X |0⟩_Y`: proof `p`, all ancillas zero. -/
def initialState (p : V.Proof) : V.Wire := Fin.append p fun _ => false

/-- The isometry `I_X ⊗ |0⟩_Y`. -/
def ancillaZero : Matrix V.Wire V.Proof ℂ :=
  Matrix.of fun w p => if w = V.initialState p then 1 else 0

/-- The projector `Π_acc` onto output value `1`. -/
def acceptProjector : Matrix V.Wire V.Wire ℂ :=
  Matrix.diagonal fun w => if w V.output then 1 else 0

/-- The acceptance operator, Eq. (1): `E = (I ⊗ ⟨0|_Y) V† Π_acc V (I ⊗ |0⟩_Y)`. -/
noncomputable def acceptanceOperator : Matrix V.Proof V.Proof ℂ :=
  V.ancillaZeroᴴ * V.unitaryᴴ * V.acceptProjector * V.unitary * V.ancillaZero

/-- A proof state: a positive semidefinite complex matrix of trace one. -/
def IsProofState (ρ : Matrix V.Proof V.Proof ℂ) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

/-- The acceptance probability `Tr(Eρ)` of the proof `ρ`. -/
noncomputable def acceptProb (ρ : Matrix V.Proof V.Proof ℂ) : ℝ :=
  (V.acceptanceOperator * ρ).trace.re

/-- Definition 2.1(i): `λ_max(E) ≥ c`, that is, some proof is accepted with probability at
least `c`. -/
def AcceptsSomeProof (c : ℝ) : Prop := ∃ ρ, V.IsProofState ρ ∧ c ≤ V.acceptProb ρ

/-- Definition 2.1(ii): `E ⪯ sI`, that is, every proof is accepted with probability at most `s`. -/
def AcceptsAllProofsAtMost (s : ℝ) : Prop := ∀ ρ, V.IsProofState ρ → V.acceptProb ρ ≤ s

/-- Self-delimiting binary code of a verifier: `m`, the ancilla count, the output wire and the gate
list, every number in unary. -/
def encode : Str :=
  encNat V.proofQubits ++ encNat V.ancillaQubits ++ encNat V.output.val ++ encodeGates V.gates

end Verifier

/-- Definition 2.1: `QMA_G(c, s)`. There is a polynomial-time algorithm mapping **every** input `x`
(also outside the promise) to the code of a verifier `V_x` over `G` such that every YES input has a
proof accepted with probability at least `c` and on every NO input every proof is accepted with
probability at most `s`. The source's constraint `0 ≤ s < c ≤ 1` holds at all three uses below. -/
def QMAClass (G : GateSet) (c s : ℝ) : Set PromiseProblem :=
  {L | ∃ (gen : Str → Str) (V : Str → Verifier G),
    PolyTimeComputable gen ∧ (∀ x, gen x = (V x).encode) ∧
    (∀ x ∈ L.yes, (V x).AcceptsSomeProof c) ∧ (∀ x ∈ L.no, (V x).AcceptsAllProofsAtMost s)}

/-- `QMA = QMA_𝒢(2/3, 1/3)` for a universal gate set `𝒢` (Definition 2.1). The source notes that
the choice of universal gate set does not matter; `{H, Λ(P)}` is the one its proof starts from. -/
def QMA : Set PromiseProblem := QMAClass gatesHP (2 / 3) (1 / 3)

/-- `QMA₁^G = QMA_G(1, 1/2)` (Definition 2.1). -/
def QMA1 (G : GateSet) : Set PromiseProblem := QMAClass G 1 (1 / 2)

end QMAPerfectCompleteness.Main


