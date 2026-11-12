-- Prove2me | Definitions.Def_QSampVerif_TargetCircuit
-- name    : QSampVerif_TargetCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:29:25.298019+00:00
-- url     : https://prove2.me/theorems/ca4d171d-0dfe-462d-baed-a486fc7d55d7
-- title:
--   Target circuits $C$ and their output distributions $P_C$; the common input $\langle 1^\lambda, C\rangle$
-- statement:
--   A **target circuit** $C$ consists of a number $n$ of wires, all started in $|0\cdots0\rangle$, a layered circuit over the Clifford+T instruction set $\{H,S,T,X,\mathrm{CNOT}\}$, and a list of output wires. It is *well formed* when the output wires are distinct and the gates of each layer act on disjoint wires. Its description $\langle C\rangle$ is the tuple of $n$ (in unary), the circuit encoding and the output-wire list; $|C|$ denotes the length of $\langle C\rangle$.
--
--   The **output distribution** $P_C$ is the Born distribution of the outcome $y\in\{0,1\}^{m}$, $m$ the number of output wires, when the output wires of $C|0\cdots0\rangle$ are measured in the computational basis:
--
--   $$P_C(y)=\sum_{w:\ w|_{\mathrm{out}}=y}\bigl|(C|0\cdots0\rangle)_w\bigr|^2 .$$
--
--   As a distribution on verifier outputs $\{\bot\}\cup\{0,1\}^*$ it gives $\bot$ probability zero ("$P_C$ assigns probability zero to rejection", Lemma 14.4) and gives the string $y$ the probability $P_C(y)$.
--
--   The **common input** of verifier and prover on security parameter $\lambda$ (the paper's $\lambda_{\mathrm{sec}}$) is $x=\langle 1^\lambda,\langle C\rangle\rangle$.
--
--   **Formalization Note** The paper fixes no gate set; the published Clifford+T instruction set is used, into which the paper's $H$/$\mathrm{CCZ}$ compilation (§14.1) embeds exactly.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Theorem 14.5, p.189 (PDF 190); §14.1, pp.181–182 (PDF 182–183); Lemma 14.4, p.188

import Definitions.Def_QSampVerif_tup

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity

/-- Chung, Cojocaru, Lee, Lin, *Classical Verification of Quantum Sampling with Negligible
Error*, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Theorem 14.5, p.189 (PDF 190):
"let C be a quantum circuit with output distribution P_C"; §14.1, p.181–182: "fixed Clifford+T
decompositions".

A target circuit: `n` wires started in `|0…0⟩`, a layered circuit over the published Clifford+T
instruction set (`H, S, T, X, CNOT`), and the list of output wires, which are measured in the
computational basis at the end.

**Formalization Note.** The paper fixes no gate set. The pinned-down version uses the published
Clifford+T instructions `QAlgorithms.Complexity.Instr`; §14.1 compiles the target into `H` and
`CCZ`, which Clifford+T expresses exactly. -/
structure TargetCircuit where
  /-- Number of wires. -/
  n : ℕ
  /-- The layered Clifford+T circuit. -/
  circ : Layered n
  /-- The output wires, measured in the computational basis. -/
  outW : List (Fin n)

namespace TargetCircuit

/-- A target circuit is well formed: its output wires are distinct and the gates of each layer
act on disjoint wires. -/
def Valid (C : TargetCircuit) : Prop :=
  C.outW.Nodup ∧ ∀ l ∈ C.circ, LayerOk l

/-- The classical description of a target circuit; `|C|` is its length. -/
def encode (C : TargetCircuit) : Str :=
  tup [unary C.n, encCirc C.circ, wireList C.outW]

/-- The output distribution `P_C` (p.189): the Born probability that measuring the output wires
of `C|0…0⟩` in the computational basis gives `y`. -/
noncomputable def outputDist (C : TargetCircuit) (y : Qubits C.outW.length) : ℝ :=
  ∑ w : Qubits C.n,
    if (∀ j : Fin C.outW.length, w (C.outW.get j) = y j) then
      ‖runLayered C.circ (zeroState C.n) w‖ ^ 2 else 0

/-- `P_C` as a distribution on verifier outputs `Option Str` (p.188, Lemma 14.4: "P_C assigns
probability zero to rejection"): `⊥` gets `0`, the string `s` gets `P_C(y)` when `s` is the
outcome `y` read as a string of length `|outW|`, and `0` otherwise. -/
noncomputable def pushSome (C : TargetCircuit) : Option Str → ℝ
  | none => 0
  | some s => ∑ y : Qubits C.outW.length, if List.ofFn y = s then C.outputDist y else 0

/-- `P_C` on the finite alphabet `Y ∪ {⊥}` with `Y = {0,1}^{|outW|}`, giving `⊥` probability `0`. -/
noncomputable def pushSomeQ (C : TargetCircuit) : Option (Qubits C.outW.length) → ℝ
  | none => 0
  | some y => C.outputDist y

end TargetCircuit

/-- The common input of verifier and prover: the security parameter `λ` (the paper's `λ_sec`)
in unary and the description of the target circuit (paper.md decision 4). -/
def commonInput (lam : ℕ) (C : TargetCircuit) : Str :=
  tup [unary lam, C.encode]

end QSampVerif


