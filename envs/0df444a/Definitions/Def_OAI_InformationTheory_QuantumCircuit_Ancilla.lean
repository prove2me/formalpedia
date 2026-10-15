-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla
-- name    : OAI_InformationTheory_QuantumCircuit_Ancilla
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:27:03.955638+00:00
-- url     : https://prove2.me/theorems/7cae81ee-822d-4f94-9872-3c08ba191a38
-- title:
--   Zero-ancilla words, restriction to the input register, and the ancilla projection
-- statement:
--   Let $N$ be the number of qubits and $n$ the number of input qubits, at positions $i<n$; the positions $i\ge n$ are ancillas. The file defines:
--
--   1. **Zero-ancilla words.** A word $z\in\{0,1\}^N$ is ancilla-valid if $z_i=0$ for every position $i\ge n$. A decidability instance for this property is also provided.
--
--   2. **Restriction.** For $n\le N$ and $z\in\{0,1\}^N$, the restriction $z|_{[n]}\in\{0,1\}^n$ is the word of the first $n$ bits, $(z|_{[n]})_i=z_i$ for $i<n$.
--
--   3. **Ancilla projection.**
--   $$
--   \Pi_{\mathrm{anc}}=\bigotimes_{i\in[N]}\begin{cases}I & i<n,\\ |0\rangle\langle0| & i\ge n,\end{cases}
--   $$
--   the projection onto the span of the basis states $|z\rangle$ with $z$ ancilla-valid.
--
--   For $n\le N$ the ancilla-valid words are exactly the padded inputs $\hat x=(x_0,\dots,x_{n-1},0,\dots,0)$ with $x\in\{0,1\}^n$, and restriction inverts the padding. Hence sums over inputs $x\in\{0,1\}^n$ can be rewritten as sums over ancilla-valid words, i.e. as traces against $\Pi_{\mathrm{anc}}$. Only the initial state of the ancillas is constrained, never their final state; this is how the parity argument handles polynomially many initially zero ancillas with arbitrary final garbage.
--
--   **Formalization Note** The Lean names are `ancillaValid`, an anonymous `Decidable` instance, `restrictWord` (which takes a proof of `n ≤ N`) and `ancillaProjection`. The statements in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the QACParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

/-- The zero-ancilla computational subspace, without any condition on final garbage. -/
def ancillaValid {N : ℕ} (n : ℕ) (z : Word N) : Prop := ∀ i, n ≤ i.val → z i=0

instance {N : ℕ} (n : ℕ) (z : Word N) : Decidable (ancillaValid n z) := by
  unfold ancillaValid
  infer_instance

def restrictWord {n N : ℕ} (hnN : n ≤ N) (z : Word N) : Word n :=
  fun i => z ⟨i.val,lt_of_lt_of_le i.isLt hnN⟩

def ancillaProjection (n N : ℕ) : Operator N :=
  tensorMatrix fun i => if i.val<n then 1 else rankOne (basisVector 0)

end QAC

end

end OAI


