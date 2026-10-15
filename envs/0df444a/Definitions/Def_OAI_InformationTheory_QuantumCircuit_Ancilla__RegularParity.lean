-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Ancilla__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:33:18.163021+00:00
-- url     : https://prove2.me/theorems/59631fd6-d42c-44bb-b82f-ba7360775e59
-- title:
--   Ancilla-valid words and the projection onto zero ancillas
-- statement:
--   Consider $N$ qubits, of which the first $n$ carry the input and the remaining ones are ancillas.
--
--   1. **Ancilla-valid words.** A word $z\in\{0,1\}^N$ is ancilla-valid if $z_i=0$ for every qubit $i$ with $i\ge n$. (This is a decidable property.)
--   2. **Restriction to the input.** If $n\le N$, the restriction of $z\in\{0,1\}^N$ to its first $n$ bits is $(z_0,\dots,z_{n-1})\in\{0,1\}^n$.
--   3. **Ancilla projection.**
--   $$
--   \Pi_{\mathrm{anc}}=\bigotimes_{i}\begin{cases}I & i<n,\\ |0\rangle\langle0| & i\ge n,\end{cases}
--   $$
--   the orthogonal projection onto the span of the ancilla-valid basis states.
--
--   Ancilla validity describes only the initial state: the padded inputs $\hat x$ (input $x$ followed by zeros) are exactly the ancilla-valid words, and restriction inverts padding on them. No condition is placed on the final values of the ancillas. The projection $\Pi_{\mathrm{anc}}$ allows sums over inputs $x\in\{0,1\}^n$ to be written as traces of $N$-qubit operators.
--
--   **Formalization Note** The definitions are `ancillaValid` (with its `Decidable` instance), `restrictWord`, which takes the proof of $n\le N$ as an argument, and `ancillaProjection`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Ancilla.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Toffoli__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Computational__RegularParity

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


