-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace
-- name    : OAI_InformationTheory_QuantumCircuit_ParityTrace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:29:19.743909+00:00
-- url     : https://prove2.me/theorems/ba058351-aef4-4684-aa1c-db293eb682bf
-- title:
--   Parity character of the input register
-- statement:
--   Let $N$ be the number of qubits and $n$ the number of input positions, the positions $i<n$. For a word $z\in\{0,1\}^N$ the file defines the input sign
--   $$
--   \chi_n(z)=\prod_{i\in[N],\ i<n}(-1)^{z_i}=(-1)^{\sum_{i<n}z_i}\in\{1,-1\},
--   $$
--   the parity character of the bits of $z$ in the input positions; the ancilla bits are ignored.
--
--   The input sign is the diagonal of the phase operator $Z^{\otimes n}\otimes I$ on the input register. For $n\le N$ and a padded input $\hat x=(x_0,\dots,x_{n-1},0,\dots,0)$ it equals $(-1)^{x_0+\dots+x_{n-1}}$, the $\pm1$ encoding of the parity of $x\in\{0,1\}^n$. It is the character against which the output statistics of a circuit are correlated in the parity lower bound.
--
--   **Formalization Note** The Lean name is `inputSign`; it is a real number defined as a product over all `i : Fin N` with factor $1$ at positions $i\ge n$, so for $n>N$ every position counts. The identities in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ParityTrace.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ParityTrace.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

def inputSign {N : ℕ} (n : ℕ) (z : Word N) : ℝ :=
  ∏ i : Fin N, if i.val<n then bitSign (z i) else 1

end QAC

end

end OAI


