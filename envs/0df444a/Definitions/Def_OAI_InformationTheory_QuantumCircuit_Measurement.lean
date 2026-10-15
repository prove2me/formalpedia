-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Measurement
-- name    : OAI_InformationTheory_QuantumCircuit_Measurement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:29:58.087769+00:00
-- url     : https://prove2.me/theorems/4df098d4-6abe-4128-915f-200b52340a48
-- title:
--   Output-qubit measurement projector and Born probabilities
-- statement:
--   Let $N$ be the number of qubits and $o\in[N]$ a designated output qubit. The file defines:
--
--   1. **Output-zero count.** $\omega_o$ is the count with support $\{o\}$ and vector $|0\rangle$ at $o$. Its zero projection
--   $$
--   \Pi^{\omega_o}_0=|0\rangle\langle0|_{o}\otimes I_{\mathrm{rest}}
--   $$
--   is the projector onto outcome $0$ of a computational-basis measurement of qubit $o$.
--
--   2. **Born probability.** For a complex $2^N\times2^N$ matrix $W$, a bit $b$ and a word $z\in\{0,1\}^N$,
--   $$
--   \Pr\nolimits_W[o=b\mid z]=\sum_{y\in\{0,1\}^N,\ y_o=b}\bigl|W_{y,z}\bigr|^2 ,
--   $$
--   the probability of reading $b$ on qubit $o$ after $W$ is applied to the basis state $|z\rangle$, summed over all values of the other qubits.
--
--   Because $\Pi^{\omega_o}_0$ is a product projection supported on one qubit, the measurement fits into the localization framework: the diagonal entries of $W^{*}\Pi^{\omega_o}_0W$ are the probabilities $\Pr_W[o=0\mid z]$, and for unitary $W$ the two outcome probabilities add up to $1$. The success probability of the parity problem is the case $z=\hat x$ (the input $x$ padded with zeros) and $b=\mathrm{parity}(x)$.
--
--   **Formalization Note** The Lean names are `outputZeroCount` and `outputProbability`. The Born probability is defined for an arbitrary matrix `W`; normalization holds only for unitaries. The identities in the last paragraph are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Measurement.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Measurement.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Matrix Polynomial Filter Asymptotics

namespace QAC

/-- The measured zero-outcome projector is a product projection on one qubit. -/
def outputZeroCount {N : ℕ} (out : Fin N) : Count N where
  support := {out}
  vector _ := basisVector 0
  normalized _ _ := basisVector_normalized 0

/-- Born probability for an arbitrary fixed input basis state. -/
def outputProbability {N : ℕ} (W : Operator N) (out : Fin N) (b : Bit) (z : Word N) : ℝ :=
  ∑ y, if y out=b then Complex.normSq (W y z) else 0

end QAC

end

end OAI


