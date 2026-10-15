-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Measurement__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Measurement__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:37:20.87855+00:00
-- url     : https://prove2.me/theorems/41ba71b3-759f-4009-8477-704c2156324f
-- title:
--   Single-qubit output measurement and Born probabilities
-- statement:
--   This file defines the objects describing the measurement of one output qubit $o$ of an $N$-qubit operator $W$.
--
--   1. **Output-zero count.** The count $Z_o$ has support $\{o\}$ and axis $|0\rangle$; its zero-mismatch projection is
--   $$
--   P^0_{Z_o}=|0\rangle\langle0|_{o}\otimes I_{\text{rest}} ,
--   $$
--   the projector for the outcome $0$ on qubit $o$.
--   2. **Born probability.** For $b\in\{0,1\}$ and an input basis word $z\in\{0,1\}^N$,
--   $$
--   \Pr\nolimits_W(o=b\mid z)=\sum_{y\in\{0,1\}^N:\ y_o=b}\bigl|W_{y,z}\bigr|^2 ,
--   $$
--   the probability of reading $b$ on qubit $o$ after applying $W$ to $|z\rangle$, with all other qubits summed out.
--
--   For a unitary $W$ the diagonal entry $(W^{\ast}P^0_{Z_o}W)_{z,z}$ equals $\Pr_W(o=0\mid z)$ and the probabilities for $b=0,1$ add up to $1$; the success probability of computing parity is $\Pr_W(o=\operatorname{par}(x)\mid\hat x)$. Expressing the output event as the product projection $P^0_{Z_o}$ is what makes the localization theorem applicable to the measured output.
--
--   **Formalization Note** The definitions are `outputZeroCount` and `outputProbability`. Every qubit carries the axis $|0\rangle$ in `outputZeroCount`, but only the support $\{o\}$ matters.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Measurement.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Measurement.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Ancilla__RegularParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace__RegularParity

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


