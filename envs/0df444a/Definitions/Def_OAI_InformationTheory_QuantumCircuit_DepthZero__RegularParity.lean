-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_DepthZero__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:17:51.396718+00:00
-- url     : https://prove2.me/theorems/a019d9c5-0fae-45cd-8287-78d694e97387
-- title:
--   Single-site factors of a product projection
-- statement:
--   For a count $M=(S,v)$ on $N$ qubits (support $S$, unit vectors $v_i\in\mathbb C^2$ for $i\in S$) and a qubit $i$, the single-site factor is the $2\times2$ matrix
--
--   $$
--   \sigma_i(M)=\begin{cases}|v_i\rangle\langle v_i| & i\in S,\\ I & i\notin S.\end{cases}
--   $$
--
--   By definition the zero-mismatch projection is the tensor product of these factors, $P_M^0=\bigotimes_i\sigma_i(M)$, and each $\sigma_i(M)$ is an orthogonal projection. Working site by site is the basis of the depth-zero localization bound: an operator inequality for the product $P_M^0P_D^0\bigl(\bigotimes_i(2(I-\sigma_i(M))+\sigma_i(M))\bigr)P_D^0P_M^0$ reduces to an inequality for $2\times2$ matrices on each qubit.
--
--   **Formalization Note** The definition is `Count.site`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/DepthZero.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/DepthZero.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

/-- Single-site factor of a product projection. -/
def Count.site {N : ℕ} (M : Count N) (i : Fin N) : QubitOperator :=
  if i ∈ M.support then rankOne (M.vector i) else 1

end QAC

end

end OAI


