-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_DepthZero
-- name    : OAI_InformationTheory_QuantumCircuit_DepthZero
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:20:51.475054+00:00
-- url     : https://prove2.me/theorems/22e1fe62-995a-4fe9-b178-288969e5dcfe
-- title:
--   Single-site factors of a product projection
-- statement:
--   Let $M$ be a count on $N$ qubits with support $S$ and one-qubit vectors $(v_i)_{i\in[N]}$ that are unit vectors for $i\in S$. For a qubit $i\in[N]$ the file defines the single-site factor
--   $$
--   P^M_i=\begin{cases}|v_i\rangle\langle v_i| & i\in S,\\ I & i\notin S,\end{cases}
--   $$
--   a $2\times2$ orthogonal projection. By definition the zero projection of the count factorizes as $\Pi^M_0=\bigotimes_{i}P^M_i$.
--
--   The single-site factors are the objects on which the depth-zero localization estimate is checked qubit by qubit: for two counts $M,D$ and $r\in\mathbb{R}$ one has $\|\Pi^M_{\ge r}\,\Pi^D_0\,\Pi^M_0\|^2\le2^{-r}$, and the proof reduces this operator inequality on $N$ qubits to a $2\times2$ inequality between the factors $P^M_i$ and $P^D_i$.
--
--   **Formalization Note** The Lean name is `Count.site`. `Count.zero M` is `tensorMatrix` of the family `fun i => if i ∈ M.support then rankOne (M.vector i) else 1`, which is pointwise `Count.site M i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/DepthZero.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/DepthZero.lean by skeleton subtraction
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


