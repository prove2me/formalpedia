-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_ParityTrace__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_ParityTrace__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:36:18.996859+00:00
-- url     : https://prove2.me/theorems/f1fd7391-b35a-4e31-ad27-4dcb4f61167d
-- title:
--   Parity character of the input qubits
-- statement:
--   For $n\in\mathbb N$ and a word $z\in\{0,1\}^N$, the input sign of $z$ is the real number
--
--   $$
--   \chi_n(z)=\prod_{\substack{0\le i\le N-1\\ i<n}}(-1)^{z_i},
--   $$
--
--   that is, $+1$ if the input bits $z_0,\dots,z_{\min(n,N)-1}$ have even parity and $-1$ otherwise.
--
--   This is the diagonal of the input phase operator $Z_{\mathrm{in}}=\bigotimes_i(Z\text{ if }i<n,\ I\text{ otherwise})$, and on a padded input $\hat x$ (with $n\le N$) it equals the parity character $(-1)^{x_1+\dots+x_n}$ of $x\in\{0,1\}^n$. It enters the trace identity expressing $\sum_x(-1)^{\operatorname{par}(x)}B_{\hat x,\hat x}$ as $\operatorname{tr}(Z_{\mathrm{in}}\Pi_{\mathrm{anc}}B)$.
--
--   **Formalization Note** The definition is `inputSign n z`, a product over all `i : Fin N` of `bitSign (z i)` if `i.val < n` and `1` otherwise.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/ParityTrace.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/ParityTrace.lean by skeleton subtraction
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


