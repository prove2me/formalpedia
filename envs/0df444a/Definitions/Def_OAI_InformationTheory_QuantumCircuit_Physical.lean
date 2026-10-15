-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical
-- name    : OAI_InformationTheory_QuantumCircuit_Physical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:25:41.9835+00:00
-- url     : https://prove2.me/theorems/792ad40b-ad71-4a18-a46a-80be7bc37483
-- title:
--   Normal form of a list of gates: reflections followed by one local layer
-- statement:
--   A physical gate on $N$ qubits is either a one-qubit unitary $u\in U(2)$ acting on a qubit $q$, or a Toffoli gate with control set $c$ and target $t\notin c$. For a list of gates $g_1,\dots,g_m$, with matrix product $g_1g_2\cdots g_m$, the file defines:
--
--   1. **A single gate as a local layer.** $\lambda_{q,u}$ is the local layer with $u$ at qubit $q$ and the identity at all other qubits.
--
--   2. **Normal counts.** A list of counts defined recursively by $\nu([\,])=[\,]$ and
--   $$
--   \nu(\mathrm{local}(q,u)::l)=\bigl[A^{\lambda_{q,u}}\ :\ A\in\nu(l)\bigr],\qquad \nu(\mathrm{Tof}(c,t)::l)=\tau_{c,t}::\nu(l),
--   $$
--   where $A^{\lambda}$ is the count $A$ rotated by the local layer $\lambda$ (vectors $\lambda_iv_i$, same support) and $\tau_{c,t}$ is the Toffoli count (support $c\cup\{t\}$, vector $|-\rangle$ at $t$ and $|1\rangle$ on $c$).
--
--   3. **Normal local layer.** A local layer defined by $\mu([\,])_i=I$, $\mu(\mathrm{local}(q,u)::l)_i=(\lambda_{q,u})_i\,\mu(l)_i$ and $\mu(\mathrm{Tof}(c,t)::l)=\mu(l)$.
--
--   These are designed so that
--   $$
--   g_1g_2\cdots g_m=\Bigl(\prod_{A\in\nu(g_1,\dots,g_m)}\bigl(I-2\,\Pi^A_0\bigr)\Bigr)\cdot\bigotimes_i\mu(g_1,\dots,g_m)_i ,
--   $$
--   that is, every one-qubit gate is moved to the right through the reflections, which rotates their product axes but not their supports. Each normal count has the support of one of the gates, so a physical layer with pairwise disjoint gate supports becomes one reflection layer followed by one local layer, and a circuit of $d$ physical layers is a normal-form circuit of depth $d$.
--
--   **Formalization Note** The Lean names are `singleLocal`, `normalCounts` and `normalLocal`, defined by recursion on `List (Gate N)`. The displayed identity and the depth statement are proved in the same module (using the Toffoli identity $\mathrm{Tof}_{c,t}=I-2\Pi^{\tau_{c,t}}_0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Physical.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Physical.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- A physical one-qubit gate, as a local layer. -/
def singleLocal {N : ℕ} (q : Fin N) (u : Matrix.unitaryGroup Bit ℂ) : LocalLayer N :=
  fun i => if i=q then u else 1

/-- Local gates are moved to the right by rotating the product axes; supports
are unchanged, so a disjoint physical layer yields one reflection layer. -/
def normalCounts {N : ℕ} : List (Gate N) → List (Count N)
  | [] => []
  | .local q u :: l => (normalCounts l).map (fun A => A.rotate (singleLocal q u))
  | .toffoli c t _ :: l => toffoliCount c t :: normalCounts l

def normalLocal {N : ℕ} : List (Gate N) → LocalLayer N
  | [] => fun _ => 1
  | .local q u :: l => fun i => singleLocal q u i * normalLocal l i
  | .toffoli _ _ _ :: l => normalLocal l

end QAC

end

end OAI


