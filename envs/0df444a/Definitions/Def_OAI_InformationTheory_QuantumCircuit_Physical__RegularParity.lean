-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Physical__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Physical__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:25:10.458337+00:00
-- url     : https://prove2.me/theorems/6da6004f-2d60-49ec-b5fa-d755f3d113e3
-- title:
--   Normal form of a gate list: one reflection layer followed by one local layer
-- statement:
--   This file defines how a list of physical gates (one-qubit unitaries and Toffoli gates) is rewritten as a product of reflections about product projections followed by a single layer of one-qubit unitaries.
--
--   1. **Single local gate.** For a qubit $q$ and a one-qubit unitary $u$, $\lambda_{q,u}$ is the local layer with $u$ on qubit $q$ and the identity on every other qubit.
--   2. **Normal counts.** For a list of gates, a list of counts is defined by recursion on the list:
--   $$
--   \nu(\,)=(\,),\qquad \nu\bigl(u\text{ on }q,\ l\bigr)=\bigl(A^{\lambda_{q,u}}\bigr)_{A\in\nu(l)},\qquad \nu\bigl(\mathrm{Toffoli}_{c,t},\ l\bigr)=\bigl(T_{c,t},\ \nu(l)\bigr),
--   $$
--   where $A^{L}$ is the count $A$ with its axes rotated by the local layer $L$, and $T_{c,t}$ is the Toffoli count (axis $|-\rangle$ on the target, $|1\rangle$ on the controls).
--   3. **Normal local layer.** Similarly, $\mu(\,)$ is the identity layer, $\mu(u\text{ on }q,\ l)_i=(\lambda_{q,u})_i\,\mu(l)_i$ for every qubit $i$, and $\mu(\mathrm{Toffoli}_{c,t},\ l)=\mu(l)$.
--
--   For a gate list $g_1,\dots,g_m$ with matrices $G_1,\dots,G_m$ these are designed so that
--   $$
--   G_1G_2\cdots G_m=\Bigl(\prod_{A\in\nu(g_1,\dots,g_m)}\bigl(I-2P_A^0\bigr)\Bigr)\cdot\bigotimes_i\mu(g_1,\dots,g_m)_i ,
--   $$
--   since a Toffoli gate equals $I-2P^0_{T_{c,t}}$ and a local gate can be moved to the right past a product projection by rotating its axes. Rotation does not change supports, so for a physical layer (gates with disjoint supports) $\nu$ is a reflection layer, and a physical circuit with $d$ layers becomes a normal-form circuit of depth $d$ (these facts are proved in the solution file).
--
--   **Formalization Note** The definitions are `singleLocal`, `normalCounts` and `normalLocal`, by structural recursion on `List (Gate N)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Physical.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Physical.lean by skeleton subtraction
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


