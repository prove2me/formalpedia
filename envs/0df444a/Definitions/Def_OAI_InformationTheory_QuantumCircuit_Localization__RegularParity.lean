-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Localization__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Localization__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:18:32.384812+00:00
-- url     : https://prove2.me/theorems/e1f77db4-2b8d-4076-a3b3-b5c91ae9a721
-- title:
--   Uniform localization property for normal-form circuits of depth $d$
-- statement:
--   For $d\in\mathbb N$ and real numbers $s,t$, the property $\mathrm{UL}(d,s,t)$ holds if for all sufficiently large $N$ (that is, there is $N_0$ such that for every $N\ge N_0$) the following is true: for every normal-form circuit $U$ of depth $d$ on $N$ qubits and all counts $M,D$ on $N$ qubits,
--
--   $$
--   \bigl\|\,[\mathcal N_M\ge N^t]\ \operatorname{conj}_U\!\bigl(P_D^0\bigr)\ P_M^0\,\bigr\|\ \le\ e^{-N^s}.
--   $$
--
--   Here $P_D^0$, $P_M^0$ are the zero-mismatch product projections of the counts, $[\mathcal N_M\ge N^t]$ is the projection onto mismatch count at least $N^t$ relative to the axes of $M$, $\operatorname{conj}_U(B)=UBU^{\ast}$, and the norm is the Euclidean operator norm. A circuit of depth $d$ is $U=L_0R_1L_1\cdots R_dL_d$ with local layers $L_j$ and reflection layers $R_j$.
--
--   The threshold $N_0$ depends only on $(d,s,t)$, not on the circuit or the counts; this uniformity is what the induction on depth and on the scale pair $(s,t)$ propagates. For $0\le s<t$ the property is equivalent to the localization statement in which the threshold is written out explicitly.
--
--   **Formalization Note** The definition is `UniformLocalization d s t`, written with the filter quantifier `∀ᶠ N in Filter.atTop`. No restriction on $s,t$ is built into the definition; the powers $N^t$ and $N^s$ are real powers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Localization.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Localization.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Polynomial Filter Asymptotics

namespace QAC

/-- The uniform estimate, with the eventual quantifier outside all circuit data. -/
def UniformLocalization (d : ℕ) (s t : ℝ) : Prop :=
  ∀ᶠ N : ℕ in Filter.atTop, ∀ U : Operator N, IsCircuit d U → ∀ M D : Count N,
    ‖M.high ((N:ℝ)^t)*conjugate U D.zero*M.zero‖ ≤ Real.exp (-((N:ℝ)^s))

end QAC

end

end OAI


