-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
-- name    : OAI_InformationTheory_QuantumCircuit_Transition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:14:40.334719+00:00
-- url     : https://prove2.me/theorems/35f2861d-b857-42a3-9158-9e479c003bd7
-- title:
--   Conjugation $B\mapsto UBU^*$ in a C*-algebra
-- statement:
--   Let $\mathcal A$ be a unital C*-algebra; in the application $\mathcal A$ is the algebra of complex $2^N\times2^N$ matrices with the operator norm. For $U,B\in\mathcal A$ the file defines the conjugate of $B$ by $U$,
--
--   $$
--   \operatorname{conj}_U(B)=U\,B\,U^{*}.
--   $$
--
--   For a unitary $U$ the map $\operatorname{conj}_U$ is a $*$-automorphism of $\mathcal A$: it is multiplicative, additive, real-linear, unital and isometric, and it maps orthogonal projections to orthogonal projections. In the circuit setting $\operatorname{conj}_U(\Pi^D_0)=U\Pi^D_0U^{*}$ is the evolved product projection whose localization against a count is estimated, and composition is explicit: $\operatorname{conj}_{UV}=\operatorname{conj}_U\circ\operatorname{conj}_V$.
--
--   **Formalization Note** The Lean name is `conjugate`, stated for an arbitrary `CStarAlgebra`. The other sections of this definition file (`NormAlgebra`, `ThreeFactors`) only declare variables; the properties listed above are proved in the same module.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Transition.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Transition.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

section NormAlgebra
variable {A : Type*} [CStarAlgebra A]

end NormAlgebra

section ThreeFactors
variable {A : Type*} [CStarAlgebra A]

end ThreeFactors

section Conjugation
variable {A : Type*} [CStarAlgebra A]

def conjugate (U B : A) : A := U*B*star U

end Conjugation

end QAC

end

end OAI


