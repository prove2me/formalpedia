-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition__RegularParity
-- name    : OAI_InformationTheory_QuantumCircuit_Transition__RegularParity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:43:56.735671+00:00
-- url     : https://prove2.me/theorems/61bec225-6782-4417-8e7d-2e3c47ef4911
-- title:
--   Conjugation in a $C^{st}$-algebra
-- statement:
--   Let $\mathcal A$ be a $C^{\ast}$-algebra (for instance the algebra of complex $2^N\times 2^N$ matrices with the operator norm). For $U,B\in\mathcal A$ define the conjugate of $B$ by $U$ as
--
--   $$
--   \operatorname{conj}_U(B)=U\,B\,U^{\ast} .
--   $$
--
--   When $U$ is unitary, $\operatorname{conj}_U$ is a norm-preserving $\ast$-automorphism of $\mathcal A$; it maps projections to projections and is how a circuit $U$ transports a product projection $P_D^0$ to the evolved projection $U P_D^0 U^{\ast}$ in the localization estimates, e.g. $\bigl\|[\mathcal N_M\ge N^t]\operatorname{conj}_U(P_D^0)\,P_M^0\bigr\|$. Writing the estimates with $\operatorname{conj}$ makes composition rules such as $\operatorname{conj}_{UV}=\operatorname{conj}_U\circ\operatorname{conj}_V$ available uniformly.
--
--   **Formalization Note** The only definition is `conjugate (U B : A) : A := U*B*star U` for an arbitrary type `A` with a `CStarAlgebra` instance; no unitarity is assumed in the definition. The file also contains empty sections whose lemmas are proved in the solution file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Transition.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Transition.lean by skeleton subtraction
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


