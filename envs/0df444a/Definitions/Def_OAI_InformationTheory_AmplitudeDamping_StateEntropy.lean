-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
-- name    : OAI_InformationTheory_AmplitudeDamping_StateEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:04:23.257998+00:00
-- url     : https://prove2.me/theorems/421718dd-cdc4-486e-ac04-3d3a75e5ecbb
-- title:
--   Site populations of multi-qubit matrices and spectral square-root factors
-- statement:
--   1. **Site population of a matrix.** Let $P$ be an $n$-qubit matrix, i.e. a complex matrix whose rows and columns are indexed by bit strings $i=(i_0,\dots,i_{n-1})\in\{0,1\}^n$. For a site $j\in\{0,\dots,n-1\}$,
--   $$\pi_j(P)=\sum_{i\in\{0,1\}^n:\ i_j=1}\operatorname{Re}P_{ii}.$$
--   For a density matrix $P$ this is the probability of finding qubit $j$ in $|1\rangle$ when measuring in the computational basis, i.e. the $|1\rangle$-population of its $j$-th one-qubit marginal; for $P=\psi\psi^*$ it equals $\sum_{i_j=1}|\psi_i|^2$.
--   2. **Spectral factor.** Let $\mathcal I$ be a finite index set and $A$ a positive semidefinite complex $\mathcal I\times\mathcal I$ matrix, with spectral decomposition $A=U\operatorname{diag}(\lambda)U^*$, where $\lambda_k\ge0$ are the eigenvalues and $U$ is the unitary whose columns are the chosen orthonormal eigenvectors. The spectral factor is
--   $$F_A=U\operatorname{diag}\bigl(\sqrt{\lambda}\bigr),\qquad (F_A)_{ik}=\sqrt{\lambda_k}\,U_{ik}.$$
--   It satisfies $F_AF_A^*=A$, and its $k$-th column has squared norm $\lambda_k$.
--
--   The population is linear in $P$, lies in $[0,1]$ for density matrices, and under the generalized amplitude-damping channel with parameters $\gamma,\nu\in[0,1]$ it evolves as $\pi_j(\mathcal N(P))=(1-\gamma)\pi_j(P)+\gamma\nu$ for density matrices $P$; it is the parameter of the per-qubit entropy bounds. The spectral factor writes every positive semidefinite matrix as a Gram matrix $FF^*$, so that mixed states can be treated through rectangular factor matrices in the same way as pure states.
--
--   **Formalization Note** The names are `matrixPopulation P j` for `P : QMatrix n`, and `spectralFactor hA`, which takes the proof `hA` of positive semidefiniteness and uses Mathlib's `eigenvalues` and `eigenvectorUnitary` of the underlying Hermitian matrix, so it depends on the eigenbasis chosen there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/StateEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/StateEntropy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_1} {α : Type u_2} [Fintype ι] [DecidableEq ι] [Fintype α]

def matrixPopulation {n : ℕ} (P : QMatrix n) (j : Fin n) : ℝ :=
  ∑ i, if i j = 1 then (P i i).re else 0

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_3} {α : Type u_4} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

def spectralFactor {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : Matrix ι ι ℂ :=
  fun i k ↦ (Real.sqrt (hA.isHermitian.eigenvalues k) : ℂ) * hA.isHermitian.eigenvectorUnitary i k

end GAD

end

end OAI


