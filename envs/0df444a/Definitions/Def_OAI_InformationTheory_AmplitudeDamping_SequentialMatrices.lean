-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
-- name    : OAI_InformationTheory_AmplitudeDamping_SequentialMatrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:27:22.086862+00:00
-- url     : https://prove2.me/theorems/414bd237-3196-4d25-8ecb-b0fa1a4be86b
-- title:
--   Left multiplication on flattened matrices and products of rejection operators
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets. Identify a vector $v$ of the Euclidean space $\mathbb{C}^{\iota\times\kappa}$ with the $\iota\times\kappa$ matrix $X_v$ whose entries are $(X_v)_{ik}=v_{(i,k)}$. The file defines:
--
--   1. **Projection action.** For a square matrix $P\in\mathbb{C}^{\iota\times\iota}$, the map $\mathcal{A}_P:\mathbb{C}^{\iota\times\kappa}\to\mathbb{C}^{\iota\times\kappa}$ obtained by reshaping $v$ into $X_v$, multiplying by $P$ on the left and flattening back:
--   $$\mathcal{A}_P(v)_{(i,k)}=(PX_v)_{ik}=\sum_{j\in\iota}P_{ij}\,v_{(j,k)} .$$
--   In tensor language, $\mathcal{A}_P=P\otimes I_\kappa$ acting on $\mathbb{C}^\iota\otimes\mathbb{C}^\kappa$.
--
--   2. **Rejection products.** For a sequence $Q_0,Q_1,Q_2,\dots$ of square matrices in $\mathbb{C}^{\iota\times\iota}$, the matrices $R_k$ defined recursively by $R_0=I$ and $R_{k+1}=(I-Q_k)R_k$, that is,
--   $$R_k=(I-Q_{k-1})(I-Q_{k-2})\cdots(I-Q_0) .$$
--
--   Neither definition assumes anything about $P$ or the $Q_k$. When $P$ is an orthogonal projection, $\mathcal{A}_P$ is an orthogonal projection of the Hilbert space of $\iota\times\kappa$ matrices with the Frobenius inner product, which turns the abstract union bound for sequential projections into a statement about matrices. When the $Q_k$ are orthogonal projections, $R_k$ describes the outcome that the tests $Q_0,\dots,Q_{k-1}$ have all been rejected in a sequential measurement, and $R_k^{*}Q_kR_k$ is the operator for a first acceptance at step $k$.
--
--   **Formalization Note** `projectionAction P v` is `frobVector (P * X)`, where `frobVector` flattens a matrix into `EuclideanSpace ℂ (ι × κ)`; `rejectProduct Q : ℕ → Matrix ι ι ℂ` is defined by recursion on $k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SequentialMatrices.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/SequentialMatrices.lean by skeleton subtraction
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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_1 u_2

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]

def projectionAction (P : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × κ)) :
    EuclideanSpace ℂ (ι × κ) := frobVector (P*(show Matrix ι κ ℂ from fun i k ↦ v (i,k)))

def rejectProduct (Q : ℕ → Matrix ι ι ℂ) : ℕ → Matrix ι ι ℂ
  | 0 => 1
  | k+1 => (1-Q k)*rejectProduct Q k

end GAD

end

end OAI


