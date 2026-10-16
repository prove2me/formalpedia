-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
-- name    : OAI_InformationTheory_AmplitudeDamping_BlockFactors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:09:33.752984+00:00
-- url     : https://prove2.me/theorems/ec615a1b-b487-473d-97db-b68be7d9ec35
-- title:
--   Block-diagonal unitaries, block projections and block injections
-- statement:
--   Let $\mathcal I$ and $\mathcal M$ be finite index sets and consider complex matrices indexed by pairs $(i,m)\in\mathcal I\times\mathcal M$, i.e. acting on $\mathbb{C}^{\mathcal I}\otimes\mathbb{C}^{\mathcal M}=\bigoplus_{m\in\mathcal M}\mathbb{C}^{\mathcal I}$; for fixed $m$ the indices $(\cdot,m)$ form the $m$-th block.
--
--   1. **Block-diagonal unitary.** For a family $(U_m)_{m\in\mathcal M}$ of unitaries on $\mathbb{C}^{\mathcal I}$, the block-diagonal matrix $\bigoplus_mU_m$ with entries
--   $$\Bigl(\bigoplus_mU_m\Bigr)_{(i,m),(j,m')}=\begin{cases}(U_m)_{ij}&m=m',\\0&m\neq m',\end{cases}$$
--   regarded as an element of the unitary group of $\mathbb{C}^{\mathcal I\times\mathcal M}$.
--   2. **Block projection.** For $m\in\mathcal M$, $\Pi_m$ is the diagonal matrix with entry $1$ at the indices $(i,m)$ and $0$ elsewhere; in tensor notation $\Pi_m=\mathbf 1\otimes|m\rangle\langle m|$, the orthogonal projection onto the $m$-th block.
--   3. **Block injection.** For $m\in\mathcal M$, $J_m$ is the $(\mathcal I\times\mathcal M)\times\mathcal I$ matrix with $(J_m)_{(i,m'),j}=1$ if $m'=m$ and $i=j$, and $0$ otherwise. It maps $x\in\mathbb{C}^{\mathcal I}$ to $x\otimes|m\rangle$, i.e. places $x$ into block $m$, and it is an isometry: $J_m^*J_m=\mathbf 1$.
--
--   These are used to place factor matrices of several states into mutually orthogonal blocks of a larger space, as in the Naimark dilation of a measurement. The von Neumann entropy of a block-diagonal matrix of Hermitian blocks is the sum of the entropies of the blocks, and for an isometry $W$ one has $S\bigl((WX)(WX)^*\bigr)=S(XX^*)$, so moving a factor into a block does not change the entropy of its Gram matrix.
--
--   **Formalization Note** The names are `blockUnitary U`, a term of `Matrix.unitaryGroup (ι × μ) ℂ` built from `Matrix.blockDiagonal`, `blockProjection m` and `blockInjection m`; the block label is the second coordinate of the index pair.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/BlockFactors.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/BlockFactors.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

section
variable {ι : Type u_1} {μ : Type u_2} [Fintype ι] [Fintype μ] [DecidableEq ι] [DecidableEq μ]

def blockUnitary (U : μ → Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup (ι × μ) ℂ :=
  ⟨Matrix.blockDiagonal (fun m ↦ U m), by
    constructor
    · change (Matrix.blockDiagonal _)ᴴ*Matrix.blockDiagonal _=1
      rw [Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]
      simp only [← Matrix.star_eq_conjTranspose,Unitary.coe_star_mul_self]
      exact Matrix.blockDiagonal_one
    · change Matrix.blockDiagonal _*(Matrix.blockDiagonal _)ᴴ=1
      rw [Matrix.blockDiagonal_conjTranspose,← Matrix.blockDiagonal_mul]
      simp only [← Matrix.star_eq_conjTranspose,← Unitary.coe_star,Unitary.coe_mul_star_self]
      exact Matrix.blockDiagonal_one⟩

end

variable {ι : Type u_3} {κ : Type u_4} {μ : Type u_5} [Fintype ι] [Fintype κ] [Fintype μ]
  [DecidableEq ι] [DecidableEq μ]

def blockProjection (m : μ) : Matrix (ι × μ) (ι × μ) ℂ :=
  Matrix.diagonal (fun im ↦ if im.2=m then 1 else 0)

def blockInjection (m : μ) : Matrix (ι × μ) ι ℂ :=
  fun ia j ↦ if ia.2=m then if ia.1=j then 1 else 0 else 0

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD
variable {ι : Type u_8} [Fintype ι] [DecidableEq ι]

end GAD

end

end OAI


