-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
-- name    : OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:07:39.410984+00:00
-- url     : https://prove2.me/theorems/0bcae808-bf35-423f-8861-d26b8bacfa1b
-- title:
--   Matrices as Euclidean vectors and orthogonal projection matrices
-- statement:
--   Let $\mathcal I$ and $\mathcal K$ be finite index sets.
--
--   1. **Frobenius vector.** For $A\in\mathbb{C}^{\mathcal I\times\mathcal K}$, $\operatorname{vec}(A)$ is the same array regarded as a vector of the Euclidean space $\ell^2(\mathcal I\times\mathcal K)$, with coordinates $\operatorname{vec}(A)_{(i,k)}=A_{ik}$. Its norm is the Frobenius norm and its real inner products are trace pairings:
--   $$\|\operatorname{vec}(A)\|^2=\sum_{i,k}|A_{ik}|^2=\operatorname{Re}\operatorname{tr}(AA^*),\qquad \langle\operatorname{vec}(A),\operatorname{vec}(B)\rangle_{\mathbb{R}}=\operatorname{Re}\operatorname{tr}(A^*B).$$
--   2. **Orthogonal projection.** A square matrix $P\in\mathbb{C}^{\mathcal I\times\mathcal I}$ is a projection if it is Hermitian and idempotent: $P^*=P$ and $P^2=P$.
--
--   The vector picture turns the squared Frobenius norm of factor matrices (their mass) into a Hilbert-space norm, so that Pythagoras and the triangle inequality become available; for instance, for a projection $P$ one has $\operatorname{mass}(PA)+\operatorname{mass}(A-PA)=\operatorname{mass}(A)$, where $\operatorname{mass}(A)=\operatorname{Re}\operatorname{tr}(AA^*)$. These tools give a continuity estimate for the von Neumann entropy $S$ in terms of factors: if $\mathcal I$ is nonempty and $X,Y\in\mathbb{C}^{\mathcal I\times\mathcal K}$ satisfy $\operatorname{mass}X=\operatorname{mass}Y=1$, then for every $\varepsilon>0$
--   $$S(XX^*)-S(YY^*)\le\Bigl(\frac{\operatorname{mass}(X-Y)}{4\varepsilon}+\varepsilon\Bigr)\log|\mathcal I|+\Bigl(1+\frac{\operatorname{mass}(X-Y)}{4\varepsilon}+\varepsilon\Bigr)\log2.$$
--
--   **Formalization Note** `frobVector A` is an element of `EuclideanSpace ℂ (ι × κ)`, and `IsProjection P` is the proposition `P.IsHermitian ∧ P * P = P`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean by skeleton subtraction
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

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace GAD

section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]

def frobVector (A : Matrix ι κ ℂ) : EuclideanSpace ℂ (ι × κ) :=
  WithLp.toLp 2 (fun ik ↦ A ik.1 ik.2)

variable [DecidableEq ι]

def IsProjection (P : Matrix ι ι ℂ) : Prop := P.IsHermitian ∧ P*P=P

end

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_3} [Fintype ι] [DecidableEq ι]

end

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_4} {κ : Type u_5} [Fintype ι] [Fintype κ]

variable [DecidableEq ι]

end GAD

open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
namespace GAD
variable {ι : Type u_6} {κ : Type u_7} [Fintype ι] [Fintype κ]

end GAD

end

end OAI


