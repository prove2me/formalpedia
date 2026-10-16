-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
-- name    : OAI_InformationTheory_AmplitudeDamping_TensorEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:00:48.640333+00:00
-- url     : https://prove2.me/theorems/2074b940-7487-4e58-8da1-6cf5aeb2aa77
-- title:
--   Diagonal embedding, reindexing isomorphisms and Kronecker products of unitaries
-- statement:
--   Let $\mathcal I$ and $\mathcal K$ be finite index sets and let $M_{\mathcal I}$ denote the $*$-algebra of complex $\mathcal I\times\mathcal I$ matrices, with the conjugate transpose as involution.
--
--   1. **Diagonal $*$-homomorphism.** The map $\mathbb{C}^{\mathcal I}\to M_{\mathcal I}$, $x\mapsto\operatorname{diag}(x)$, as a homomorphism of $\mathbb{C}$-$*$-algebras, where $\mathbb{C}^{\mathcal I}$ carries pointwise operations and pointwise complex conjugation: $\operatorname{diag}(xy)=\operatorname{diag}(x)\operatorname{diag}(y)$ and $\operatorname{diag}(\overline{x})=\operatorname{diag}(x)^*$.
--   2. **Reindexing $*$-isomorphism.** For a bijection $e:\mathcal I\to\mathcal K$, the map $M_{\mathcal I}\to M_{\mathcal K}$, $A\mapsto A^{e}$ with
--   $$(A^{e})_{kl}=A_{e^{-1}(k)\,e^{-1}(l)},$$
--   as an isomorphism of $\mathbb{C}$-$*$-algebras.
--   3. **Tensor product of unitaries.** For unitaries $U$ on $\mathbb{C}^{\mathcal I}$ and $V$ on $\mathbb{C}^{\mathcal K}$, the Kronecker product $U\otimes V$, with entries $(U\otimes V)_{(i,k),(j,l)}=U_{ij}V_{kl}$, as an element of the unitary group of $\mathbb{C}^{\mathcal I\times\mathcal K}$.
--
--   Star-algebra homomorphisms commute with the continuous functional calculus, so these maps transport matrix functions such as $\eta(A)$, $\eta(x)=-x\log x$, between matrix algebras. They are used to compute the von Neumann entropy $S(A)=\operatorname{tr}\eta(A)$ of diagonal matrices, $S(\operatorname{diag}p)=\sum_i\eta(p_i)$ for real $p$; to show that $S$ is invariant under relabeling of the indices of a Hermitian matrix; and to prove the Kronecker product rule $S(A\otimes B)=\operatorname{tr}(B)\,S(A)+\operatorname{tr}(A)\,S(B)$ for Hermitian $A,B$, which gives $S(A\otimes B)=S(A)+S(B)$ for density matrices.
--
--   **Formalization Note** `diagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ` and `reindexStarAlgEquiv e : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ` upgrade Mathlib's `Matrix.diagonalAlgHom` and `Matrix.reindexAlgEquiv`; `tensorUnitary U V` bundles `U ⊗ₖ V` with the proof `Matrix.kronecker_mem_unitary`. In Lean the entropy is the real part of the trace.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/TensorEntropy.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/TensorEntropy.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open scoped BigOperators
open Set Filter Topology

open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
namespace GAD
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq κ] in
noncomputable def diagonalStarAlgHom : (ι → ℂ) →⋆ₐ[ℂ] Matrix ι ι ℂ :=
  { Matrix.diagonalAlgHom ℂ with
    map_star' := by intro x; ext i j; simp [Matrix.star_apply, Matrix.diagonal_apply]; split_ifs <;> simp_all }

noncomputable def reindexStarAlgEquiv (e : ι ≃ κ) : Matrix ι ι ℂ ≃⋆ₐ[ℂ] Matrix κ κ ℂ :=
  { Matrix.reindexAlgEquiv ℂ ℂ e with
    map_star' := by intro A; ext i j; rfl
    map_smul' := by intro r A; rfl }

end GAD
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace GAD
variable {ι : Type u_3} {κ : Type u_4} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def tensorUnitary (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ), Matrix.kronecker_mem_unitary U.prop V.prop⟩

end GAD

end

end OAI


