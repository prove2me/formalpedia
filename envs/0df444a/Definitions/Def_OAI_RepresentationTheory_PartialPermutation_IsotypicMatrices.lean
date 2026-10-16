-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
-- name    : OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:14:20.402731+00:00
-- url     : https://prove2.me/theorems/53a3bc10-4306-4baa-affc-77cbf01b8a64
-- title:
--   Matrix models for isotypic modules: diagonal lifts, orbit maps and the model structure
-- statement:
--   Let $R$ be a complex algebra, and let $M$ and $S$ be $R$-modules that are also complex vector spaces, the two actions being compatible (complex scalars act through $R$). For $m\in\mathbb{N}$ write $S^m$ for the space of $m$-tuples $(x_1,\dots,x_m)$ of elements of $S$, and $M_d(\mathbb{C})$ for the algebra of complex $d\times d$ matrices.
--
--   1. **Diagonal endomorphisms.** The map $\operatorname{diag}_m\colon\operatorname{End}_{\mathbb{C}}(S)\to\operatorname{End}_{\mathbb{C}}(S^m)$ sending $A$ to the operator acting by $A$ in every coordinate is a homomorphism of complex algebras.
--   2. **Isotypic lift.** For an $R$-linear isomorphism $e\colon M\to S^m$, the complex algebra homomorphism $L_e\colon\operatorname{End}_{\mathbb{C}}(S)\to\operatorname{End}_{\mathbb{C}}(M)$ conjugates the diagonal action back to $M$.
--   3. **Orbit map.** For $e$ as above and $v\in M$, the complex-linear map $O_{e,v}\colon\operatorname{End}_{\mathbb{C}}(S)\to M$ is $A\mapsto L_e(A)\,v$.
--   4. **Isotypic matrix model.** An isotypic matrix model of $M$ over $R$ consists of
--      - an integer $d\ge 1$, the degree;
--      - a complex algebra homomorphism $L\colon M_d(\mathbb{C})\to\operatorname{End}_{\mathbb{C}}(M)$ such that for every matrix $A$ there is $r\in R$ with $L(A)x=r\cdot x$ for all $x\in M$;
--      - for every $v\in M$, a complex subspace $W\subseteq M$ with $v\in W$, $r\cdot W\subseteq W$ for all $r\in R$, and $\dim_{\mathbb{C}}W\le d^2$.
--
--   The formulas for items 1 and 2 are
--
--   $$
--   \operatorname{diag}_m(A)(x_1,\dots,x_m)=(Ax_1,\dots,Ax_m),\qquad L_e(A)=e^{-1}\circ\operatorname{diag}_m(A)\circ e .
--   $$
--
--   If $M\cong S^m$ with $S$ a simple module of complex dimension $d$, every complex endomorphism of $S$ is realised by an element of $R$ (Burnside's theorem), so $L_e$ composed with the identification $M_d(\mathbb{C})\cong\operatorname{End}_{\mathbb{C}}(S)$ is a matrix model, and the range of the orbit map $O_{e,v}$ is an $R$-invariant subspace containing $v$ of dimension at most $d^2$. The structure in item 4 records exactly these two features: a full matrix algebra acting on $M$ through $R$, and small invariant subspaces around every vector.
--
--   **Formalization Note** The objects are `diagonalEnd m`, `isotypicLift e` (built from `LinearEquiv.conjAlgEquiv` of the inverse of $e$, composed with `diagonalEnd`), `isotypicOrbitMap e v`, and the structure `IsotypicMatrixModel R M` with fields `degree`, `degree_pos`, `lift`, `lift_image`, `orbit`; the action of $r$ is written with `Algebra.lsmul`. The dimension bound uses `Module.finrank`, which is $0$ for an infinite-dimensional subspace, so it is only meaningful when the subspaces involved are finite-dimensional. An empty section named Burnside only declares hypotheses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/IsotypicMatrices.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/IsotypicMatrices.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the PartialPermutation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_PartialPermutation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SchurAverage
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ModuleTransport
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Components
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CentralKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CompleteKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RegularRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Plancherel
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TrivialRepresentation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ConvolutionKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ComponentGeometry
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Restriction

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace PartialPermutation

section Burnside
variable {R S : Type*} [Ring R] [Algebra ℂ R] [AddCommGroup S]
    [Module ℂ S] [Module R S] [IsScalarTower ℂ R S]
    [IsSimpleModule R S] [FiniteDimensional ℂ S]

end Burnside

def diagonalEnd {S : Type*} [AddCommGroup S] [Module ℂ S] (m : ℕ) :
    Module.End ℂ S →ₐ[ℂ] Module.End ℂ (Fin m → S) where
  toFun A := LinearMap.pi fun i => A.comp (LinearMap.proj i)
  map_zero' := by ext; rfl
  map_one' := by ext; rfl
  map_add' := by intros; ext; rfl
  map_mul' := by intros; ext; rfl
  commutes' := by intro; ext; rfl

section Isotypic
variable {R M S : Type*} [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
    [AddCommGroup S] [Module ℂ S] [Module R S] [IsScalarTower ℂ R S]

noncomputable def isotypicLift {m : ℕ} (e : M ≃ₗ[R] Fin m → S) :
    Module.End ℂ S →ₐ[ℂ] Module.End ℂ M :=
  (e.restrictScalars ℂ).symm.conjAlgEquiv ℂ |>.toAlgHom.comp (diagonalEnd m)

noncomputable def isotypicOrbitMap {m : ℕ} (e : M ≃ₗ[R] Fin m → S) (v : M) :
    Module.End ℂ S →ₗ[ℂ] M where
  toFun A := isotypicLift e A v
  map_add' A B := by simp
  map_smul' c A := by simp

end Isotypic

structure IsotypicMatrixModel (R M : Type*) [Ring R] [Algebra ℂ R]
    [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M] where
  degree : ℕ
  degree_pos : 0 < degree
  lift : Matrix (Fin degree) (Fin degree) ℂ →ₐ[ℂ] Module.End ℂ M
  lift_image : ∀ A, ∃ r : R, lift A = Algebra.lsmul ℂ ℂ M r
  orbit : ∀ v : M, ∃ W : Submodule ℂ M, v ∈ W ∧
    (∀ r : R, ∀ x ∈ W, r • x ∈ W) ∧ Module.finrank ℂ W ≤ degree ^ 2

end PartialPermutation

end

end OAI


