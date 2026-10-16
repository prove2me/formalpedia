-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
-- name    : OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:16:33.40551+00:00
-- url     : https://prove2.me/theorems/ec9301a4-d69d-4f49-8ef0-9a5a89372173
-- title:
--   Isotypic kernel models: matrix models together with a reproducing group-algebra kernel
-- statement:
--   Let $G$ be a group and let $M$ be a complex inner product space that is also a module over the group algebra $\mathbb{C}[G]$, compatibly with complex scalars; write $g\cdot x$ for the action of the basis element $g\in\mathbb{C}[G]$ on $x\in M$.
--
--   1. **The representation attached to a module.** The representation of $G$ on $M$ given by $g\mapsto(x\mapsto g\cdot x)$ induces on $\mathbb{C}[G]$ exactly the given module action, so its $\mathbb{C}[G]$-module is $\mathbb{C}[G]$-linearly isomorphic to $M$ by the identity on vectors.
--   2. **Isotypic kernel model.** For finite $G$, an isotypic kernel model of $M$ consists of an isotypic matrix model of $M$ over $\mathbb{C}[G]$ of some degree $d$ (an integer $d\ge 1$, a complex algebra homomorphism $L$ from complex $d\times d$ matrices to $\operatorname{End}_{\mathbb{C}}(M)$ each of whose values is the action of an element of $\mathbb{C}[G]$, and, for every $v\in M$, a $\mathbb{C}[G]$-invariant complex subspace containing $v$ of dimension at most $d^2$), together with a kernel $k\colon G\to\mathbb{C}$ satisfying the three conditions displayed below.
--
--   The conditions on the kernel are
--
--   $$
--   \sum_{g\in G}|k(g)|^2=\frac{d^2}{|G|},\qquad k(g^{-1})=\overline{k(g)}\quad(g\in G),\qquad \sum_{g\in G}k(g)\,(g\cdot x)=x\quad(x\in M).
--   $$
--
--   For an isotypic module whose simple constituent $S$ has dimension $d$ and character $\chi_S$, the natural kernel is $k(g)=\frac{d}{|G|}\overline{\chi_S(g)}$: Schur orthogonality gives the norm identity, unitarity gives the conjugate symmetry, and the element $\sum_g k(g)\,g$ is the central idempotent of the type of $S$, which acts as the identity on $M$. The structure packages exactly the properties needed to bound norms of Fourier transforms on a single isotypic piece.
--
--   **Formalization Note** Item 1 consists of the lemma `ofModule'_algebra` and the isomorphism `ofModule'ModuleEquiv` for Mathlib's `Representation.ofModule'`. The structure `IsotypicKernelModel G M` extends `IsotypicMatrixModel` over the group algebra by the fields `kernel`, `kernel_norm`, `kernel_inv` and `kernel_action`, where $g\cdot x$ is the action of `MonoidAlgebra.single g 1` and $|k(g)|$ is the complex norm. The inner product on $M$ belongs to the setting but is not used by the fields.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/IsotypicKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/IsotypicKernels.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicMatrices

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
open scoped MonoidAlgebra BigOperators ComplexConjugate

noncomputable section
variable {G M : Type*} [Group G]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M]

lemma ofModule'_algebra : (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom =
    Algebra.lsmul ℂ ℂ M := by
  exact (MonoidAlgebra.lift ℂ (Module.End ℂ M) G).apply_symm_apply _

noncomputable def ofModule'ModuleEquiv :
    (Representation.ofModule' (k := ℂ) (G := G) M).asModule ≃ₗ[ℂ[G]] M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change (Representation.ofModule' (k := ℂ) (G := G) M).asAlgebraHom a x = a • (show M from x)
    rw [ofModule'_algebra]
    rfl

structure IsotypicKernelModel (G M : Type*) [Group G] [Fintype G]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] extends IsotypicMatrixModel ℂ[G] M where
  kernel : G → ℂ
  kernel_norm : ∑ g, ‖kernel g‖^2 = (degree : ℝ)^2 / Fintype.card G
  kernel_inv : ∀ g, kernel g⁻¹ = conj (kernel g)
  kernel_action : ∀ x : M, ∑ g, kernel g • (MonoidAlgebra.single g (1 : ℂ)) • x = x

variable [Fintype G]

end
end PartialPermutation

end

end OAI


