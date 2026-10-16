-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SmallKernels
-- name    : OAI_RepresentationTheory_PartialPermutation_SmallKernels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:06:55.278989+00:00
-- url     : https://prove2.me/theorems/030555bc-637d-421b-9ede-3921ae1b4160
-- title:
--   Kernel selecting the irreducible types of degree at most $R$
-- statement:
--   Let $G$ be a finite group. Let $\operatorname{Irr}(G)$ be the set of isotypic components of the left regular representation $\lambda$ of $G$ on $\ell^2(G)$ (complex functions on $G$, with $(\lambda(g)f)(h)=f(g^{-1}h)$), regarded as a module over the group algebra $\mathbb{C}[G]$. For $c\in\operatorname{Irr}(G)$ let $S_c\subseteq\ell^2(G)$ be the simple submodule chosen to represent the type of $c$, let $\pi_c$ be the restriction of $\lambda$ to $S_c$, and write $d_c=\dim_{\mathbb{C}}S_c$ for its degree and $\chi_c(g)=\operatorname{tr}\pi_c(g)$ for its character.
--
--   1. **Small-type kernel.** For a real number $R$, the small-type kernel $k_R\colon G\to\mathbb{C}$ is the sum of the central character kernels of all irreducible types of degree at most $R$:
--
--   $$
--   k_R(g)=\sum_{\substack{c\in\operatorname{Irr}(G)\\ d_c\le R}}\frac{d_c}{|G|}\,\chi_c(g^{-1})\qquad(g\in G).
--   $$
--
--   2. **Hilbert–Schmidt norm of the identity.** For a finite-dimensional complex inner product space $V$, with $\|A\|_{\mathrm{HS}}^2=\operatorname{Re}\operatorname{tr}(A^*A)$ for $A\in\operatorname{End}_{\mathbb{C}}(V)$ and $A^*$ the adjoint, one has $\|I_V\|_{\mathrm{HS}}^2=\dim V$.
--
--   Because each central character kernel acts as the identity on its own irreducible type and as zero on all others, the Fourier transform $\sum_g k_R(g)\rho(g)$ at an irreducible representation $\rho$ is $I$ when $\dim\rho\le R$ and $0$ otherwise. Thus $k_R$ is the central idempotent that cuts out the small-degree part of a representation, used to split Fourier transforms into small-degree and large-degree contributions.
--
--   **Formalization Note** The kernel is `smallTypeKernel G R`, where the degree `irreducibleDegree c` is cast to $\mathbb{R}$ for the comparison with $R$ and each summand is `centralCharacterKernel (irreducibleRep c)`. Item 2 is the simp lemma `hsNormSq_one` for the base definition `hsNormSq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/SmallKernels.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/SmallKernels.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
noncomputable section
variable {G : Type*} [Group G] [Fintype G]

def smallTypeKernel (G : Type*) [Group G] [Fintype G] (R : ℝ) : G → ℂ :=
  fun g => ∑ c : IrreducibleIndex G,
    if (irreducibleDegree c : ℝ) ≤ R then centralCharacterKernel (irreducibleRep c) g else 0

@[simp] lemma hsNormSq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] : hsNormSq (1 : Module.End ℂ V) = Module.finrank ℂ V := by
  simp [hsNormSq, LinearMap.trace_one]

end
end PartialPermutation

end

end OAI


