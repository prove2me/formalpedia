-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
-- name    : OAI_RepresentationTheory_PartialPermutation_ProjectionCovers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:09:14.292954+00:00
-- url     : https://prove2.me/theorems/30f6dc24-8311-4ddd-a466-0013c8c1d393
-- title:
--   Sum of squared degrees of the irreducible types of degree at most $R$
-- statement:
--   Let $G$ be a finite group. Let $\operatorname{Irr}(G)$ be the set of isotypic components of the left regular representation $\lambda$ of $G$ on $\ell^2(G)$ (complex functions on $G$, with $(\lambda(g)f)(h)=f(g^{-1}h)$), regarded as a module over the group algebra $\mathbb{C}[G]$. For $c\in\operatorname{Irr}(G)$ let $S_c\subseteq\ell^2(G)$ be the simple submodule chosen to represent the type of $c$, let $\pi_c$ be the restriction of $\lambda$ to $S_c$, and write $d_c=\dim_{\mathbb{C}}S_c$ for its degree and $\chi_c(g)=\operatorname{tr}\pi_c(g)$ for its character. For a real number $R$, the small-degree sum of $G$ at level $R$ is
--
--   $$
--   D_G(R)=\sum_{\substack{c\in\operatorname{Irr}(G)\\ d_c\le R}}d_c^{\,2}.
--   $$
--
--   Since the $\pi_c$ list every irreducible representation exactly once, $\sum_{c}d_c^2=|G|$, so $D_G(R)$ is the dimension of the part of the regular representation carried by irreducible types of degree at most $R$ and satisfies $0\le D_G(R)\le|G|$. By the Plancherel formula it equals $|G|\sum_{g}|k_R(g)|^2$, where $k_R(g)=\sum_{c:\,d_c\le R}\frac{d_c}{|G|}\chi_c(g^{-1})$ is the kernel selecting the types of degree at most $R$; it therefore measures the $\ell^2$-energy that enters Hilbert–Schmidt bounds for Fourier transforms of functions with coset caps.
--
--   **Formalization Note** The sum is `smallDegreeSum G R`, with degrees `irreducibleDegree c` cast to $\mathbb{R}$. The module also opens a section fixing the hypotheses of a projection cover (a unitary representation and a finite family of self-adjoint operators $P_i$ on $V$ such that every isotypic component space is fixed pointwise by some $P_i$); these hypotheses are used only by lemmas outside this definition file, and the section introduces no further definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/ProjectionCovers.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/ProjectionCovers.lean by skeleton subtraction
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

def smallDegreeSum (G : Type*) [Group G] [Fintype G] (R : ℝ) : ℝ :=
  ∑ c : IrreducibleIndex G, if (irreducibleDegree c : ℝ) ≤ R then
    (irreducibleDegree c : ℝ)^2 else 0

section Cover
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    {ι : Type*} [Fintype ι] (P : ι → Module.End ℂ V)
    (hP : ∀ i, LinearMap.adjoint (P i) = P i)
    (hcover : ∀ c : isotypicComponents ℂ[G] ρ.asModule,
      ∃ i, ∀ x ∈ componentSpace ρ c, P i x = x)

include ρ hρ hP hcover

end Cover
end
end PartialPermutation

end

end OAI


