-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtShapes
-- name    : OAI_RepresentationTheory_PartialPermutation_SpechtShapes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:08:49.807847+00:00
-- url     : https://prove2.me/theorems/192a64cd-619e-488b-91d0-1fed3bd3f088
-- title:
--   Specht modules of different shapes are non-isomorphic
-- statement:
--   This file proves that a Specht module determines its Young diagram: an equivariant linear isomorphism between the Specht modules of $\mu$ and $\nu$, taken with respect to any bijection between their cells, forces $\mu=\nu$.
--
--   **Setting.** For a Young diagram $\mu$, regarded as a finite set $[\mu]\subset\mathbb{N}\times\mathbb{N}$ of cells $(i,j)$ (row $i$, column $j$, counted from $0$) closed under decreasing either coordinate, the tabloids of shape $\mu$ are the maps $r=\operatorname{row}\circ p:[\mu]\to\mathbb{N}$ with $p$ a permutation of $[\mu]$, on which $\mathrm{Sym}([\mu])$ acts by $g\cdot r=r\circ g^{-1}$; $M^\mu$ is the space of complex functions on tabloids with $(\rho_\mu(g)f)(r)=f(g^{-1}\cdot r)$; $C_\mu$ is the column group of permutations of $[\mu]$ preserving the column of every cell; $e_\mu=\sum_{c\in C_\mu}\operatorname{sgn}(c)\,\rho_\mu(c)\,\delta_{r_0}$ is the polytabloid, where $\delta_{r_0}$ is the indicator of the canonical tabloid $r_0=\operatorname{row}$; and $S^\mu=\operatorname{span}_{\mathbb{C}}\{\rho_\mu(g)e_\mu: g\in\mathrm{Sym}([\mu])\}$ is the Specht module, with the restricted action. The row moment is $n(\mu)=\sum_{x\in[\mu]}\operatorname{row}(x)$. Let $\nu$ be a second Young diagram and $e:[\mu]\to[\nu]$ a bijection, which transports permutations by $g\mapsto ege^{-1}$. A linear map $L:S^\mu\to S^\nu$ is called $e$-equivariant if
--   $$
--   L(\rho_\mu(g)x)=\rho_\nu(ege^{-1})\,L(x)\qquad\text{for all } g\in\mathrm{Sym}([\mu]) \text{ and } x\in S^\mu .
--   $$
--
--   1. **Sign action on the polytabloid.** $\rho_\mu(c)\,e_\mu=\operatorname{sgn}(c)\,e_\mu$ for every $c\in C_\mu$.
--
--   2. **A transversal tabloid.** If $L:S^\mu\to S^\nu$ is linear, injective and $e$-equivariant, then there is a tabloid $r$ of shape $\nu$ such that $r\circ e$ is injective on every column of $\mu$: $\operatorname{col}(x)=\operatorname{col}(y)$ and $r(e(x))=r(e(y))$ imply $x=y$.
--
--   3. **Moment inequality.** Under the hypotheses of item 2, $n(\mu)\le n(\nu)$.
--
--   4. **Shapes are determined.** If $L:S^\mu\to S^\nu$ is a linear isomorphism that is $e$-equivariant, then $\mu=\nu$.
--
--   Applied with bijections from the cells of each diagram onto a common set of $n$ letters, item 4 says that Specht modules of distinct Young diagrams with $n$ cells are non-isomorphic representations of the symmetric group $S_n$. This is the injectivity half of the classification of the irreducible representations of $S_n$ by Young diagrams.
--
--   **Formalization Note** The equivariance hypothesis is written with `e.permCongrHom g`, the permutation $z\mapsto e(g(e^{-1}(z)))$ of $[\nu]$, and $\rho_\mu$ on $S^\mu$ is `spechtRep μ`. Items 1 to 4 are `polytabloid_specht_sign`, `cross_transversal_of_specht_map`, `specht_map_rowMoment_le` and `specht_equiv_shape_eq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/SpechtShapes.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/SpechtShapes.lean by skeleton subtraction
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
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_IsotypicKernels
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Equivalences
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SymmetricTransfer
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RankFillings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_FillingExtensions
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Interleavings
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_RowBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Truncation
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagramCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DeficitCounts
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Tabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnSorting
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_AlternatingTabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_Polytabloids
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_SpechtModules
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_ColumnRearrangement
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauVectors
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_CrossTableaux

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

lemma polytabloid_specht_sign (μ : YoungDiagram) (c : columnGroup μ) :
    spechtRep μ c.1 ⟨polytabloid μ,polytabloid_mem_specht μ⟩ =
      signC c.1 • (⟨polytabloid μ,polytabloid_mem_specht μ⟩ : (spechtSub μ).toSubmodule) := by
  apply Subtype.ext
  apply PiLp.ext
  intro r
  change polytabloid μ (relabel μ c.1⁻¹ r)=signC c.1 * polytabloid μ r
  simpa using polytabloid_alternating μ c⁻¹ r

lemma cross_transversal_of_specht_map (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (L : (spechtSub μ).toSubmodule →ₗ[ℂ] (spechtSub ν).toSubmodule)
    (hL : Function.Injective L)
    (hcomm : ∀ g x, L (spechtRep μ g x)=spechtRep ν (e.permCongrHom g) (L x)) :
    ∃ r : Tabloid ν, CrossTransversal μ (fun x => r.1 (e x)) := by
  let v : (spechtSub μ).toSubmodule := ⟨polytabloid μ,polytabloid_mem_specht μ⟩
  have hv : v≠0 := fun h => polytabloid_ne_zero μ (congrArg Subtype.val h)
  have hf : (L v).val ≠ 0 := by
    intro h
    exact hv (hL (by simpa using (show L v=0 from Subtype.ext h)))
  obtain ⟨r,hr⟩ : ∃ r : Tabloid ν, (L v).val r≠0 := by
    by_contra hh
    push Not at hh
    exact hf (PiLp.ext hh)
  refine ⟨r,?_⟩
  intro x y hc he
  by_contra hxy
  let c : columnGroup μ := ⟨Equiv.swap x y,swap_mem_column μ x y hc⟩
  have hsg : signC c.1 = -1 := signC_swap x y hxy
  have hswap : e.permCongrHom c.1=Equiv.swap (e x) (e y) := by
    apply Equiv.ext
    intro z
    change e (Equiv.swap x y (e.symm z))=Equiv.swap (e x) (e y) z
    by_cases hx : e.symm z=x
    · have hz : z=e x := by simpa using congrArg e hx
      simp [hz]
    by_cases hy : e.symm z=y
    · have hz : z=e y := by simpa using congrArg e hy
      simp [hz]
    have hx' : z≠e x := by intro h; exact hx (by simp [h])
    have hy' : z≠e y := by intro h; exact hy (by simp [h])
    simp [Equiv.swap_apply_of_ne_of_ne hx hy,Equiv.swap_apply_of_ne_of_ne hx' hy']
  have h := hcomm c.1 v
  rw [polytabloid_specht_sign,map_smul,hsg,hswap] at h
  have hh := congrArg (fun w : (spechtSub ν).toSubmodule => w.val r) h
  change (-1 : ℂ) * (L v).val r = (L v).val (relabel ν (Equiv.swap (e x) (e y))⁻¹ r) at hh
  rw [Equiv.swap_inv,relabel_swap_fix ν r (e x) (e y) he] at hh
  apply hr
  linear_combination -hh / 2

lemma specht_map_rowMoment_le (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (L : (spechtSub μ).toSubmodule →ₗ[ℂ] (spechtSub ν).toSubmodule)
    (hL : Function.Injective L)
    (hcomm : ∀ g x, L (spechtRep μ g x)=spechtRep ν (e.permCongrHom g) (L x)) :
    rowMoment μ ≤ rowMoment ν := by
  obtain ⟨r,hr⟩ := cross_transversal_of_specht_map μ ν e L hL hcomm
  exact cross_rowMoment_le μ ν e r hr

theorem specht_equiv_shape_eq (μ ν : YoungDiagram) (e : μ.cells ≃ ν.cells)
    (L : (spechtSub μ).toSubmodule ≃ₗ[ℂ] (spechtSub ν).toSubmodule)
    (hcomm : ∀ g x, L (spechtRep μ g x)=spechtRep ν (e.permCongrHom g) (L x)) : μ=ν := by
  have hrev : ∀ g x, L.symm (spechtRep ν g x)=spechtRep μ (e.symm.permCongrHom g) (L.symm x) := by
    intro g x
    apply L.injective
    have he : e.permCongrHom (e.symm.permCongrHom g)=g := e.permCongrHom.apply_symm_apply g
    simpa only [he,L.apply_symm_apply] using (hcomm (e.symm.permCongrHom g) (L.symm x)).symm
  have hm := le_antisymm (specht_map_rowMoment_le μ ν e L.toLinearMap L.injective hcomm)
    (specht_map_rowMoment_le ν μ e.symm L.symm.toLinearMap L.symm.injective hrev)
  obtain ⟨r,hr⟩ := cross_transversal_of_specht_map μ ν e L.toLinearMap L.injective hcomm
  exact cross_equal_moment_shape_eq μ ν e r hr hm

end
end PartialPermutation.YoungTabloid

end

end OAI


