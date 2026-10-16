-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_AlternatingTabloids
-- name    : OAI_RepresentationTheory_PartialPermutation_AlternatingTabloids
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:55:17.447301+00:00
-- url     : https://prove2.me/theorems/7e626078-8c1a-4be5-a26b-ecbdbf0ddd73
-- title:
--   Column-alternating functions on tabloids are determined by their value at the canonical tabloid
-- statement:
--   This file introduces the complex-valued sign of a permutation and the column-alternating functions on tabloids, and shows that such a function vanishes off the transversal tabloids and is determined by its value at the canonical tabloid.
--
--   **Setting.** Throughout, $\mu$ is a Young diagram, regarded as a finite set $[\mu]\subset\mathbb{N}\times\mathbb{N}$ of cells $(i,j)$ (row $i$, column $j$, both counted from $0$) that is closed under decreasing either coordinate. Write $\operatorname{row}(i,j)=i$ and $\operatorname{col}(i,j)=j$, let $\mu_i$ be the length of row $i$, and put $n=|[\mu]|$. The cells serve both as positions in the diagram and as the $n$ letters permuted by the symmetric group $\mathrm{Sym}([\mu])$. A *tabloid* of shape $\mu$ is a map $r:[\mu]\to\mathbb{N}$ of the form $r=\operatorname{row}\circ p$ for some $p\in\mathrm{Sym}([\mu])$: it places each letter $x$ in row $r(x)$, and row $i$ receives exactly $\mu_i$ letters. Let $\mathrm{Tab}(\mu)$ be the (finite) set of tabloids. The *canonical tabloid* is $r_0=\operatorname{row}$ (each letter sits in its own row), and a permutation $g$ acts on tabloids by $g\cdot r=r\circ g^{-1}$. The *column group* $C_\mu$ is the subgroup of permutations $c\in\mathrm{Sym}([\mu])$ with $\operatorname{col}(c(x))=\operatorname{col}(x)$ for every cell $x$, i.e. those that move each letter only within its own column. A tabloid $r$ is *transversal* if distinct letters of the same column lie in distinct rows: $\operatorname{col}(x)=\operatorname{col}(y)$ and $r(x)=r(y)$ imply $x=y$.
--
--   1. **Complex sign.** For a permutation $g$ of a finite set, its sign $\operatorname{sgn}(g)\in\{1,-1\}$ is regarded as a complex number. It satisfies $\operatorname{sgn}(1)=1$, $\operatorname{sgn}(gh)=\operatorname{sgn}(g)\operatorname{sgn}(h)$, $\operatorname{sgn}(g^{-1})=\operatorname{sgn}(g)$, $\operatorname{sgn}(g)^2=1$, and $\operatorname{sgn}((x\,y))=-1$ for every transposition $(x\,y)$ with $x\neq y$.
--
--   2. **Alternating functions.** A function $f:\mathrm{Tab}(\mu)\to\mathbb{C}$ is *alternating* if
--   $$
--   f(c\cdot r)=\operatorname{sgn}(c)\,f(r)\qquad\text{for all } c\in C_\mu \text{ and all } r\in\mathrm{Tab}(\mu).
--   $$
--
--   3. **Transpositions.** If $\operatorname{col}(x)=\operatorname{col}(y)$, the transposition $(x\,y)$ lies in $C_\mu$; if a tabloid $r$ satisfies $r(x)=r(y)$, then $(x\,y)\cdot r=r$.
--
--   4. **Vanishing.** Every alternating function vanishes at every tabloid that is not transversal.
--
--   5. **Transversal tabloids.** The map $C_\mu\to\mathrm{Tab}(\mu)$, $c\mapsto c\cdot r_0$, is injective, and every transversal tabloid equals $c\cdot r_0$ for some $c\in C_\mu$.
--
--   6. **Uniqueness.** If $f$ and $g$ are alternating and $f(r_0)=g(r_0)$, then $f=g$. In particular, evaluation at $r_0$ is injective on the vector space of alternating functions, which therefore has dimension at most one.
--
--   These statements are the combinatorial core of the tabloid construction of Specht modules. The polytabloid of shape $\mu$ is the alternating function with value $1$ at $r_0$, and the uniqueness statement is what makes the signed column sum $\sum_{c\in C_\mu}\operatorname{sgn}(c)\,c$ act as a rank-one operator on functions of tabloids, the key step towards the irreducibility of Specht modules.
--
--   **Formalization Note** Tabloids form the subtype `Tabloid μ` of functions from the cells to $\mathbb{N}$; the action is `relabel`, the canonical tabloid is `canonical`, the column group is `columnGroup μ` and transversality is `Transversal` (all from earlier files). The complex sign is `signC`, alternation is `Alternating`, and items 3 to 6 are `swap_mem_column`, `relabel_swap_fix`, `alternating_zero_nontransversal`, `column_canonical_injective`, `transversal_column_orbit` and `alternating_eq_of_canonical_eq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/AlternatingTabloids.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/AlternatingTabloids.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

def signC {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) : ℂ :=
  (Equiv.Perm.sign g : ℤ)

@[simp] lemma signC_one {α : Type*} [Fintype α] [DecidableEq α] : signC (1 : Equiv.Perm α)=1 := by
  simp [signC]
@[simp] lemma signC_mul {α : Type*} [Fintype α] [DecidableEq α] (g h : Equiv.Perm α) :
    signC (g*h)=signC g*signC h := by simp [signC]
@[simp] lemma signC_inv {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    signC g⁻¹=signC g := by simp [signC]
@[simp] lemma signC_sq {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    signC g*signC g=1 := by
  simpa using (signC_mul g g⁻¹).symm
@[simp] lemma signC_swap {α : Type*} [Fintype α] [DecidableEq α] (x y : α) (h : x≠y) :
    signC (Equiv.swap x y) = -1 := by simp [signC,Equiv.Perm.sign_swap h]

lemma swap_mem_column (μ : YoungDiagram) (x y : μ.cells) (h : col μ x=col μ y) :
    Equiv.swap x y ∈ columnGroup μ := by
  intro z
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

lemma relabel_swap_fix (μ : YoungDiagram) (r : Tabloid μ) (x y : μ.cells)
    (h : r.1 x=r.1 y) : relabel μ (Equiv.swap x y) r=r := by
  apply Subtype.ext
  funext z
  change r.1 ((Equiv.swap x y)⁻¹ z)=r.1 z
  rw [Equiv.swap_inv]
  by_cases hx : z=x
  · subst z; simpa using h.symm
  by_cases hy : z=y
  · subst z; simpa using h
  simp [Equiv.swap_apply_of_ne_of_ne hx hy]

def Alternating (μ : YoungDiagram) (f : Tabloid μ → ℂ) : Prop :=
  ∀ (c : columnGroup μ) r, f (relabel μ c r)=signC c.1*f r

lemma alternating_zero_nontransversal (μ : YoungDiagram) (f : Tabloid μ → ℂ)
    (hf : Alternating μ f) (r : Tabloid μ) (hr : ¬Transversal μ r) : f r=0 := by
  simp only [Transversal,not_forall] at hr
  obtain ⟨x,y,h⟩ := hr
  obtain ⟨hc,he,hne⟩ := h
  have hz := hf ⟨Equiv.swap x y,swap_mem_column μ x y hc⟩ r
  change f (relabel μ (Equiv.swap x y) r)=signC (Equiv.swap x y)*f r at hz
  rw [relabel_swap_fix μ r x y he] at hz
  erw [signC_swap x y hne] at hz
  linear_combination hz / 2

lemma column_canonical_injective (μ : YoungDiagram) :
    Function.Injective (fun c : columnGroup μ => relabel μ c (canonical μ)) := by
  intro c d h
  have h' : c⁻¹=d⁻¹ := column_row_injective μ (congrArg Subtype.val h)
  exact inv_injective h'

lemma transversal_column_orbit (μ : YoungDiagram) (r : Tabloid μ) (hr : Transversal μ r) :
    ∃ c : columnGroup μ, r=relabel μ c (canonical μ) := by
  obtain ⟨c,hc⟩ := transversal_eq_column μ r hr
  refine ⟨c⁻¹,Subtype.ext ?_⟩
  change r.1 = fun x => row μ ((c.1⁻¹)⁻¹ x)
  simpa only [inv_inv] using hc

lemma alternating_eq_of_canonical_eq (μ : YoungDiagram) (f g : Tabloid μ → ℂ)
    (hf : Alternating μ f) (hg : Alternating μ g) (h : f (canonical μ)=g (canonical μ)) :
    f=g := by
  funext r
  by_cases hr : Transversal μ r
  · obtain ⟨c,rfl⟩ := transversal_column_orbit μ r hr
    rw [hf,hg,h]
  · rw [alternating_zero_nontransversal μ f hf r hr,
      alternating_zero_nontransversal μ g hg r hr]

end
end YoungTabloid
end PartialPermutation
end

end OAI


