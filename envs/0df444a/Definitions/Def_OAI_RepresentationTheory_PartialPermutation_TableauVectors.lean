-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauVectors
-- name    : OAI_RepresentationTheory_PartialPermutation_TableauVectors
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:04:39.235003+00:00
-- url     : https://prove2.me/theorems/6e7187dd-88e9-4873-95fe-c30ea995f10f
-- title:
--   Standard Young tableaux, their tabloids and standard polytabloids
-- statement:
--   This file attaches to every standard Young tableau of shape $\mu$ a permutation of the cells, a tabloid and a polytabloid vector, and introduces a numerical score of tabloids.
--
--   **Setting.** Throughout, $\mu$ is a Young diagram, regarded as a finite set $[\mu]\subset\mathbb{N}\times\mathbb{N}$ of cells $(i,j)$ (row $i$, column $j$, both counted from $0$) that is closed under decreasing either coordinate. Write $\operatorname{row}(i,j)=i$ and $\operatorname{col}(i,j)=j$, let $\mu_i$ be the length of row $i$, and put $n=|[\mu]|$. The cells serve both as positions in the diagram and as the $n$ letters permuted by the symmetric group $\mathrm{Sym}([\mu])$. A *tabloid* of shape $\mu$ is a map $r:[\mu]\to\mathbb{N}$ of the form $r=\operatorname{row}\circ p$ for some $p\in\mathrm{Sym}([\mu])$: it places each letter $x$ in row $r(x)$, and row $i$ receives exactly $\mu_i$ letters. Let $\mathrm{Tab}(\mu)$ be the (finite) set of tabloids. The *canonical tabloid* is $r_0=\operatorname{row}$ (each letter sits in its own row), and a permutation $g$ acts on tabloids by $g\cdot r=r\circ g^{-1}$. The *column group* $C_\mu$ is the subgroup of permutations $c\in\mathrm{Sym}([\mu])$ with $\operatorname{col}(c(x))=\operatorname{col}(x)$ for every cell $x$, i.e. those that move each letter only within its own column. $M^\mu$ is the space of complex functions on $\mathrm{Tab}(\mu)$ with the inner product $\langle f,h\rangle=\sum_{r}\overline{f(r)}\,h(r)$ and the unitary representation $(\rho_\mu(g)f)(r)=f(g^{-1}\cdot r)$ of $\mathrm{Sym}([\mu])$; $\delta_r\in M^\mu$ is the indicator function of the single tabloid $r$; $A_\mu=\sum_{c\in C_\mu}\operatorname{sgn}(c)\,\rho_\mu(c)$ is the column antisymmetrizer (with $\operatorname{sgn}$ the sign of a permutation, as a complex number); and $e_\mu=A_\mu\delta_{r_0}$ is the polytabloid.
--
--   1. **Standard tableaux.** $\mathrm{Std}(\mu)$ is the set of bijections $t:[\mu]\to\{0,1,\dots,n-1\}$ that are strictly increasing for the componentwise order on cells ($(i,j)\le(i',j')$ iff $i\le i'$ and $j\le j'$); these are the standard Young tableaux of shape $\mu$ filled with $0,\dots,n-1$, whose entries increase along every row and down every column.
--
--   2. **Reference labels.** A fixed bijection $\ell:[\mu]\to\{0,1,\dots,n-1\}$, an arbitrary enumeration of the cells used to identify the numbers written in a tableau with letters.
--
--   3. **Permutation of a tableau.** For $t\in\mathrm{Std}(\mu)$, $\sigma_t=\ell^{-1}\circ t\in\mathrm{Sym}([\mu])$; it sends a cell $x$ to the letter whose reference number is the entry $t(x)$.
--
--   4. **Tabloid of a tableau.** $\{t\}=\sigma_t\cdot r_0$, that is, $\{t\}(y)=\operatorname{row}\bigl(t^{-1}(\ell(y))\bigr)$: the letter $y$ is placed in the row of the cell in which $t$ writes the number $\ell(y)$.
--
--   5. **Standard polytabloid.** $e_t=\rho_\mu(\sigma_t)\,e_\mu\in M^\mu$, the translate of the polytabloid by $\sigma_t$; it belongs to the Specht module $\operatorname{span}\{\rho_\mu(g)e_\mu\}$.
--
--   6. **Row cells.** For $i\in\mathbb{N}$ and $j<\mu_i$, the cell $(i,j)$ regarded as an element of $[\mu]$, i.e. the $j$-th cell of row $i$.
--
--   7. **Score.** For a tabloid $r$,
--   $$
--   \operatorname{score}(r)=\sum_{x\in[\mu]}\ell(x)\,r(x)\in\mathbb{N},
--   $$
--   the sum of the rows of all letters, weighted by their reference numbers.
--
--   These are the ingredients of the standard lower bound for the dimension of a Specht module: the vectors $e_t$, $t\in\mathrm{Std}(\mu)$, are linearly independent by a triangularity argument in which the score orders the tabloids, so the dimension of the Specht module is at least the number of standard Young tableaux of shape $\mu$.
--
--   **Formalization Note** $\mathrm{Std}(\mu)$ is `Std μ`, an abbreviation for `Tableau.StandardFilling μ.cells`, where the cells carry the product order of $\mathbb{N}\times\mathbb{N}$. The enumeration $\ell$ is `referenceLabels μ`, chosen by `Fintype.equivFin`, so no particular enumeration is intended. The remaining objects are `tableauPerm`, `tableauTabloid`, `tableauVector`, `rowCell` and `score`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/TableauVectors.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/TableauVectors.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation.YoungTabloid
noncomputable section
open Finset
open scoped Classical

abbrev Std (μ : YoungDiagram) := Tableau.StandardFilling μ.cells

def referenceLabels (μ : YoungDiagram) : μ.cells ≃ Fin (Fintype.card μ.cells) := Fintype.equivFin _
def tableauPerm (μ : YoungDiagram) (t : Std μ) : Equiv.Perm μ.cells :=
  t.1.trans (referenceLabels μ).symm
def tableauTabloid (μ : YoungDiagram) (t : Std μ) : Tabloid μ :=
  relabel μ (tableauPerm μ t) (canonical μ)
def tableauVector (μ : YoungDiagram) (t : Std μ) : EuclideanSpace ℂ (Tabloid μ) :=
  tabloidRep μ (tableauPerm μ t) (polytabloid μ)

def rowCell (μ : YoungDiagram) (i : ℕ) (j : Fin (μ.rowLen i)) : μ.cells :=
  ⟨(i,j),μ.mem_iff_lt_rowLen.mpr j.2⟩

def score (μ : YoungDiagram) (r : Tabloid μ) : ℕ :=
  ∑ x, ((referenceLabels μ) x).val * r.1 x

end
end PartialPermutation.YoungTabloid
end

end OAI


