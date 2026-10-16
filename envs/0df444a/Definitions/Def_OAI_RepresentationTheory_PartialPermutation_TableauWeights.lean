-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TableauWeights
-- name    : OAI_RepresentationTheory_PartialPermutation_TableauWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:46:25.213611+00:00
-- url     : https://prove2.me/theorems/73f68291-79a7-427a-b383-308e18317715
-- title:
--   Sums of negative powers of standard tableau counts over the shapes of size $n$, sorted by deficit
-- statement:
--   For a Young diagram $\mu$ (a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ closed downwards for the componentwise order) let $f^\mu$ be its number of standard Young tableaux, i.e. of strictly increasing bijections from its cells onto $\{0,\dots,|\mu|-1\}$; one always has $f^\mu\ge1$. Let $d(\mu)=|\mu|-\max(r_0(\mu),c_0(\mu))$ be its deficit, where $r_0(\mu)$ and $c_0(\mu)$ are the lengths of the first row and the first column. Write $\mathrm{Shape}(n)$ for the set of diagrams with $n$ cells, $p(n)=|\mathrm{Shape}(n)|$, and $\mathrm{Shape}(n,k)$ for the diagrams in $\mathrm{Shape}(n)$ of deficit $k$. Fix $u\in\mathbb{R}$ and $n,k\in\mathbb{N}$.
--
--   1. **Majorant.**
--   $$
--   M_u(k)=2\,p(k)\,\exp\Bigl(u\log2-\frac{u\log2}{8}\,k\Bigr)=2\,p(k)\,2^{\,u(1-k/8)}.
--   $$
--   2. **Inverse weight.** $w_u(\mu)=0$ if $d(\mu)=0$, and $w_u(\mu)=(f^\mu)^{-u}$ otherwise.
--   3. **Deficit term.** $D_n(u,k)=\sum_{\mu\in\mathrm{Shape}(n,k)}w_u(\mu)$.
--   4. **Nontrivial sum.** $N_n(u)=\sum_{\mu\in\mathrm{Shape}(n)}w_u(\mu)$.
--   5. **Full sum.** $Z_n(u)=\sum_{\mu\in\mathrm{Shape}(n)}(f^\mu)^{-u}$.
--
--   The irreducible representations of the symmetric group $S_n$ are indexed by the shapes $\mu\in\mathrm{Shape}(n)$, the one of shape $\mu$ having degree $f^\mu$, so $Z_n(u)$ is a sum of negative powers of degrees of irreducible representations. The diagrams of deficit $0$ (a single row or a single column) are left out of $N_n(u)$; the remaining shapes are grouped by deficit, $N_n(u)=\sum_k D_n(u,k)$, and for $u>0$ each deficit term is dominated by $M_u(k)$, which is summable in $k$. These objects are the setup for showing that $N_n(u)\to0$ as $n\to\infty$ and that $Z_n(u)$ is bounded uniformly in $n$ for every $u>0$, which bounds the supremum over $n$ of the sums of $(\text{degree})^{-u}$ over irreducible representations of $S_n$.
--
--   **Formalization Note** Items 1 to 5 are `majorant u k`, `inverseWeight u μ`, `deficitTerm n u k`, `nontrivialSum n u` and `fullSum n u`. The powers $(f^\mu)^{-u}$ are real powers (`Real.rpow`) of the natural number `standardCount μ` cast to the reals; the deficit is `deficit μ`, i.e. `μ.cells.card - maxLine μ` with `maxLine μ` the maximum of `μ.rowLen 0` and `μ.colLen 0`; the sums run over the finite types `ShapeDeficit n k` and `Shape n`. The definitions impose no sign condition on $u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/TableauWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/TableauWeights.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace TableauZeta
noncomputable section
open Finset Filter
open Tableau DiagramCounting

def majorant (u : ℝ) (k : ℕ) : ℝ :=
  2*(partitionCount k : ℝ)*Real.exp (u*Real.log 2 - (u*Real.log 2/8)*k)

def inverseWeight (u : ℝ) (μ : YoungDiagram) : ℝ :=
  if deficit μ=0 then 0 else (standardCount μ:ℝ)^(-u)

def deficitTerm (n : ℕ) (u : ℝ) (k : ℕ) : ℝ :=
  ∑ μ : ShapeDeficit n k, inverseWeight u μ.1.1

def nontrivialSum (n : ℕ) (u : ℝ) : ℝ :=
  ∑ μ : Shape n, inverseWeight u μ.1

def fullSum (n : ℕ) (u : ℝ) : ℝ :=
  ∑ μ : Shape n, (standardCount μ.1:ℝ)^(-u)

end
end TableauZeta
end PartialPermutation
end

end OAI


