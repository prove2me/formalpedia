-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
-- name    : OAI_RepresentationTheory_PartialPermutation_DiagonalBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:28:39.965102+00:00
-- url     : https://prove2.me/theorems/681ace00-5576-4531-9795-bcfd4c6e56e9
-- title:
--   Anti-diagonal indices and the anti-diagonal rank of the cells of a Young diagram
-- statement:
--   Let $\mu$ be a Young diagram, viewed as a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$, both indexed from $0$) that is closed downwards for the componentwise order $(i',j')\le(i,j)\iff i'\le i\text{ and }j'\le j$. The cell $(i,j)$ lies on the anti-diagonal with index $i+j$.
--
--   1. **Anti-diagonal index set.** The set of anti-diagonals met by $\mu$ is
--   $$
--   D(\mu)=\{\,i+j : (i,j)\in\mu\,\}\subseteq\mathbb{N}.
--   $$
--   2. **Anti-diagonal rank.** The map $\delta_\mu:\mu\to D(\mu)$, $\delta_\mu(i,j)=i+j$, sends each cell to the index of its anti-diagonal.
--
--   The rank $\delta_\mu$ is strictly monotone on the poset of cells, and its fibres are the anti-diagonals of $\mu$, so it is a rank function to which the fibrewise-permutation count of standard fillings applies. Writing $f^\mu$ for the number of standard Young tableaux of shape $\mu$ (strictly increasing bijections from the cells onto $\{0,\dots,|\mu|-1\}$) and $d_k$ for the number of cells on anti-diagonal $k$, this yields $f^\mu\ge\prod_{k\in D(\mu)}d_k!$ and hence $f^\mu\ge2^{|\mu|-|D(\mu)|}$; together with $|D(\mu)|\le2m(\mu)-1$, where $m(\mu)$ is the length of a longest row or column, it gives the exponential lower bound $f^\mu\ge2^{|\mu|-(2m(\mu)-1)}$ (natural-number subtraction, truncated at $0$).
--
--   **Formalization Note** `diagonalIndices μ` is the `Finset ℕ` image of `μ.cells` under $(i,j)\mapsto i+j$, and `diagonalRank μ` takes values in the subtype of this finset, so that it is a map into a finite linear order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/DiagonalBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/DiagonalBounds.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def diagonalIndices (μ : YoungDiagram) : Finset ℕ := μ.cells.image (fun x => x.1+x.2)

def diagonalRank (μ : YoungDiagram) (x : μ.cells) : diagonalIndices μ :=
  ⟨x.1.1+x.1.2, Finset.mem_image.mpr ⟨x.1,x.2,rfl⟩⟩

end
end Tableau
end PartialPermutation
end

end OAI


