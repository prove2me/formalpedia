-- Prove2me | Definitions.Def_OAI_RepresentationTheory_PartialPermutation_TailBounds
-- name    : OAI_RepresentationTheory_PartialPermutation_TailBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:40:28.445224+00:00
-- url     : https://prove2.me/theorems/eab0ff08-a4d4-4871-9ada-3a6c6520db55
-- title:
--   Transposition as an order isomorphism between the cells of a Young diagram and of its conjugate
-- statement:
--   Let $\mu$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}\times\mathbb{N}$ (row $i$, column $j$) closed downwards for the componentwise order $(i',j')\le(i,j)\iff i'\le i\text{ and }j'\le j$, and let $\mu^{t}=\{(j,i) : (i,j)\in\mu\}$ be its transpose (conjugate) diagram, the reflection of $\mu$ in the main diagonal. The swap map
--
--   $$
--   \tau_\mu:\mu\to\mu^{t},\qquad \tau_\mu(i,j)=(j,i),
--   $$
--
--   is an order isomorphism between the cells of $\mu$ and the cells of $\mu^{t}$, both ordered componentwise: $\tau_\mu$ is a bijection and $\tau_\mu(x)\le\tau_\mu(y)$ if and only if $x\le y$.
--
--   Transporting standard fillings along $\tau_\mu$ shows that $\mu$ and $\mu^{t}$ have the same number $f^\mu=f^{\mu^t}$ of standard Young tableaux (strictly increasing bijections from the cells onto $\{0,\dots,|\mu|-1\}$). Transposition exchanges row and column lengths, so it also preserves the deficit $d(\mu)=|\mu|-\max(r_0,c_0)$, where $r_0$ and $c_0$ are the lengths of the first row and the first column. This symmetry allows the tail lower bound $2^{\lfloor d(\mu)/8\rfloor}\le f^\mu$ to be proved only for diagrams whose first row is at least as long as their first column.
--
--   **Formalization Note** `transposeCellsEquiv μ` is an `OrderIso` from `μ.cells` to `μ.transpose.cells`, the only definition of this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/PartialPermutation/TailBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/PartialPermutation/TailBounds.lean by skeleton subtraction
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

namespace OAI

section
namespace PartialPermutation
namespace Tableau
noncomputable section
open Finset

def transposeCellsEquiv (μ : YoungDiagram) : μ.cells ≃o μ.transpose.cells where
  toFun x := ⟨x.1.swap, by simpa only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose,
    Prod.swap_swap] using x.2⟩
  invFun x := ⟨x.1.swap, YoungDiagram.mem_transpose.mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intro x y; exact ⟨fun h => ⟨h.2,h.1⟩,fun h => ⟨h.2,h.1⟩⟩

end
end Tableau
end PartialPermutation

end

end OAI


