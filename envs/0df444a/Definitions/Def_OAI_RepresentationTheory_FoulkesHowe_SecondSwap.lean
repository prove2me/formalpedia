-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap
-- name    : OAI_RepresentationTheory_FoulkesHowe_SecondSwap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T16:15:20.073263+00:00
-- url     : https://prove2.me/theorems/cb7d018d-cb75-46dd-822e-e940fa2cf4dc
-- title:
--   Transposing two factor positions within a single row
-- statement:
--   Fix $r,b\in\mathbb{N}$, and index the rows of a grid of slots by $0\le a\le r$ and the factor positions by $0\le j<b$. For a row $i$ with $1\le i\le r$ and two positions $j,l<b$, the module defines the family of permutations of the factor positions, one for each row,
--   $$
--   \rho_{i,j,l}(a)=\begin{cases}(j\ l)&\text{if } a=i,\\ \mathrm{id}&\text{if } a\ne i,\end{cases}\qquad 0\le a\le r,
--   $$
--   where $(j\ l)$ is the transposition of $j$ and $l$ in the symmetric group on $\{0,\dots,b-1\}$ (the identity when $j=l$).
--
--   Applying $\rho_{i,j,l}$ to a grid exchanges two factors of row $i$ and leaves all other rows untouched. Because each row of the grid is turned into a monomial in a symmetric power, such a permutation does not change the value of a flattened form. It is used to show that relabelling one slot of row $i$ to the common block of the second transfer gives, up to this permutation, the labelling in which the count of row $i$ is increased by one.
--
--   **Formalization Note** `rowFactorSwap i j l` takes `i : Fin r` and is a function from `Fin (r+1)` to permutations of `Fin b`, equal to `Equiv.swap j l` at the row `i.succ` and to the identity elsewhere; Lean's row `i.succ` is the row $i$ with $1\le i\le r$ in the notation above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SecondSwap.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SecondSwap.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels

namespace OAI

noncomputable section
namespace Problem346.SecondTransfer

/-- Swap two factor positions in one nonzero row, leaving all other rows fixed. -/
def rowFactorSwap {r b : ℕ} (i : Fin r) (j l : Fin b) :
    Fin (r+1) → Equiv.Perm (Fin b) :=
  fun a => if a = i.succ then Equiv.swap j l else Equiv.refl _

end Problem346.SecondTransfer

end

end OAI


