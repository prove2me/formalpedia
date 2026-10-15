-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree
-- name    : OAI_Combinatorics_BooleanFunctions_CellDegree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:38:03.515011+00:00
-- url     : https://prove2.me/theorems/5167aae1-bab5-4a59-b72e-75009dd2a06a
-- title:
--   Label tuples and switched observations assembled from blocks of a Boolean cube
-- statement:
--   Let $\Gamma$ be a finite coordinate set, $B$ a finite label set and $I$ a finite index set (the leaves), and let $\Sigma:B\to I$ and $L_i:B\to\mathbb{B}$ be a selector table and leaf tables with the table event of the rounding file.
--
--   1. **Label tuple.** For observations $F_0,F_i:\mathbb{B}^\Gamma\to B$ ($i\in I$), $\mathrm{tup}(x)=\big(F_0(x),(F_i(x))_{i\in I}\big)$.
--   2. **Switched observation on one cube.** For a further observation $F_\ast:\mathbb{B}^\Gamma\to B$,
--   $$\mathrm{obs}(x)=\begin{cases}\mathrm{inr}\,F_\ast(x)&\text{if the table event of }(\Sigma,L)\text{ holds at }\mathrm{tup}(x),\\ \mathrm{inl}\,\mathrm{tup}(x)&\text{otherwise.}\end{cases}$$
--   3. **Block decomposition.** The bijection between $\mathbb{B}^{\mathrm{Slots}(I)\times\Gamma}$ and $\mathrm{Full}(\mathbb{B}^\Gamma,I)$ obtained by currying the cube into the blocks indexed by $\mathrm{Slots}(I)=I\sqcup\{\mathrm{sel},\ast\}$ and arranging them as (selector block, leaf blocks, spare block).
--   4. **Switched observation.** For $F:\mathbb{B}^\Gamma\to B$, the map
--   $$\mathrm{sw}_{F,\Sigma,L}:\mathbb{B}^{\mathrm{Slots}(I)\times\Gamma}\to\big(B\times B^I\big)\sqcup B$$
--   that applies $F$ to every block and then the switching rule: if the labels of the selector block and of the leaf blocks satisfy the table event, it reveals only the label of the spare block; otherwise it reveals the labels of the selector and leaf blocks.
--
--   The switched observation, applied to a grouped observation, is the new observation produced by one amplification step. Its single-cube form with separate observations $F_0$, $F_\ast$ and $F_i$ is what lets its cells be written as products of cells of block observations, so that their Fourier degree is controlled by the degrees of the cells of $F$.
--
--   **Formalization Note** The Lean names are `CellDegree.labelTuple`, `CellDegree.observationOn`, `Observations.fullCubeEquiv` (the composition of `blockCurry` and `Switching.fullEquiv`) and `Observations.switched`, which is `Switching.observation F (TableRounding.tableEvent S L)` precomposed with `fullCubeEquiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/CellDegree.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/CellDegree.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SquareRootDegree mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace CellDegree
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]

def labelTuple (F₀ : Cube γ → β) (F : ι → Cube γ → β) (x : Cube γ) : β × (ι → β) :=
  (F₀ x,fun i => F i x)

def observationOn (F₀ Fw : Cube γ → β) (F : ι → Cube γ → β)
    (S : β → ι) (L : ι → β → Bool) (x : Cube γ) : (β × (ι → β)) ⊕ β :=
  if TableRounding.tableEvent S L (labelTuple F₀ F x) then Sum.inr (Fw x) else Sum.inl (labelTuple F₀ F x)

end CellDegree
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
open Switching
attribute [local instance] Classical.propDecidable
variable {γ β ι : Type*} [Fintype γ] [Fintype β] [Fintype ι]
  [DecidableEq γ] [DecidableEq ι]

def fullCubeEquiv (γ ι : Type*) : Cube (Slots ι × γ) ≃ FullSpace (Cube γ) ι :=
  (blockCurry (Slots ι) γ Bool).trans (fullEquiv (Cube γ) ι)

def switched (F : Cube γ → β) (S : β → ι) (L : ι → β → Bool)
    (x : Cube (Slots ι × γ)) : EventSpace β ι ⊕ β :=
  observation F (TableRounding.tableEvent S L) (fullCubeEquiv γ ι x)

end Observations
end SquareRootDegree

end

end OAI


