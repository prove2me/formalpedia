-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping
-- name    : OAI_Combinatorics_BooleanFunctions_Grouping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:38:50.654896+00:00
-- url     : https://prove2.me/theorems/c133ac83-623c-4515-b1c9-a60e66d1e884
-- title:
--   Relabelled event spaces and the standardized score of a grouped observation
-- statement:
--   Use the observations, scores $\operatorname{sc}_F$, variances $V(F)$ and standardized scores $T_F=\operatorname{sc}_F/\sqrt{V(F)}$ of the observations file, the normalized sums of the central-limit file, and the event spaces $E(\Lambda,I)=\Lambda\times\Lambda^I$ of the switching file.
--
--   1. **Relabelling event spaces.** For a bijection $e:\Lambda\to\Delta$ and an index set $I$, the bijection $E(\Lambda,I)\to E(\Delta,I)$ applying $e$ to every component, $(x_0,(x_i)_i)\mapsto(e(x_0),(e(x_i))_i)$.
--   2. **Group scale.** For an observation $F$ on $\mathbb{B}^\Gamma$ and $n\in\mathbb{N}$, $\kappa_{F,n}=\sqrt n\,\sqrt{V(F)}$.
--   3. **Grouped standardized score.** The function on $\mathbb{B}^{[n]\times\Gamma}$
--   $$G_{F,n}(x)=\frac{1}{\sqrt n}\sum_{j=1}^{n}T_F\big(x_{j,\cdot}\big),$$
--   the normalized sum of the standardized score over the $n$ blocks $x_{j,\cdot}$.
--
--   Since the score of the grouped observation $F^{([n])}$ is the sum of the block scores, it equals $\kappa_{F,n}\,G_{F,n}$ when $V(F)>0$ and $n\ge1$. The function $G_{F,n}$ then has mean $0$ and second moment $1$ and, for large $n$, is approximately standard Gaussian; these normalizations link the variance of grouped observations with the central limit theorem.
--
--   **Formalization Note** The Lean names are `Observations.eventCongr`, `groupScale` and `groupStandard`, the latter being `normalizedSum (standard F) n` composed with `blockCurry`; the block index set $[n]$ is `Fin n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Grouping.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Grouping.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
open Switching FiniteCLT UniformFinite GaussianGain MomentTransfer
attribute [local instance] Classical.propDecidable

variable {α δ ι : Type*} [Fintype α] [Fintype δ] [Fintype ι]

def eventCongr (e : α ≃ δ) : EventSpace α ι ≃ EventSpace δ ι :=
  Equiv.prodCongr e (Equiv.piCongrRight (fun _ : ι => e))

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

def groupScale (F : Cube γ → β) (n : ℕ) : ℝ := Real.sqrt n * Real.sqrt (variance F)
def groupStandard (F : Cube γ → β) (n : ℕ) : Cube (Fin n × γ) → ℝ :=
  normalizedSum (standard F) n ∘ blockCurry (Fin n) γ Bool

end Observations
end SquareRootDegree

end

end OAI


