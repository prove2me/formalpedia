-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_ReadoutCLT
-- name    : OAI_Combinatorics_BooleanFunctions_ReadoutCLT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:41:20.050274+00:00
-- url     : https://prove2.me/theorems/e112d7d2-097d-4a0f-ae44-0eb8e210816f
-- title:
--   The bump test and the absolute-value readout constant $c$
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on $\mathbb{R}$.
--
--   1. **Test function.** $\psi(x)=\tfrac12\operatorname{tent}_{1,1/2}(x)=\tfrac12\max\{0,\,1-2|x-1|\}$, a continuous bump of height $1/2$ vanishing outside $(1/2,3/2)$.
--   2. **Readout constant.**
--   $$c=\frac12\int_{\mathbb{R}}\psi\,d\gamma .$$
--
--   The constant $c$ is positive, and $\psi(x)\le|x|$ for all $x$. Since $\psi$ is continuous with compact support, the central limit theorem gives $\mathbb{E}|Z_n|>c$ for large $n$, where $Z_n$ is the normalized sum of $n$ independent copies of a mean-zero, unit-variance variable on a finite space. The constant $c$ is therefore the guaranteed factor between first-order Fourier mass and the square root of the variance when an observation is read out by the sign of its score.
--
--   **Formalization Note** The Lean names are `ReadoutCLT.test` and `ReadoutCLT.constant`, with `gaussianReal 0 1` for $\gamma$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/ReadoutCLT.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/ReadoutCLT.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Amplification

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace ReadoutCLT
open MeasureTheory ProbabilityTheory Filter UniformFinite FiniteCLT
open scoped Topology
attribute [local instance] Classical.propDecidable

def test (x : ℝ) : ℝ := (1/2)*SmoothGaussian.tent 1 (1/2) x
def constant : ℝ := (∫ x, test x ∂gaussianReal 0 1)/2

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]

end ReadoutCLT
end SquareRootDegree

end

end OAI


