-- Prove2me | Definitions.Def_OAI_Combinatorics_BooleanFunctions_Readout
-- name    : OAI_Combinatorics_BooleanFunctions_Readout
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:42:00.319669+00:00
-- url     : https://prove2.me/theorems/b57fe47d-15ed-45cf-90b1-d135a37a990f
-- title:
--   Sign readout of the score and reindexing of cube coordinates
-- statement:
--   Let $\Gamma$ be a finite coordinate set, $F:\mathbb{B}^\Gamma\to B$ an observation, $S(x)=\sum_i\operatorname{sgn}(x_i)$ the cube sum and $\operatorname{sc}_F=\mathbb{E}[S\mid F]$ the score.
--
--   1. **Sign readout.** For $z\in\mathbb{R}$, $\operatorname{sgn}^{+}(z)=1$ if $z\ge0$ and $\operatorname{sgn}^{+}(z)=-1$ if $z<0$.
--   2. **Readout of an observation.** The $\{-1,1\}$-valued function
--   $$f_F(x)=\operatorname{sgn}^{+}\big(\operatorname{sc}_F(x)\big).$$
--   3. **Coordinate reindexing.** For a bijection $e:\Gamma\to\Delta$ between coordinate sets, the bijection $\mathbb{B}^\Delta\to\mathbb{B}^\Gamma$, $x\mapsto x\circ e$, with inverse $y\mapsto y\circ e^{-1}$.
--
--   Since $f_F$ is a function of the label $F(x)$, its Fourier degree is at most the cost of $F$, and $\operatorname{sgn}^+(z)\,z=|z|$ gives $\sum_i\hat f_F(\{i\})=\mathbb{E}[f_F\,S]=\mathbb{E}\,|\operatorname{sc}_F|$: the readout turns the absolute first moment of the score into first-order Fourier mass of a Boolean function. Reindexing moves such a function to the standard cube on $\{0,\dots,n-1\}$ without changing its first-order sum or increasing its degree.
--
--   **Formalization Note** The Lean names are `Observations.readSign`, `readout` and `cubeReindex`, where `cubeReindex e` is an `Equiv` from `Cube δ` to `Cube γ` for `e` an `Equiv` from `γ` to `δ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BooleanFunctions/Readout.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Readout.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_ReadoutCLT

namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

def readSign (z : ℝ) : ℝ := if 0 ≤ z then 1 else -1

def readout (F : Cube γ → β) (x : Cube γ) : ℝ := readSign (score F x)

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ δ : Type*} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]

def cubeReindex (e : γ ≃ δ) : Cube δ ≃ Cube γ where
  toFun x i := x (e i)
  invFun x j := x (e.symm j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

end Observations
end SquareRootDegree

end

end OAI


