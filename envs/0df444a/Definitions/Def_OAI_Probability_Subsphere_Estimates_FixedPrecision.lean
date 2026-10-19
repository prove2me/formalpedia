-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
-- name    : OAI_Probability_Subsphere_Estimates_FixedPrecision
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:55:22.3864+00:00
-- url     : https://prove2.me/theorems/b442a5df-3204-4323-a1be-3218b63c583d
-- title:
--   The numerical constant $e^{2048}$ of the fixed-dimension precision estimate
-- statement:
--   This file defines a single real number,
--
--   $$
--   C_\ast=e^{2048}.
--   $$
--
--   It is the explicit value of the constant $C$ in the fixed-dimension estimate for finite-state streams: for large $d$, integers $j,m$ with $d/2+2j\le m\le d$, a precision $\eta>0$, and seeded streams on $\mathbb{R}^m$ with $2^{d^2}$ states that read $j\lfloor d/32\rfloor$ Gaussian rows, the probability (over a uniform hidden unit vector $s$, the seed and the rows) of producing an estimate within Euclidean distance $\eta$ of $s$ is at most $(C^{j+1}\eta)^{d/32}$, under the measurability assumptions of that estimate. The number $C_\ast$ satisfies $C_\ast\ge2$ and is large enough that the explicit bound produced by the proof (for $d\ge64$ and $\eta\le1$) is dominated by $(C_\ast^{\,j+1}\eta)^{d/32}$.
--
--   **Formalization Note** `Fixed.boundConstant : ℝ := Real.exp 2048`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Estimates/FixedPrecision.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Estimates/FixedPrecision.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine

namespace OAI

noncomputable section

namespace SubsphereCurrent.Fixed
section
open scoped ENNReal NNReal

def boundConstant : ℝ := Real.exp 2048
end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u

end SubsphereCurrent.Fixed

end

end OAI


