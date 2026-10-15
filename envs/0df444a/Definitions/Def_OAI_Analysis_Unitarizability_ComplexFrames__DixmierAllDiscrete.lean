-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:29:32.299978+00:00
-- url     : https://prove2.me/theorems/918284ac-4964-4ada-a182-1fc2c78851a1
-- title:
--   Complexification, real parts and imaginary parts of Euclidean coordinate vectors
-- statement:
--   Let $K$ be a finite set, and let $\mathbb{R}^K$ and $\mathbb{C}^K$ be the real and complex Euclidean coordinate spaces.
--
--   1. **Complexification.** $\iota:\mathbb{R}^K\to\mathbb{C}^K$, $(\iota v)_a=v_a$, each real coordinate viewed as a complex number.
--   2. **Real part.** $\operatorname{Re}:\mathbb{C}^K\to\mathbb{R}^K$, $(\operatorname{Re}z)_a=\operatorname{Re}(z_a)$.
--   3. **Imaginary part.** $\operatorname{Im}:\mathbb{C}^K\to\mathbb{R}^K$, $(\operatorname{Im}z)_a=\operatorname{Im}(z_a)$.
--
--   One has $z=\iota(\operatorname{Re}z)+\mathrm{i}\,\iota(\operatorname{Im}z)$, $\|\iota v\|=\|v\|$ and
--   $$\|z\|^2=\|\operatorname{Re}z\|^2+\|\operatorname{Im}z\|^2 .$$
--   These maps let real synthesis bounds pass to complex coefficients by treating the real and imaginary coefficient vectors separately: if real vectors $v_j$ satisfy $\|\sum_{j\in J}z_jv_j\|\le b\|z\|$ for all real coefficient vectors $z$, then the complexified family $(\iota v_j)$ satisfies the same bound for all complex coefficient vectors. This is how real random sign frames become the complex frames used in the fibres $\mathbb{C}^k$ of the construction.
--
--   **Formalization Note** `ComplexFrames.ofReal`, `ComplexFrames.realPart` and `ComplexFrames.imagPart` are coordinatewise maps between `EuclideanSpace ℝ K` and `EuclideanSpace ℂ K` built with `WithLp.toLp 2`; they are plain functions rather than bundled linear maps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/ComplexFrames.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/ComplexFrames.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete

namespace OAI

/-! Complexification preserves real synthesis norm bounds.
The real and imaginary coefficient vectors are handled separately. -/
noncomputable section
namespace Dixmier
namespace ComplexFrames
open Finset
variable {I K : Type*} [Fintype K]
def ofReal (v : EuclideanSpace ℝ K) : EuclideanSpace ℂ K := WithLp.toLp 2 (fun a => (v a : ℂ))
def realPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).re)
def imagPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).im)

end ComplexFrames
end Dixmier

end

end OAI


