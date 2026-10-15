-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_MeanBounds
-- name    : OAI_Analysis_Unitarizability_MeanBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:40:28.909855+00:00
-- url     : https://prove2.me/theorems/b3d8690a-50d8-4a71-8bf7-9352a98aedc8
-- title:
--   Real and imaginary parts of a bounded complex function on a discrete space
-- statement:
--   Let $G$ be a set carrying the discrete topology (no group structure is used), and let $\ell^\infty(G)$ be the space of bounded functions $f:G\to\mathbb{C}$ with the supremum norm $\|f\|=\sup_{x\in G}|f(x)|$. The file defines two operations on $\ell^\infty(G)$.
--
--   1. **Real part.** $\operatorname{Re}f\in\ell^\infty(G)$ is the function $x\mapsto\operatorname{Re}f(x)$, viewed as complex-valued (with zero imaginary part).
--   2. **Imaginary part.** $\operatorname{Im}f\in\ell^\infty(G)$ is the function $x\mapsto\operatorname{Im}f(x)$, again viewed as complex-valued.
--
--   Both functions are bounded by $\|f\|$, because $|\operatorname{Re}z|\le|z|$ and $|\operatorname{Im}z|\le|z|$ for $z\in\mathbb{C}$, and they recover $f$ pointwise:
--   $$f=\operatorname{Re}f+i\,\operatorname{Im}f .$$
--
--   The decomposition reduces estimates for positive linear functionals on $\ell^\infty(G)$ to real-valued functions: a normalized positive functional $m$ satisfies $|m(h)|\le C$ for every real-valued $h$ with $|h|\le C$, and applying this to $\operatorname{Re}f$ and $\operatorname{Im}f$ gives $|m(f)|\le2\|f\|$. That bound makes the averaged sesquilinear form in the proof of the Day–Dixmier theorem bounded.
--
--   **Formalization Note** The functions are `DayDixmier.realComponent f` and `DayDixmier.imagComponent f`, built with `BoundedContinuousFunction.ofNormedAddCommGroupDiscrete` from the pointwise formula and the explicit bound $\|f\|$; elements of $\ell^\infty(G)$ are bounded continuous functions `G →ᵇ ℂ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/MeanBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/MeanBounds.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport__DixmierAllDiscrete

namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [TopologicalSpace G]

variable [DiscreteTopology G]

def realComponent (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun g => ((f g).re : ℂ)) ‖f‖
    (fun g => by simpa using (Complex.abs_re_le_norm (f g)).trans (f.norm_coe_le_norm g))

def imagComponent (f : G →ᵇ ℂ) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun g => ((f g).im : ℂ)) ‖f‖
    (fun g => by simpa using (Complex.abs_im_le_norm (f g)).trans (f.norm_coe_le_norm g))

end DayDixmier
end Dixmier
end

end OAI


