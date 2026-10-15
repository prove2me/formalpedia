-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:30:12.905361+00:00
-- url     : https://prove2.me/theorems/0bd524cf-449c-4477-81dd-39b513563d21
-- title:
--   Zero extension of real coordinate vectors along an injective map
-- statement:
--   Let $J$ and $L$ be finite sets and $e:J\to L$ an injective map. For $z\in\mathbb{R}^J$, the **zero extension** of $z$ along $e$ is the vector $\mathrm{ext}_ez\in\mathbb{R}^L$ with
--   $$(\mathrm{ext}_ez)_{e(j)}=z_j\quad(j\in J),\qquad(\mathrm{ext}_ez)_l=0\quad(l\notin e(J)).$$
--
--   Zero extension is an isometry, $\|\mathrm{ext}_ez\|=\|z\|$, and it is compatible with synthesis along selections of a sign matrix: for an injective $f:L\to I$, synthesizing $\mathrm{ext}_ez$ along $f$ gives the same vector as synthesizing $z$ along $f\circ e$. Hence a bound for all selections of exactly $p$ columns also bounds every smaller selection. The module uses this to pass from $p$-column selections to all subfamilies of at most $p$ labels (when $p\le|I|$), and to prove the frame lemma: for a finite set $I$ with $|I|\ge2$ and $r\ge1$ there are unit vectors $(v_i)_{i\in I}$ in $\mathbb{C}^{k}$, $k=\lceil2r\log(2|I|)\rceil_+$, all of whose subfamilies of at most $\min(2r,|I|)$ vectors have synthesis norm at most $10$.
--
--   **Formalization Note** `SignMatrix.extendVector e z` is `WithLp.toLp 2 (SignMatrix.extend e z)` for an embedding `e : J ↪ L`; it is the only definition of this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Frames.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Frames.lean by skeleton subtraction
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

namespace OAI

/-! Frame existence with prescribed dimensions and bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
def extendVector (e : J ↪ L) (z : EuclideanSpace ℝ J) : EuclideanSpace ℝ L :=
  WithLp.toLp 2 (extend e z)

end SignMatrix
end Dixmier

end

end OAI


