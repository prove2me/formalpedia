-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:27:57.085328+00:00
-- url     : https://prove2.me/theorems/880f453f-e323-4db9-91b9-0b49e83ab818
-- title:
--   Frame dimension $\lceil 2r\log(2n)\rceil$ and subfamily size $\min(2r,n)$
-- statement:
--   For natural numbers $n$ (the number of frame vectors) and $r$ (a capacity), with $\log$ the natural logarithm and $\lceil t\rceil_+$ the natural-number ceiling of a real number $t$:
--
--   1. **Frame dimension.**
--   $$k(n,r)=\bigl\lceil 2r\log(2n)\bigr\rceil_+ .$$
--   2. **Subfamily size.**
--   $$p(n,r)=\min(2r,\,n).$$
--
--   These are the parameters of the frame lemma of the development: for $n\ge2$ and $r\ge1$ there are $n$ unit vectors in $\mathbb{C}^{k(n,r)}$ such that every subfamily of at most $p(n,r)$ of them has synthesis norm at most $10$. The module checks the arithmetic behind the probabilistic proof: for $n\ge2$ and $r\ge1$ one has $1\le k(n,r)$, $p(n,r)\le k(n,r)$ and $p(n,r)\log n\le k(n,r)$; and for all natural numbers $n\ge2$, $k\ge1$ and $p\le k$ with $p\log n\le k$, the union bound $2n^{p}\,9^{k+p}\,e^{-25k/2}$ is strictly smaller than $1$. The subfamily size $\min(2r,n)$ matches the bound on the difference sets of a mask with capacity $r$ over $n$ labels.
--
--   **Formalization Note** `FrameParameters.dimension n r` is `⌈2 * r * Real.log (2 * n)⌉₊` and `FrameParameters.subfamilySize n r` is `min (2*r) n`; for $n=0$ Lean's convention $\log0=0$ gives dimension $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FrameParameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FrameParameters.lean by skeleton subtraction
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

namespace OAI

/-! Ceiling dimensions and finite union-bound arithmetic for frames. -/
noncomputable section
namespace Dixmier
namespace FrameParameters

def dimension (n r : ℕ) : ℕ := ⌈2 * (r : ℝ) * Real.log (2 * (n : ℝ))⌉₊
def subfamilySize (n r : ℕ) : ℕ := min (2*r) n

end FrameParameters
end Dixmier

end

end OAI


