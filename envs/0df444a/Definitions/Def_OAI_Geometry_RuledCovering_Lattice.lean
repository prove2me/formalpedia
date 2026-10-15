-- Prove2me | Definitions.Def_OAI_Geometry_RuledCovering_Lattice
-- name    : OAI_Geometry_RuledCovering_Lattice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T06:17:37.330005+00:00
-- url     : https://prove2.me/theorems/0eca2ed6-029b-4dd9-8c64-1fc31bc8c5c8
-- title:
--   Rounding to the nearest integer with half-integers rounded up
-- statement:
--   For a real number $t$, its nearest integer is
--   $$\operatorname{round}(t)=\Bigl\lfloor t+\tfrac12\Bigr\rfloor\in\mathbb{Z},$$
--   where $\lfloor\cdot\rfloor$ is the floor function. Thus $\operatorname{round}(t)$ is an integer closest to $t$, and ties at half-integers are broken upwards: $\operatorname{round}(k+\tfrac12)=k+1$ for every integer $k$.
--
--   The rounding map is monotone and satisfies $|\operatorname{round}(t)-t|\le\tfrac12$ for all $t$ (shown in the same module). It is the elementary step of the monotone fixed-point argument behind the planar lattice covering lemmas: for reals $\alpha,\beta$ with $0\le\alpha\beta<1$ and any $(u_1,u_2)\in\mathbb{R}^2$ there are integers $i,j$ with $|u_1-(i+\alpha j)|\le\tfrac12$ and $|u_2-(\beta i+j)|\le\tfrac12$. The symmetric case $\alpha=\beta$, $|\alpha|<1$, feeds the hyperbolic lattice template, and the case $\beta=0$ with arbitrary $\alpha$ (sliding rows) feeds the nilpotent one.
--
--   **Formalization Note** `nearestInteger t` is `⌊t + 1 / 2⌋`, using Mathlib's `Int.floor`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/RuledCovering/Lattice.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/Lattice.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RuledCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- Rounding convention: half-integers are rounded upwards. -/
def nearestInteger (t : ℝ) : ℤ := ⌊t + 1 / 2⌋

end RuledApproximation

end

end OAI


