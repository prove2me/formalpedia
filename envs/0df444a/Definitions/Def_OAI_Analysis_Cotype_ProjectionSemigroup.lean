-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
-- name    : OAI_Analysis_Cotype_ProjectionSemigroup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:47:09.019982+00:00
-- url     : https://prove2.me/theorems/aaccb480-220e-4118-8bab-fc8fc6396ad1
-- title:
--   The coordinate projection semigroup
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$.
--
--   1. **Semigroup.** $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$ for $r\in\mathbb R$.
--   2. **Weights.** $\pi_r(\varepsilon)=\prod_i(1-r\text{ if }\varepsilon_i=1,\ r\text{ else})$, the expansion weights of the product.
--   3. **Linear coefficient.**
--   $$
--   L=\sum_i(1-P_i)\prod_{j\ne i}P_j ,
--   $$
--   the coefficient of $r$ in $T(r)$, i.e. $T'(0)$. Bounding $L$ is the core of the K-convexity estimate.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionSemigroup.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionSemigroup.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def projectionSemigroup {m : ℕ} (P : Fin m → X →L[ℝ] X) (r : ℝ) : X →L[ℝ] X :=
  projectionProduct (fun i => P i + r • (1-P i))

def projectionWeight {m : ℕ} (r : ℝ) (ε : Cube m) : ℝ :=
  ∏ i, if ε i then 1-r else r

def projectionLinearCoefficient {m : ℕ} (P : Fin m → X →L[ℝ] X) : X →L[ℝ] X :=
  ∑ i, (1-P i) * projectionSubset P (fun j => decide (j ≠ i))

end Cotype

end

end OAI


