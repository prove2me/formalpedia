-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_SupportNets
-- name    : OAI_Analysis_DirectCrouzeix_SupportNets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:20:14.186604+00:00
-- url     : https://prove2.me/theorems/e814f720-d413-4fbe-accb-2f1559cdd5ca
-- title:
--   Support function of a planar set
-- statement:
--   Identify $\mathbb{C}$ with $\mathbb{R}^2$ and write $\langle\nu,z\rangle_{\mathbb{R}}=\operatorname{Re}(\overline{\nu}z)$ for the real inner product. For a set $K\subseteq\mathbb{C}$ and a direction $\nu\in\mathbb{C}$, the support function of $K$ is
--   $$h_K(\nu)=\sup_{z\in K}\langle\nu,z\rangle_{\mathbb{R}}.$$
--   For a unit vector $\nu$ and a nonempty bounded set $K$, the closed half-plane $\{z:\langle\nu,z\rangle_{\mathbb{R}}\le h_K(\nu)\}$ is the smallest closed half-plane with outer normal $\nu$ that contains $K$.
--
--   For compact nonempty $K$ the supremum is attained, and $h_K(\nu)\le M$ for every unit $\nu$ when $K$ lies in the closed disc of radius $M$. A compact convex set is the intersection of its supporting half-planes, and testing only finitely many directions gives a quantitative version: if $K$ is compact, convex and contained in the disc of radius $M$, the directions $\mu$ form a $\delta$-net of the unit circle, and $|z|\le L$ satisfies $\langle\mu,z\rangle_{\mathbb{R}}\le h_K(\mu)+\delta$ for every net direction $\mu$, then $z$ lies within distance $\delta(1+L+M)$ of $K$. This is how a compact convex set, such as a numerical range, is approximated from outside by finitely many half-planes, before these half-planes are smoothed into exponential sums.
--
--   **Formalization Note** $h_K(\nu)$ is `convexSupport K ν`, Mathlib's `sSup` of the image of $K$ under $z\mapsto\langle\nu,z\rangle_{\mathbb{R}}$. Lean's `sSup` on $\mathbb{R}$ returns $0$ for the empty set and for sets that are not bounded above, so $h_K(\nu)$ is a genuine supremum only when $K$ is nonempty and the image is bounded above (for example when $K$ is compact and nonempty).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/SupportNets.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
import Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
import Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

def convexSupport (K : Set ℂ) (ν : ℂ) : ℝ := sSup ((fun z => inner ℝ ν z) '' K)

end DirectCrouzeix.Geometry

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end

end

end OAI


