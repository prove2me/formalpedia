-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_InverseExterior
-- name    : OAI_Analysis_DirectCrouzeix_InverseExterior
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:16:31.24196+00:00
-- url     : https://prove2.me/theorems/81d16cbe-ba41-4374-8bab-01f2767883e9
-- title:
--   Inversion of the exterior of a sublevel set into a bounded domain containing the origin
-- statement:
--   Let $f:\mathbb{C}\to\mathbb{R}$ be a function and $a\in\mathbb{C}$ a point. Define
--   $$\Omega_{f,a}=\{0\}\cup\bigl\{w\in\mathbb{C}\setminus\{0\}\ :\ f\bigl(a+w^{-1}\bigr)>1\bigr\}.$$
--   For $w\neq0$, membership means that $z=a+1/w$ lies in the exterior region $\{f>1\}$. Hence $\Omega_{f,a}\setminus\{0\}$ is the image of $\{z\neq a:\ f(z)>1\}$ under the inversion $z\mapsto1/(z-a)$, and the point $0$ plays the role of the image of $\infty$. A simplification lemma records $0\in\Omega_{f,a}$.
--
--   If $f$ is convex and continuous, $f(a)<1$ and the sublevel set $\{f\le1\}$ is compact, then $\Omega_{f,a}$ is a bounded open set, star-shaped with respect to $0$ (hence simply connected) and different from $\mathbb{C}$, and each of its boundary points $w$ satisfies $w\neq0$ and $f(a+1/w)=1$. The Riemann mapping theorem therefore applies to $\Omega_{f,a}$; this turns the unbounded exterior of the convex domain $\{f<1\}$ into a bounded simply connected domain and produces exterior conformal maps of that convex domain.
--
--   **Formalization Note** $\Omega_{f,a}$ is `inverseExterior f a`, the set of $w$ with `w = 0 ∨ 1 < f (a+w⁻¹)`; since Lean sets $0^{-1}=0$, the point $0$ is included explicitly through the first alternative. The simp lemma is `zero_mem_inverseExterior`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/InverseExterior.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/InverseExterior.lean by skeleton subtraction
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

namespace DirectCrouzeix.Geometry

def inverseExterior (f : ℂ → ℝ) (a : ℂ) : Set ℂ := {w | w = 0 ∨ 1 < f (a+w⁻¹)}

@[simp] theorem zero_mem_inverseExterior (f : ℂ → ℝ) (a : ℂ) : 0 ∈ inverseExterior f a := Or.inl rfl

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end

end

end

end OAI


