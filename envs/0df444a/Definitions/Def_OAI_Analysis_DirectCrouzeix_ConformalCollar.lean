-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_ConformalCollar
-- name    : OAI_Analysis_DirectCrouzeix_ConformalCollar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:04:36.833391+00:00
-- url     : https://prove2.me/theorems/eba87a7a-593f-491b-a21b-77653551f2a2
-- title:
--   Analytic boundary charts and planar sets with analytic boundary
-- statement:
--   Let $U\subseteq\mathbb{C}$ be a set and $p\in\mathbb{C}$ a point.
--
--   1. **Analytic boundary chart of $U$ at $p$.** Such a chart consists of open sets $S,T\subseteq\mathbb{C}$ and a homeomorphism $\varphi:S\to T$ with inverse $\psi=\varphi^{-1}:T\to S$ such that $0\in S$, $\varphi(0)=p$, $\varphi$ is holomorphic on $S$, $\psi$ is holomorphic on $T$, $\psi'(p)\neq0$, and $\varphi$ sends exactly the upper half of $S$ into $U$:
--   $$\varphi(z)\in U\iff\operatorname{Im}z>0\qquad\text{for every }z\in S.$$
--   2. **Analytic boundary.** $U$ has analytic boundary if every point $p$ of its topological boundary $\partial U=\overline{U}\setminus\operatorname{int}U$ admits at least one analytic boundary chart of $U$ at $p$.
--
--   A chart straightens the boundary near $p$: since $\varphi$ is a biholomorphism of $S$ onto the open set $T$, one gets $U\cap T=\varphi(S\cap\{\operatorname{Im}z>0\})$, so near $p$ the boundary of $U$ is the real-analytic arc $\varphi(S\cap\mathbb{R})$ and $U$ lies on exactly one side of it. This is the regularity hypothesis under which the conformal map from the unit disc onto a bounded simply connected domain $U$ extends holomorphically and injectively, with nonvanishing derivative, to a disc of radius larger than $1$ (a conformal collar), so that boundary integrals over $\partial U$ can be pulled back to circles.
--
--   **Formalization Note** `AnalyticBoundaryChart U p` is a structure whose data is an `OpenPartialHomeomorph ℂ ℂ` (its `source` is $S$ and its `target` is $T$, both open) together with the listed properties; holomorphy is `AnalyticOnNhd ℂ`, and the derivative condition is `deriv chart.symm p ≠ 0`. `HasAnalyticBoundary U` asks for `Nonempty (AnalyticBoundaryChart U p)` for every `p ∈ frontier U`; no openness or boundedness of $U$ is built into the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ConformalCollar.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ConformalCollar.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

open InnerProductSpace Real

structure AnalyticBoundaryChart (U : Set ℂ) (p : ℂ) where
  chart : OpenPartialHomeomorph ℂ ℂ
  zero_mem : 0 ∈ chart.source
  at_zero : chart 0 = p
  analytic : AnalyticOnNhd ℂ chart chart.source
  inverse_analytic : AnalyticOnNhd ℂ chart.symm chart.target
  inverse_derivative : deriv chart.symm p ≠ 0
  side : ∀ z ∈ chart.source, chart z ∈ U ↔ 0 < z.im

def HasAnalyticBoundary (U : Set ℂ) : Prop :=
  ∀ p ∈ frontier U, Nonempty (AnalyticBoundaryChart U p)

end Conformal

end DirectCrouzeix

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

end

end

end

end

end OAI


