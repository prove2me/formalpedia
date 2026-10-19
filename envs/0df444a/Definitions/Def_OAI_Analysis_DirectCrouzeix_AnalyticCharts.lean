-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_AnalyticCharts
-- name    : OAI_Analysis_DirectCrouzeix_AnalyticCharts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:07:54.310419+00:00
-- url     : https://prove2.me/theorems/8afbcbb2-599f-4388-b372-8e64a5d9d3b9
-- title:
--   Coordinatewise conjugation on $\mathbb{C}^2$ and exponential-sum level functions on the plane
-- statement:
--   Identify $\mathbb{C}$ with $\mathbb{R}^2$ and write $\langle v,z\rangle_{\mathbb{R}}=\operatorname{Re}(\overline{v}z)=\operatorname{Re}v\,\operatorname{Re}z+\operatorname{Im}v\,\operatorname{Im}z$ for the real inner product.
--
--   1. **Coordinatewise conjugation on $\mathbb{C}^2$.** The map $\sigma:\mathbb{C}^2\to\mathbb{C}^2$, $\sigma(z_1,z_2)=(\overline{z_1},\overline{z_2})$. A simplification lemma records $\sigma(0,0)=(0,0)$.
--   2. **Exponential-sum level function.** For a finite index set $I$, vectors $v=(v_i)_{i\in I}$ in $\mathbb{C}$ and real offsets $b=(b_i)_{i\in I}$,
--   $$L_{v,b}(z)=\sum_{i\in I}\exp\bigl(\langle v_i,z\rangle_{\mathbb{R}}+b_i\bigr),\qquad z\in\mathbb{C}.$$
--
--   $L_{v,b}$ is a smooth, positive, convex function on the plane, so $\{L_{v,b}<1\}$ is an open convex set and $\{L_{v,b}\le1\}$ a closed convex set; as soon as $L_{v,b}<1$ at some point, the gradient of $L_{v,b}$ does not vanish on the level curve $\{L_{v,b}=1\}$, which is then a real-analytic curve. With many directions $v_i$ these sublevel sets approximate a given compact convex set from outside, by sets with analytic boundary. The conjugation $\sigma$ is the real structure of $\mathbb{C}^2$: a holomorphic function $F$ of two variables with $F(\sigma(z))=\overline{F(z)}$ is real on $\mathbb{R}^2$, and this symmetry is what an analytic implicit-function argument needs to produce a real-analytic parametrization of such a level curve.
--
--   **Formalization Note** $\sigma$ is `conjugatePair` (a map on `ℂ × ℂ`), with simp lemma `conjugatePair_zero`. $L_{v,b}$ is `expLevel v b`; the index type carries a `Fintype` instance, and $\langle v_i,z\rangle_{\mathbb{R}}$ is `inner ℝ (v i) z`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/AnalyticCharts.lean by skeleton subtraction
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

namespace OAI

universe u_133 u_134 u_135

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

namespace DirectCrouzeix.Geometry

def conjugatePair (z : ℂ × ℂ) : ℂ × ℂ := (conj z.1,conj z.2)

@[simp] theorem conjugatePair_zero : conjugatePair 0 = 0 := by simp [conjugatePair]

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

noncomputable section

open Set Filter Metric

open scoped Topology ComplexConjugate

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

def expLevel (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) : ℝ :=
  ∑ i, Real.exp (inner ℝ (v i) z+b i)

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI


