-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_Convexity
-- name    : OAI_Analysis_DirectCrouzeix_Convexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:22:52.494245+00:00
-- url     : https://prove2.me/theorems/6a528619-8084-4bb8-8262-4aff64d247e6
-- title:
--   Bloch-sphere coordinates and $2\times2$ quadratic forms behind the Toeplitz–Hausdorff theorem
-- statement:
--   Write $\overline{u}$ for the complex conjugate of $u\in\mathbb{C}$ and $|u|^2=u\overline{u}$.
--
--   1. **Euclidean three-space.** $\mathbb{R}^3$ with its Euclidean norm, the ambient space of the unit sphere $S^2$.
--   2. **Bloch map.** For $u,v\in\mathbb{C}$,
--   $$\beta(u,v)=\bigl(2\operatorname{Re}(\overline{u}v),\ 2\operatorname{Im}(\overline{u}v),\ |u|^2-|v|^2\bigr)\in\mathbb{R}^3.$$
--   If $|u|^2+|v|^2=1$ then $\beta(u,v)\in S^2$, and every point of $S^2$ arises in this way.
--   3. **Complex-valued linear forms on $\mathbb{R}^3$.** For $\gamma=(\gamma_0,\gamma_1,\gamma_2)\in\mathbb{C}^3$, the $\mathbb{R}$-linear map $\Lambda_\gamma:\mathbb{R}^3\to\mathbb{C}$, $\Lambda_\gamma(p)=p_0\gamma_0+p_1\gamma_1+p_2\gamma_2$.
--   4. **Quadratic form of a $2\times2$ matrix.** For $a,b,c,d,u,v\in\mathbb{C}$,
--   $$q_{a,b,c,d}(u,v)=|u|^2a+|v|^2d+\overline{u}v\,b+\overline{v}u\,c=\begin{pmatrix}\overline{u}&\overline{v}\end{pmatrix}\begin{pmatrix}a&b\\ c&d\end{pmatrix}\begin{pmatrix}u\\ v\end{pmatrix}.$$
--
--   These objects carry the classical proof that numerical ranges are convex (the Toeplitz–Hausdorff theorem). For $|u|^2+|v|^2=1$ one has $q_{a,b,c,d}(u,v)=\tfrac{a+d}{2}+\Lambda_{\gamma}(\beta(u,v))$ with $\gamma=\bigl(\tfrac{b+c}{2},\tfrac{i(b-c)}{2},\tfrac{a-d}{2}\bigr)$, so the numerical range of a $2\times2$ matrix is a translate of the image of $S^2$ under an $\mathbb{R}$-linear map $\mathbb{R}^3\to\mathbb{C}$; that image coincides with the image of the closed unit ball and is therefore convex. For a linear operator $T$ on a complex inner-product space and orthonormal vectors $x,y$, $\langle ux+vy,T(ux+vy)\rangle=q_{a,b,c,d}(u,v)$ with $a=\langle x,Tx\rangle$, $b=\langle x,Ty\rangle$, $c=\langle y,Tx\rangle$, $d=\langle y,Ty\rangle$, which reduces convexity of $\{\langle x,Tx\rangle:\|x\|=1\}$ to the two-dimensional case.
--
--   **Formalization Note** $\mathbb{R}^3$ is the abbreviation `Three` for `EuclideanSpace ℝ (Fin 3)`; $\beta$ is `bloch`, $\Lambda_\gamma$ is `threeLinear γ` (a bundled real-linear map) and $q_{a,b,c,d}(u,v)$ is `twoForm a b c d u v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Convexity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Convexity.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SupportNets

namespace OAI

universe u_140 u_141 u_142

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

noncomputable section

open Set

open scoped ComplexConjugate Matrix

namespace DirectCrouzeix.Geometry

abbrev Three := EuclideanSpace ℝ (Fin 3)

def bloch (u v : ℂ) : Three :=
  WithLp.toLp 2 ![2*(conj u*v).re,2*(conj u*v).im,Complex.normSq u-Complex.normSq v]

def threeLinear (c : Fin 3 → ℂ) : Three →ₗ[ℝ] ℂ where
  toFun p := ∑ i, (p i : ℂ)*c i
  map_add' p q := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' a p := by simp [Complex.real_smul,Finset.mul_sum,mul_assoc]

def twoForm (a b c d u v : ℂ) : ℂ :=
  Complex.normSq u * a + Complex.normSq v * d + (conj u*v)*b + (conj v*u)*c

section Inner

variable {E : Type u_142} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Inner

end DirectCrouzeix.Geometry

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


