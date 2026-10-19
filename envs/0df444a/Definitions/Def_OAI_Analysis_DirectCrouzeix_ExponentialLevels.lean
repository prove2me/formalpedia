-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_ExponentialLevels
-- name    : OAI_Analysis_DirectCrouzeix_ExponentialLevels
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:12:23.088926+00:00
-- url     : https://prove2.me/theorems/3ae2f56f-548f-4a6e-aa9c-61d56b53a32c
-- title:
--   Gradient and holomorphic complexification of exponential-sum level functions
-- statement:
--   Let $I$ be a finite index set. For vectors $v=(v_i)_{i\in I}$ in $\mathbb{C}$ and real offsets $b=(b_i)_{i\in I}$ let $L_{v,b}(z)=\sum_{i\in I}\exp(\langle v_i,z\rangle_{\mathbb{R}}+b_i)$, where $\langle v,z\rangle_{\mathbb{R}}=\operatorname{Re}(\overline{v}z)$ is the real inner product on $\mathbb{C}\cong\mathbb{R}^2$.
--
--   1. **Gradient.** The complex number
--   $$\nabla L_{v,b}(z)=\sum_{i\in I}\exp\bigl(\langle v_i,z\rangle_{\mathbb{R}}+b_i\bigr)\,v_i .$$
--   It is the gradient of $L_{v,b}$ for the real inner product: the real derivative of $L_{v,b}$ at $z$ is $w\mapsto\langle\nabla L_{v,b}(z),w\rangle_{\mathbb{R}}$.
--   2. **Complexified exponential sum.** For real families $\alpha,\beta,\gamma:I\to\mathbb{R}$,
--   $$E_{\alpha,\beta,\gamma}(z_1,z_2)=\sum_{i\in I}\exp\bigl(\gamma_i+\alpha_iz_1+\beta_iz_2\bigr)\in\mathbb{C},\qquad(z_1,z_2)\in\mathbb{C}^2.$$
--
--   $E_{\alpha,\beta,\gamma}$ is an entire function of two complex variables, real on $\mathbb{R}^2$, where it equals $\sum_ie^{\gamma_i+\alpha_ix+\beta_iy}$, and symmetric under conjugation, $E_{\alpha,\beta,\gamma}(\overline{z_1},\overline{z_2})=\overline{E_{\alpha,\beta,\gamma}(z_1,z_2)}$. Writing $z=p+x\xi+yq$ in real affine coordinates turns $L_{v,b}(z)$ into $E_{\alpha,\beta,\gamma}(x,y)$ with $\alpha_i=\langle v_i,\xi\rangle_{\mathbb{R}}$, $\beta_i=\langle v_i,q\rangle_{\mathbb{R}}$ and $\gamma_i=\langle v_i,p\rangle_{\mathbb{R}}+b_i$, so $E_{\alpha,\beta,\gamma}$ is a holomorphic extension of the level function, and the analytic implicit function theorem applied to the equation $E_{\alpha,\beta,\gamma}=1$ yields real-analytic parametrizations of the level curve $\{L_{v,b}=1\}$. The gradient enters through the convexity inequality $L_{v,b}(w)\ge L_{v,b}(z)+\langle\nabla L_{v,b}(z),w-z\rangle_{\mathbb{R}}$, and it is nonzero at every point of the level curve once $L_{v,b}<1$ somewhere.
--
--   **Formalization Note** $\nabla L_{v,b}$ is `expGradient v b` and $E_{\alpha,\beta,\gamma}$ is `expComplex α β γ`, a function on `ℂ × ℂ`; the index type carries a `Fintype` instance, and $L_{v,b}$ is `expLevel v b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/ExponentialLevels.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/ExponentialLevels.lean by skeleton subtraction
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

namespace OAI

universe u_135 u_136 u_137

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

namespace DirectCrouzeix.Geometry

variable {ι : Type u_135} [Fintype ι]

def expGradient (v : ι → ℂ) (b : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, Real.exp (inner ℝ (v i) z+b i) • v i

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_136} [Fintype ι]

def expComplex (α β γ : ι → ℝ) (z : ℂ × ℂ) : ℂ :=
  ∑ i, Complex.exp ((γ i:ℂ)+(α i:ℂ)*z.1+(β i:ℂ)*z.2)

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

end DirectCrouzeix.Geometry

namespace DirectCrouzeix.Geometry

variable {ι : Type u_137} [Fintype ι]

end DirectCrouzeix.Geometry

end

end

end

end

end

end OAI


