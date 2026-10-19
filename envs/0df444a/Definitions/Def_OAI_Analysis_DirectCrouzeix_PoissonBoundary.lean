-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_PoissonBoundary
-- name    : OAI_Analysis_DirectCrouzeix_PoissonBoundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:57:24.936892+00:00
-- url     : https://prove2.me/theorems/3a9dc535-8de3-4642-b8d1-55d91d43b6a1
-- title:
--   Poisson and Herglotz–Riesz integrals of boundary data on a circle about the origin
-- statement:
--   Fix a real number $R$ and a real-valued function $u:\mathbb{C}\to\mathbb{R}$; only the values of $u$ on the circle $|\zeta|=|R|$ are used. For a point $z\in\mathbb{C}$ this file defines two averages of $u$ against classical kernels over that circle, parametrized as $\zeta=Re^{i\theta}$, $0\le\theta\le2\pi$.
--
--   1. **Poisson integral.** With the Poisson kernel $P(z,\zeta)=\dfrac{|\zeta|^2-|z|^2}{|\zeta-z|^2}$, the real number
--   $$\mathcal{P}_R[u](z)=\frac{1}{2\pi}\int_0^{2\pi}\frac{R^2-|z|^2}{|Re^{i\theta}-z|^2}\,u(Re^{i\theta})\,d\theta .$$
--   2. **Herglotz–Riesz integral.** With the Herglotz–Riesz kernel $H(z,\zeta)=\dfrac{\zeta+z}{\zeta-z}$, the complex number
--   $$\mathcal{H}_R[u](z)=\frac{1}{2\pi}\int_0^{2\pi}\frac{Re^{i\theta}+z}{Re^{i\theta}-z}\,u(Re^{i\theta})\,d\theta .$$
--
--   The two kernels are related by $\operatorname{Re}H(z,\zeta)=P(z,\zeta)$. For $R>0$, $|z|<R$ and $u$ continuous on the circle $|\zeta|=R$, the real part of $\mathcal{H}_R[u](z)$ is $\mathcal{P}_R[u](z)$; moreover $\mathcal{P}_R[u]$ is the harmonic function in the disc $|z|<R$ with boundary values $u$, and $\mathcal{H}_R[u]$ is holomorphic in that disc. These are the basic tools for the Dirichlet problem on a disc, for producing holomorphic functions with prescribed real part, and for the reflection principles used to continue conformal maps across analytic boundary arcs.
--
--   **Formalization Note** The two transforms are `poissonExtension R u z` and `herglotzExtension R u z`, defined as Mathlib's `Real.circleAverage` (centre $0$, radius $R$) of `poissonKernel 0 z ζ * u ζ` and of `herglotzRieszKernel 0 z ζ * u ζ`. They are total functions of $R$, $u$ and $z$: by Lean's conventions the average of a non-integrable integrand is $0$, and the kernels, being quotients, take the value $0$ at $\zeta=z$, which matters only for points $z$ on the circle. For negative $R$ the parametrization $\theta\mapsto Re^{i\theta}$ still runs over the circle of radius $|R|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/PoissonBoundary.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PoissonBoundary.lean by skeleton subtraction
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

def poissonExtension (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage (fun ζ => poissonKernel 0 z ζ * u ζ) 0 R

def herglotzExtension (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℂ :=
  Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ * (u ζ : ℂ)) 0 R

end Conformal

end DirectCrouzeix

end

end

end

end OAI


