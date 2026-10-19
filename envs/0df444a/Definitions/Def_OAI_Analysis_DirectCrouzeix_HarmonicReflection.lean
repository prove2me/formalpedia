-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_HarmonicReflection
-- name    : OAI_Analysis_DirectCrouzeix_HarmonicReflection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:00:50.861477+00:00
-- url     : https://prove2.me/theorems/a62da8de-da71-4507-a15d-69657c66a770
-- title:
--   Upper half-discs, odd reflection across the real axis, and the Poisson extension completed by boundary values
-- statement:
--   Fix $R\in\mathbb{R}$ and write $\overline{z}$ for the complex conjugate of $z$. For $u:\mathbb{C}\to\mathbb{R}$ let
--   $$\mathcal{P}_R[u](z)=\frac{1}{2\pi}\int_0^{2\pi}\frac{R^2-|z|^2}{|Re^{i\theta}-z|^2}\,u(Re^{i\theta})\,d\theta$$
--   be the Poisson integral of $u$ over the circle of radius $R$ centred at $0$. The file defines the following objects.
--
--   1. **Poisson extension completed by boundary values.** For $u:\mathbb{C}\to\mathbb{R}$,
--   $$\widetilde{\mathcal{P}}_R[u](z)=\begin{cases}\mathcal{P}_R[u](z), & |z|<R,\\ u(z), & |z|\ge R.\end{cases}$$
--   2. **Open upper half-disc** $D_R^{+}=\{z\in\mathbb{C}:\ |z|<R,\ \operatorname{Im}z>0\}$.
--   3. **Closed upper half-disc** $\overline{D}{}_R^{+}=\{z\in\mathbb{C}:\ |z|\le R,\ \operatorname{Im}z\ge0\}$.
--   4. **Odd reflection across the real axis.** For $u:\mathbb{C}\to\mathbb{R}$,
--   $$u^{\mathrm{odd}}(z)=\begin{cases}u(z), & \operatorname{Im}z\ge0,\\ -u(\overline{z}), & \operatorname{Im}z<0.\end{cases}$$
--
--   For $R>0$ and $u$ continuous on the circle $|z|=R$, the function $\widetilde{\mathcal{P}}_R[u]$ is continuous on the closed disc $|z|\le R$, which allows maximum-principle comparisons between the Poisson extension and its boundary data. If $u$ vanishes on the real axis, then $u^{\mathrm{odd}}(\overline{z})=-u^{\mathrm{odd}}(z)$ for all $z$. These objects are the ingredients of the Schwarz reflection principle for harmonic functions: for $R>0$, a function harmonic on $D_R^{+}$, continuous on $\overline{D}{}_R^{+}$ and zero on the real axis agrees on $D_R^{+}$ with the real part of the Herglotz–Riesz integral of its odd reflection, and therefore extends harmonically to the whole disc $|z|<R$.
--
--   **Formalization Note** The four objects are `poissonClosed R u`, `upperBall R`, `upperClosedBall R` and `oddUpper u`. The Poisson integral $\mathcal{P}_R[u]$ is `poissonExtension R u`, a Mathlib circle average (equal to $0$ when the integrand is not integrable). If $R\le0$ the open disc is empty and $\widetilde{\mathcal{P}}_R[u]=u$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HarmonicReflection.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HarmonicReflection.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_132

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

def poissonClosed (R : ℝ) (u : ℂ → ℝ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ ball 0 R then poissonExtension R u z else u z

def upperBall (R : ℝ) : Set ℂ := ball 0 R ∩ {z | 0 < z.im}

def upperClosedBall (R : ℝ) : Set ℂ := closedBall 0 R ∩ {z | 0 ≤ z.im}

def oddUpper (u : ℂ → ℝ) (z : ℂ) : ℝ := if 0 ≤ z.im then u z else -u (conj z)

end Conformal

end DirectCrouzeix

end

end

end

end OAI


