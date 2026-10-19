-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_HolomorphicReflection
-- name    : OAI_Analysis_DirectCrouzeix_HolomorphicReflection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:01:37.180472+00:00
-- url     : https://prove2.me/theorems/c7283f37-6cd8-4160-bc8c-8dcf3148c9a0
-- title:
--   Logarithm of the modulus on the upper half-plane, extended by zero
-- statement:
--   For a function $f:\mathbb{C}\to\mathbb{C}$ define $\ell_f:\mathbb{C}\to\mathbb{R}$ by
--   $$\ell_f(z)=\begin{cases}\log|f(z)|, & \operatorname{Im}z>0,\\ 0, & \operatorname{Im}z\le0.\end{cases}$$
--   Thus $\ell_f$ records $\log|f|$ in the open upper half-plane and is identically zero on the real axis and in the lower half-plane.
--
--   This is the real-valued function to which harmonic reflection is applied in the holomorphic reflection principle for functions whose modulus tends to $1$ at a real segment. If $R>0$, $f$ is continuous and zero-free on $\{|z|\le R,\ \operatorname{Im}z>0\}$, and $|f(w)|\to1$ as $w$ tends from the upper half-plane to any real point of the closed disc $|z|\le R$, then $\ell_f$ is continuous on the closed upper half-disc $\{|z|\le R,\ \operatorname{Im}z\ge0\}$ and vanishes on the real axis; where $f$ is moreover holomorphic, $\ell_f$ is harmonic. Reflecting $\ell_f$ oddly across the real axis and taking a holomorphic function with that real part leads to a holomorphic continuation of $f$ to the whole disc, of modulus $1$ on the real diameter.
--
--   **Formalization Note** $\ell_f$ is `logModulusUpper f`, built from `Real.log` of the complex norm. Lean's convention $\log0=0$ means that $\ell_f(z)=0$ also at zeros of $f$ in the upper half-plane; in the intended applications $f$ has no zeros there.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/HolomorphicReflection.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HolomorphicReflection.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

def logModulusUpper (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < z.im then Real.log ‖f z‖ else 0

end Conformal

end DirectCrouzeix

end

end

end

end OAI


