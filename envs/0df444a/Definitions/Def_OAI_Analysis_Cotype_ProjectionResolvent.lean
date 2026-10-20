-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
-- name    : OAI_Analysis_Cotype_ProjectionResolvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:08:40.776397+00:00
-- url     : https://prove2.me/theorems/65c5af60-4811-405b-b110-05e4cfb65e48
-- title:
--   Timed shift integrals of the generator
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. The spectral patterns $Q_\varepsilon=\prod_i(1-P_i\text{ or }P_i)$ of commuting projections decompose the identity, and $\widehat{\cdot}$ denotes the complex dual lift; functions $f$ of the pattern give $f(P)=\sum_\varepsilon f(\varepsilon)\widehat{Q_\varepsilon}$. Let $G$ be the generator.
--
--   1. **Shift integral.** For $z\in\mathbb C$ and $t\ge0$,
--   $$
--   J_z(t)=e^{-zt}\int_0^te^{s(z-G)}\,ds .
--   $$
--   Since $(z-G)J_z(t)=1-e^{-tG}$, controlling $J_z(t)$ and the decay of $e^{-tG}$ inverts $z-G$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionResolvent.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionResolvent.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral

namespace OAI

noncomputable section
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def projectionShiftIntegral {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (z : ℂ) (t : ℝ) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  Complex.exp (-(z * (t : ℂ))) •
    exponentialIntegral (z • 1 - projectionGenerator P) t

end Cotype

end

end OAI


