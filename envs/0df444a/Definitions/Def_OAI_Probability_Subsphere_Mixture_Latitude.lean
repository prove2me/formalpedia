-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude
-- name    : OAI_Probability_Subsphere_Mixture_Latitude
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:59:19.088466+00:00
-- url     : https://prove2.me/theorems/2d71fcc0-f8a5-4c9e-a39b-ed82338c8b05
-- title:
--   Direction law of a uniform unit vector of a subspace under Haar rotations fixing another subspace
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, and let $V,N\subseteq E$ be linear subspaces (no inclusion between them is assumed here). Write $V^{\perp}$ for the orthogonal complement of $V$, $O(V^{\perp})$ for its orthogonal group with the Haar probability measure $\mathfrak h_{V^\perp}$, and $\sigma_N$ for the uniform probability measure on the unit sphere of $N$, regarded as a measure on $N$. For $w\in O(V^{\perp})$ let $B_V(I,w)$ be the orthogonal map of $E$ that is the identity on $V$ and acts by $w$ on $V^{\perp}$, i.e. $B_V(I,w)x=P_Vx+w(P_{V^\perp}x)$ with $P_V,P_{V^\perp}$ the orthogonal projections. The direction law of the pair $(V,N)$ is the image measure
--   $$D_{V,N}=\bigl((w,x)\mapsto B_V(I,w)\,x\bigr)_{\#}\bigl(\mathfrak h_{V^\perp}\otimes\sigma_N\bigr),$$
--   the law of $B_V(I,W)X$ for independent $W\sim\mathfrak h_{V^\perp}$ and $X\sim\sigma_N$. This file establishes two basic facts about it.
--
--   1. **Measurable sampler.** The map $O(V^{\perp})\times N\to E$, $(w,x)\mapsto B_V(I,w)x$, is measurable (it is continuous).
--   2. **Normalization.** If $N\ne\{0\}$, then $D_{V,N}$ is a probability measure on $E$.
--
--   When $V\subseteq N$, $D_{V,N}$ describes a uniformly random unit vector of $N$ after a Haar-random rotation that fixes $V$ pointwise; it is the law that the spherical mixture estimate dominates by the uniform law on the sphere of $E$ plus a latitude law. Beyond the two entries above, the module proves that for $N\ne\{0\}$ the law $D_{V,N}$ is concentrated on the unit sphere and, when $V\subseteq N$, invariant under the block-diagonal orthogonal maps of $V\oplus V^{\perp}$, and that under it the squared length $\|P_{V^\perp}x\|^{2}$ has law $\mathrm{Beta}\bigl(\tfrac{\dim N-\dim V}{2},\tfrac{\dim V}{2}\bigr)$ when $V\subseteq N$ and $0<\dim V<\dim N$.
--
--   **Formalization Note** $D_{V,N}$ is `directionLaw V N` and $B_V(u,w)$ is `blockIso V u w`, both from the base definitions; $\sigma_N$ is `SubsphereRegression.ambientSphereLaw (E := N)`. The entries are the lemma `measurable_directionSampler` and the instance `directionLaw_probability`, which takes `[Nontrivial N]`; for $N=\{0\}$ the sphere of $N$ is empty and $D_{V,N}$ is the zero measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Mixture/Latitude.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Latitude.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory

namespace OAI

noncomputable section

namespace SubsphereCurrent.Mixture
section
open MeasureTheory ProbabilityTheory Set

section
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma measurable_directionSampler (V N : Submodule ℝ E) :
    Measurable (fun z : Orthogonal Vᗮ × N => blockIso V 1 z.1 (z.2 : E)) :=
  ((continuous_blockIso V).comp
    ((continuous_const.prodMk continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).measurable

instance directionLaw_probability (V N : Submodule ℝ E) [Nontrivial N] :
    IsProbabilityMeasure (directionLaw V N) := by
  unfold directionLaw
  exact Measure.isProbabilityMeasure_map (measurable_directionSampler V N).aemeasurable

end
open scoped ENNReal NNReal

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture

end

end OAI


