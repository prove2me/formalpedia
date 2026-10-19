-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
-- name    : OAI_Probability_Subsphere_Geometry_MassBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:49:45.542609+00:00
-- url     : https://prove2.me/theorems/94b71af4-dc07-440c-8c2f-d045c42e5954
-- title:
--   Radius-weighted values on affine tests, spherical density measures and completion of sub-probability routes
-- statement:
--   Write $S^{d-1}$ for the unit sphere of $\mathbb{R}^d$. An $n$-dimensional affine test $A$ in $\mathbb{R}^d$ consists of a linear subspace $K_A$ of dimension $n$, a centre $c_A\in K_A^\perp$ and a radius $r_A>0$ with $\|c_A\|^2+r_A^2=1$; for $s$ in the unit sphere $S_{K_A}$ of $K_A$, the point $c_A+r_As$ lies on $S^{d-1}$.
--
--   1. **Radius-weighted value on a test.** For $g:S^{d-1}\to[0,\infty]$ and $s\in S_{K_A}$,
--   $$g_A(s)=r_A^{\,d/16}\;g\bigl(c_A+r_A s\bigr),$$
--   where the exponent $d/16$ is the real number $d/16$.
--   2. **Spherical density measure.** Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, $S_E$ its unit sphere and $\sigma_E$ the uniform law on $S_E$. For $g:S_E\to[0,\infty]$, $\mu_g$ is the measure on $E$ with density $\tilde g$ (the radial extension $\tilde g(x)=g(x/\|x\|)$, $\tilde g(0)=0$) with respect to the image of $\sigma_E$ in $E$; for measurable $U\subseteq E$,
--   $$\mu_g(U)=\int_{S_E}\mathbf 1_U(s)\,g(s)\,d\sigma_E(s).$$
--   3. **Completion of a route.** For a finite set $V$, an element $v_0\in V$ and weights $w:V\to[0,\infty]$ with $\sum_{v}w(v)\le1$, the probability distribution
--   $$p(v)=w(v)+\mathbf 1[v=v_0]\Bigl(1-\sum_{u\in V}w(u)\Bigr),\qquad v\in V,$$
--   which puts the missing mass on $v_0$.
--
--   The radius-weighted values are the integrands of the weighted norm of the main estimate, in which a function $g$ on $S^{d-1}$ is measured by the supremum over $n$-dimensional tests $A$ of $\int g_A\,d\sigma_{K_A}$. The spherical density measure turns a function on the sphere into a measure on the ambient space, to which mass bounds apply. The completion turns sub-probability weights, such as block kernels $\kappa_v$ with $\sum_v\kappa_v\le1$, into a genuine probability distribution by routing the deficit to a default element.
--
--   **Formalization Note** `Weighted.weightedOnTest A g s` (with `(ENNReal.ofReal A.radius)^((d : ℝ)/16)`), `Weighted.sphereDensity g` (`ambientSphereLaw.withDensity (Polar.radial g)`) and `Weighted.completeRoute v₀ w hw : PMF V`. The difference $1-\sum w$ is truncated subtraction in `ℝ≥0∞`, which is exact here because of the hypothesis $\sum w\le1$. The `[Nontrivial E]` and `[Nonempty V]` assumptions of the surrounding sections are not arguments of these definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Geometry/MassBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Geometry/MassBounds.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace SubsphereCurrent.Weighted
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace

def weightedOnTest {d n : ℕ} (A : Affine.Test d n) (g : Sphere d → ℝ≥0∞)
    (s : Affine.Sphere A.space) : ℝ≥0∞ :=
  (ENNReal.ofReal A.radius)^((d : ℝ)/16) * g (onTest A s)

section Ambient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

def sphereDensity (g : Metric.sphere (0 : E) 1 → ℝ≥0∞) : Measure E :=
  (SubsphereRegression.ambientSphereLaw (E := E)).withDensity (Polar.radial g)

end Ambient

variable {V : Type*} [Fintype V] [Nonempty V]

def completeRoute (v₀ : V) (w : V → ℝ≥0∞) (hw : ∑ v, w v ≤ 1) : PMF V := by
  classical
  refine ⟨fun v => w v + if v = v₀ then 1-∑ i, w i else 0,?_⟩
  have he : (∑ v, (w v + if v = v₀ then 1-∑ i, w i else 0)) = 1 := by
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact add_tsub_cancel_of_le hw
  have hh := hasSum_fintype (fun v => w v + if v=v₀ then 1-∑ i, w i else 0)
  rw [he] at hh
  exact hh

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {V : Type*} [Fintype V] [Nonempty V] [MeasurableSpace V] [MeasurableSingletonClass V]

end SubsphereCurrent.Weighted

end

end OAI


