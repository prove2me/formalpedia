-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
-- name    : OAI_Probability_Subsphere_Regression_Projection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:33:22.64837+00:00
-- url     : https://prove2.me/theorems/992815fc-3a38-45b2-a073-e01a49200fa5
-- title:
--   Gaussian matrix–label reference law, noiseless and noisy projection laws, and row operators
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\gamma_E$ be the standard Gaussian measure on $E$ (the law of $\sum_i\xi_ie_i$ for an orthonormal basis $(e_i)$ and independent standard normal $\xi_i$), and let $m\in\mathbb{N}$. An observation is a pair $(A,y)\in E^m\times\mathbb{R}^m$ of $m$ rows and $m$ labels, and $|y|_2=\bigl(\sum_j y_j^2\bigr)^{1/2}$ is the Euclidean norm of a label vector.
--
--   1. **Reference law.** $\Lambda_m=\gamma_E^{\otimes m}\otimes\mathrm{Leb}_{\mathbb{R}^m}$: independent Gaussian rows and Lebesgue measure on the labels.
--   2. **Projection law.** For a measure $\nu$ on $E$, $P_{\nu,m}$ is the image of $\gamma_E^{\otimes m}\otimes\nu$ under $(A,t)\mapsto\bigl(A,(\langle t,A_j\rangle)_{j<m}\bigr)$: the joint law of Gaussian rows and the noiseless labels of a hidden vector $t\sim\nu$.
--   3. **Gaussian coupling.** For a measure $\nu$ on $E$, the measure $\gamma_E^{\otimes m}\otimes\bigl(\nu\otimes N(0,1)^{\otimes m}\bigr)$ on $E^m\times(E\times\mathbb{R}^m)$, carrying rows $A$, a hidden vector $t$ and standard normal noise $\xi$.
--   4. **Noisy observation.** For a noise level $\delta\in\mathbb{R}$, the map
--   $$\bigl(A,(t,\xi)\bigr)\longmapsto\Bigl(A,\ \bigl(\langle t,A_j\rangle+\delta\,\xi_j\bigr)_{j<m}\Bigr),$$
--   so that the image of the Gaussian coupling is the law of rows with labels corrupted by independent Gaussian noise of standard deviation $|\delta|$.
--   5. **Euclidean norm and ball of label vectors.** The function $y\mapsto|y|_2$ on $\mathbb{R}^m$, together with the fact that it is continuous, and for $r\in\mathbb{R}$ the closed ball $\{y\in\mathbb{R}^m:|y|_2\le r\}$.
--   6. **Row operator.** For rows $A\in E^m$, the continuous linear map $E\to\mathbb{R}^m$ (Euclidean norm on the target) given by $x\mapsto(\langle A_j,x\rangle)_{j<m}$.
--   7. **Net enclosure.** For a finite set $S\subset E$,
--   $$D(S,m)=\bigcup_{u\in S}\Bigl\{(A,y)\in E^m\times\mathbb{R}^m:\ |y|_2\le 2\,\bigl|(\langle u,A_j\rangle)_{j<m}\bigr|_2\Bigr\}.$$
--
--   The projection law $P_{\nu,m}$ is the object whose mass on sets is compared with the reference law $\Lambda_m$; the Gaussian coupling and the noisy observation map realize its noise-smoothed version, whose density with respect to $\Lambda_m$ is a projection smoothing of $\nu$; and $D(S,m)$ is a measurable common enclosure of the supports of noiseless observation laws, indexed by a finite net $S$ of inputs.
--
--   **Formalization Note** Names: `matrixLabelReference`, `projectionLaw`, `gaussianCoupling`, `noisyObservation`, `coordinateNorm` (with the continuity lemma `continuous_coordinateNorm`), `coordinateBall`, `rowOperator` and `netProjectionSupport`. Lebesgue measure on $\mathbb{R}^m$ is `volume` on `Fin m → ℝ`, and $N(0,1)$ is `gaussianReal 0 1`. `coordinateNorm` passes through `WithLp 2` because the plain function space `Fin m → ℝ` carries the sup norm in Mathlib. The measures are defined for an arbitrary measure $\nu$; `noisyObservation`, `rowOperator` and `netProjectionSupport` use only the inner product of $E$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Projection.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Projection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section ProjectionCoupling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def matrixLabelReference (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  (Measure.pi (fun _ => stdGaussian E)).prod volume

def projectionLaw (ν : Measure E) (m : ℕ) : Measure ((Fin m → E) × (Fin m → ℝ)) :=
  ((Measure.pi (fun _ => stdGaussian E)).prod ν).map
    (fun z => (z.1, fun j => ⟪z.2, z.1 j⟫))

def gaussianCoupling (ν : Measure E) (m : ℕ) :
    Measure ((Fin m → E) × (E × (Fin m → ℝ))) :=
  (Measure.pi (fun _ => stdGaussian E)).prod
    (ν.prod (Measure.pi (fun _ => gaussianReal 0 1)))

def noisyObservation (m : ℕ) (δ : ℝ)
    (z : (Fin m → E) × (E × (Fin m → ℝ))) : (Fin m → E) × (Fin m → ℝ) :=
  (z.1, fun j => ⟪z.2.1, z.1 j⟫ + δ * z.2.2 j)

end ProjectionCoupling

open scoped Pointwise

/-- The Euclidean norm of an ordinary finite coordinate tuple. -/
def coordinateNorm {m : ℕ} (y : Fin m → ℝ) : ℝ := ‖WithLp.toLp 2 y‖

@[fun_prop] lemma continuous_coordinateNorm {m : ℕ} :
    Continuous (coordinateNorm (m := m)) := by
  unfold coordinateNorm
  fun_prop

def coordinateBall (m : ℕ) (r : ℝ) : Set (Fin m → ℝ) :=
  {y | coordinateNorm y ≤ r}

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Linear noiseless observation operator, with the Euclidean output norm. -/
def rowOperator {m : ℕ} (A : Fin m → E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

/-- A measurable common support enclosure indexed by a finite input net. -/
def netProjectionSupport (s : Finset E) (m : ℕ) :
    Set ((Fin m → E) × (Fin m → ℝ)) :=
  ⋃ u ∈ s, {z | coordinateNorm z.2 ≤ 2 * coordinateNorm (fun j => ⟪u, z.1 j⟫)}

end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end NetNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end SubsphereRegression

end

end OAI


