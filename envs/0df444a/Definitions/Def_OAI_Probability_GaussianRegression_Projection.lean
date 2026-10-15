-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Projection
-- name    : OAI_Probability_GaussianRegression_Projection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:05:53.08859+00:00
-- url     : https://prove2.me/theorems/a6a55499-87c1-4e66-a643-16b8df716a81
-- title:
--   Gaussian design with exact or noisy projection labels: reference measure, joint law and coupling
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\gamma_E$ be its standard Gaussian measure (the law of $\sum_i g_ie_i$ for an orthonormal basis $(e_i)$ and independent standard normal $g_i$), let $\lambda_m$ be Lebesgue measure on $\mathbb{R}^{m}$, and let $\mathcal N(0,1)$ be the standard normal law on $\mathbb{R}$. Fix the number of observations $m\in\mathbb{N}$ and a measure $\nu$ on $E$. A design is $A=(A_0,\dots,A_{m-1})\in E^{m}$. The file defines:
--
--   1. **Reference measure.** On $E^{m}\times\mathbb{R}^{m}$,
--      $$\Lambda_m=\gamma_E^{\otimes m}\otimes\lambda_m ,$$
--      independent Gaussian rows together with Lebesgue-distributed labels.
--
--   2. **Noiseless projection law.** The push-forward
--      $$P_{\nu,m}=\big(\gamma_E^{\otimes m}\otimes\nu\big)\circ\Pi^{-1},\qquad \Pi(A,t)=\big(A,\ (\langle t,A_j\rangle)_{j<m}\big).$$
--      For a probability measure $\nu$, it is the joint law of the design and the exact labels when the unknown vector $t$ is drawn from $\nu$ independently of the Gaussian rows.
--
--   3. **Gaussian coupling.** On $E^{m}\times\big(E\times\mathbb{R}^{m}\big)$,
--      $$\Gamma_{\nu,m}=\gamma_E^{\otimes m}\otimes\big(\nu\otimes\mathcal N(0,1)^{\otimes m}\big),$$
--      which draws the rows, the unknown vector and independent standard normal noise variables $\xi_0,\dots,\xi_{m-1}$.
--
--   4. **Noisy observation map.** For a noise level $\delta\in\mathbb{R}$,
--      $$O_\delta\big(A,(t,\xi)\big)=\big(A,\ (\langle t,A_j\rangle+\delta\,\xi_j)_{j<m}\big).$$
--
--   Pushing $\Gamma_{\nu,m}$ forward by $O_0$ gives the noiseless law $P_{\nu,m}$. For $\delta\ne0$ the push-forward has an explicit density with respect to $\Lambda_m$, obtained by integrating products of the $\mathcal N(0,\delta^2)$ densities of $y_j-\langle t,A_j\rangle$ against $\nu(dt)$. Letting $\delta\to0$ transfers moment bounds for these densities to Hölder-type bounds $P_{\nu,m}(S)\le c\,\Lambda_m(S)^{1-1/(n+1)}$ for sets $S$ of observations, where $n\ge1$ and the constant $c$ depends on $\nu$, $m$ and $n$.
--
--   **Formalization Note** The Lean names are `matrixLabelReference m`, `projectionLaw ν m`, `gaussianCoupling ν m` and `noisyObservation m δ`. They use `stdGaussian E`, `gaussianReal 0 1` and `volume`, and labels are plain functions `Fin m → ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Projection.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Projection.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing

namespace OAI

/-!
Exact noiseless projection laws and completed-event bounds.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

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

end NoiselessRegression

end

end OAI


