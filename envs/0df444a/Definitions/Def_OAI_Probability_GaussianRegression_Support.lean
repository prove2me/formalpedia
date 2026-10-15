-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Support
-- name    : OAI_Probability_GaussianRegression_Support
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:08:58.855967+00:00
-- url     : https://prove2.me/theorems/367d48cf-c539-48c5-98c3-c715a0c53d5f
-- title:
--   Euclidean label norms, the row operator of a design, and net enclosures of exact observations
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra and let $m\in\mathbb{N}$. The file defines:
--
--   1. **Euclidean norm of labels.** For $y\in\mathbb{R}^{m}$, $\|y\|_2=\big(\sum_{j<m}y_j^{2}\big)^{1/2}$; the file records that it is continuous.
--
--   2. **Euclidean label ball.** For $r\in\mathbb{R}$,
--      $$B_m(r)=\{y\in\mathbb{R}^{m}:\ \|y\|_2\le r\},$$
--      which is empty when $r<0$.
--
--   3. **Row operator.** For a design $A=(A_0,\dots,A_{m-1})\in E^{m}$, the continuous linear map
--      $$R_A:E\to\ell_2^{m},\qquad R_A\,t=\big(\langle A_0,t\rangle,\dots,\langle A_{m-1},t\rangle\big),$$
--      where $\ell_2^{m}$ is $\mathbb{R}^{m}$ with the Euclidean norm; it is the matrix with rows $A_j$.
--
--   4. **Net enclosure.** For a finite set $S\subseteq E$,
--      $$D_m(S)=\bigcup_{u\in S}\Big\{(A,y)\in E^{m}\times\mathbb{R}^{m}:\ \|y\|_2\le 2\,\big\|\big(\langle u,A_j\rangle\big)_{j<m}\big\|_2\Big\}.$$
--
--   If $S$ is a $\tfrac12$-net of the closed unit ball, then $\|R_A\,t\|_2\le 2\max_{u\in S}\|R_A\,u\|_2$ whenever $\|t\|\le1$, so every exact observation $(A,R_A\,t)$ with $\|t\|\le1$ lies in $D_m(S)$. On the other hand, for $S$ inside the unit ball, $D_m(S)$ has measure at most $|S|\cdot32^{m}$ under the product of the standard Gaussian row law on $E^{m}$ and Lebesgue measure on labels. Together this gives a set of bounded reference volume that carries all noiseless observations of vectors in the unit ball.
--
--   **Formalization Note** The Lean names are `coordinateNorm` (with `continuous_coordinateNorm`), `coordinateBall m r`, `rowOperator A`, valued in `EuclideanSpace ℝ (Fin m)`, and `netProjectionSupport S m`. In Mathlib the type `Fin m → ℝ` carries the sup norm, which is why the Euclidean norm is introduced explicitly through `WithLp.toLp 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Support.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Support.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_GaussianRegression_Projection

namespace OAI

/-!
Finite-volume enclosures for Gaussian matrix observations.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

open scoped Pointwise

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

def rowOperator {m : ℕ} (A : Fin m → E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

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

end NoiselessRegression

end

end OAI


