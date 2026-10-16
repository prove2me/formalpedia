-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
-- name    : OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:52:11.927181+00:00
-- url     : https://prove2.me/theorems/79e575f3-268e-4d8a-8d06-f169ec1f4f5c
-- title:
--   Log-determinant deficits of skew-Hermitian and Schur-complement perturbations
-- statement:
--   Let $\mathcal I$ and $\mathcal J$ be finite index sets. All matrices are complex, $Z^*$ is the conjugate transpose, $|\cdot|$ is the modulus of a complex number and $\log$ is the natural logarithm.
--
--   1. **Skew-shift deficit.** For $\mathcal I\times\mathcal I$ matrices $Z$ and $D$,
--   $$\operatorname{skewLogDet}(Z,D)=\log\bigl|\det(D+Z)\bigr|-\log\bigl|\det D\bigr|.$$
--   It is used for skew-Hermitian $Z$ ($Z^*=-Z$) and positive definite $D$; then $\det(D+Z)$ is in general not real, which is why the modulus is taken.
--   2. **Block (Schur-complement) deficit.** For an $\mathcal I\times\mathcal J$ matrix $Z$, an $\mathcal I\times\mathcal I$ matrix $D$ and a $\mathcal J\times\mathcal J$ matrix $E$,
--   $$\operatorname{blockLogDet}(Z,D,E)=\log\bigl|\det(D+Z\,E^{-1}Z^{*})\bigr|-\log\bigl|\det D\bigr|.$$
--   For positive definite $D$ and $E$ it coincides with the skew-shift deficit of the block matrices $\begin{pmatrix}0&Z\\-Z^*&0\end{pmatrix}$ and $\begin{pmatrix}D&0\\0&E\end{pmatrix}$, by the Schur-complement formula for the determinant.
--
--   The main facts proved about these functions are convexity statements: for a fixed skew-Hermitian $Z$ the map $D\mapsto\operatorname{skewLogDet}(Z,D)$ is convex on the cone of positive definite matrices, and consequently, for every rectangular $Z$, the map $(D,E)\mapsto\operatorname{blockLogDet}(Z,D,E)$ is jointly convex on pairs of positive definite matrices. Through resolvent determinants $\log\det(\mathbf 1+rA)$ this joint convexity is turned into entropy inequalities for outputs of the generalized amplitude-damping channel.
--
--   **Formalization Note** The names are `skewLogDet Z D` and `blockLogDet Z D E`. Lean's matrix inverse `E⁻¹` is the zero matrix when `E` is singular, and `Real.log 0 = 0`; these conventions only matter outside the positive definite range.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- The skew-shift log-determinant deficit, including non-real determinants. -/
def skewLogDet (Z D : Matrix ι ι ℂ) : ℝ :=
  Real.log ‖(D + Z).det‖ - Real.log ‖D.det‖

end GAD

open scoped ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def blockLogDet (Z : Matrix ι κ ℂ) (D : Matrix ι ι ℂ) (E : Matrix κ κ ℂ) : ℝ :=
  Real.log ‖(D + Z * E⁻¹ * Zᴴ).det‖ - Real.log ‖D.det‖

end GAD

end

end OAI


