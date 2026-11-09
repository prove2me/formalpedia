-- Prove2me | Definitions.Def_QMatVecLB_ConvexOpt_DualWitness
-- name    : QMatVecLB_ConvexOpt_DualWitness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:12:56.236201+00:00
-- url     : https://prove2.me/theorems/133e9d48-cc8c-4dfe-9deb-cbe9c2023347
-- title:
--   Definition 3.2 — arbitrary finite complex dual witnesses
-- statement:
--   A pair of finite complex measures is represented by two integrable complex densities with respect to a common arbitrary finite measure. Their variation masses are the integrals of the density norms. A rank-$r$ dual witness has positive first mass, its first density vanishes almost everywhere outside the promise set, and the plus-sign Fourier transform of the sum vanishes on every matrix of rank at most $r$. Every pair of finite complex measures admits this representation using the sum of its variation measures, so atomic and singular witnesses are retained. No Lebesgue-density restriction is imposed.
-- source:
--   Andrew M. Childs, Quantum lower bounds for convex optimization and real matrix-vector query problems, STOC 2027 submission #252 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/252.pdf, definitions in Sections 2–3, 5–6; anchor PDF p. 6 (printed p. 5).

import Mathlib
import Definitions.Def_QMatVecLB_ConvexOpt_Calculus

noncomputable section

namespace QMatVecLB.ConvexOpt
open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise

/-- A pair of finite complex measures using a common finite dominating measure.
The base need not be Lebesgue measure; singular and atomic witnesses are included. -/
structure WitnessMeasures (n : ℕ) where
  base : Measure (RMat n)
  finite_base : IsFiniteMeasure base
  density0 : RMat n → ℂ
  density1 : RMat n → ℂ
  integrable0 : Integrable density0 base
  integrable1 : Integrable density1 base

def WitnessMeasures.mass0 {n : ℕ} (ξ : WitnessMeasures n) : ℝ :=
  ∫ A, ‖ξ.density0 A‖ ∂ξ.base
def WitnessMeasures.mass1 {n : ℕ} (ξ : WitnessMeasures n) : ℝ :=
  ∫ A, ‖ξ.density1 A‖ ∂ξ.base
def WitnessMeasures.integral {n : ℕ} (ξ : WitnessMeasures n) (F : RMat n → ℂ) : ℂ :=
  ∫ A, F A * (ξ.density0 A + ξ.density1 A) ∂ξ.base

/-- Definition 3.2. D enters only the correlation, not this witness predicate. -/
def IsDualWitness {n : ℕ} (ξ : WitnessMeasures n) (P : Set (RMat n)) (r : ℕ) : Prop :=
  0 < ξ.mass0 ∧
  (∀ᵐ A ∂ξ.base, A ∉ P → ξ.density0 A = 0) ∧
  ∀ M ∈ rankVariety n r, ξ.integral (fun A => phaseExp (matrixPair A M)) = 0

end QMatVecLB.ConvexOpt
end


