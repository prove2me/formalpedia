-- Prove2me | Definitions.Def_Kall1976_RecourseDifferentiability
-- name    : Kall1976_RecourseDifferentiability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:12:30.091989+00:00
-- url     : https://prove2.me/theorems/3fc23f83-dd82-4701-bd34-5157d45d3cdb
-- title:
--   Fixed-recourse data, feasible domain, signed expectation, and moment alternatives
-- statement:
--   The joint random recourse data, the almost-sure feasible first-stage domain, the signed extended expected recourse, and exactly the four moment alternatives used in Kall's Theorems 12 and 15.
-- source:
--   Peter Kall, Stochastic Linear Programming, Springer, 1976, Chapter III, equations (4)-(5) printed p. 41 / PDF47, equation (8) printed p. 44 / PDF50, Theorem 10 printed p. 46 / PDF52, and Corollary 11 printed pp. 47-48 / PDF53-54. https://doi.org/10.1007/978-3-642-66252-2.

import Definitions.Def_KallMayer_Recourse_ExpectedRecourse

open MeasureTheory

namespace Kall1976

/-- Full coefficient space, in the source order (A,b,q). -/
abbrev RecourseData (m n p : ℕ) :=
  (Fin m → Fin n → ℝ) × (Fin m → ℝ) × (Fin p → ℝ)

/-- III.(5), p.41: feasibility almost surely, without complete recourse. -/
def recourseDomain {m n p : ℕ} (μ : Measure (RecourseData m n p))
    (W : Matrix (Fin m) (Fin p) ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ᵐ d ∂μ, KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x < ⊤}

/-- III.(8): positive-part integral minus negative-part integral.
The theorem's moment hypotheses make the positive part finite on K, so the
source's exclusion of negative infinite expectation is meaningful there. -/
noncomputable def extendedExpectedRecourse {m n p : ℕ}
    (μ : Measure (RecourseData m n p)) (W : Matrix (Fin m) (Fin p) ℝ)
    (x : Fin n → ℝ) : EReal :=
  ((∫⁻ d, (KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal ∂μ) : EReal) -
  ((∫⁻ d, (-KallMayer.Recourse.PointwiseRecourse W d.1 d.2.1 d.2.2 x).toENNReal ∂μ) : EReal)

/-- Exactly the four alternatives cited by III.12. Finite-dimensional vector
integrability is equivalent to entrywise integrability. Constants and bounded
ranges are stated almost surely, which leaves the data law unchanged. -/
def recourseMomentAlternative {m n p : ℕ} (μ : Measure (RecourseData m n p)) : Prop :=
  (MemLp (fun d => d.1) 2 μ ∧ MemLp (fun d => d.2.1) 2 μ ∧
    MemLp (fun d => d.2.2) 2 μ) ∨
  ((∃ q : Fin p → ℝ, ∀ᵐ d ∂μ, d.2.2 = q) ∧
    Integrable (fun d => d.1) μ ∧ Integrable (fun d => d.2.1) μ) ∨
  ((∃ (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      ∀ᵐ d ∂μ, d.1 = A ∧ d.2.1 = b) ∧ Integrable (fun d => d.2.2) μ) ∨
  (∃ C : ℝ, ∀ᵐ d ∂μ, ‖d.1‖ ≤ C ∧ ‖d.2.1‖ ≤ C ∧ ‖d.2.2‖ ≤ C)

end Kall1976


