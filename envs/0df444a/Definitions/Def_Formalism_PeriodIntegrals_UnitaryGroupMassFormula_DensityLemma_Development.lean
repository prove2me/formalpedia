-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_Development
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:56:08.848793+00:00
-- url     : https://prove2.me/theorems/39bc943d-96e6-41f7-b867-64eedb030a49
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/Development.lean

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace PI.UnitaryGroupMassFormula.DLm
section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
def admitted (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ) : Prop :=
  Measurable θ ∧ (∀ p, 0 ≤ θ p) ∧ ∀ p, D.inSS p → ∫ x, θ (actR γ (Matrix.of x) p) ∂μR = 1
def orbI (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (θ : B.SS k r → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) :
    Wq →L[ℂ] Wp :=
  ∫ p, θ p • (B.xiTau D (1, 1) p • B.rho D p F γ) ∂D.μSS
def zc (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) : ℕ :=
  (Finset.univ.filter fun l : Fin (r + 2) => Dmin k r D.z D.z' γ l = 0).card
end
def StepAdm (CV : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r)),
    B.IsHaarOn (Rset γ) μR →
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ →
    ∃ θ : B.SS k r → ℝ, admitted D γ μR θ ∧
      Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS
def ZeroUpTo (CV m : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
    B.IsHaarOn (Rset γ) μR →
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    (∀ g ∈ bigPos D, B.JF D F' g = 0) →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    orbI D γ θ F' = 0
def StepBig (CV : ℕ) : Prop := ZeroUpTo CV 0
def StepDown (CV : ℕ) : Prop := ∀ m : ℕ, ZeroUpTo CV m → ZeroUpTo CV (m + 1)
end PI.UnitaryGroupMassFormula.DLm


