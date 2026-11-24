-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PDownTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PDownTop
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:34:13.686257+00:00
-- url     : https://prove2.me/theorems/8f357baf-abbc-492d-9330-ff562c9aebbc
-- title:
--   PDown Top
-- statement:
--   Definitions and structural lemmas for PDown Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PDownTop.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_DensLemmaOfCut
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
structure TopModel where
  V : Type
  [ng : NormedAddCommGroup V]
  [ns : NormedSpace ℂ V]
  [cs : CompleteSpace V]
attribute [instance] TopModel.ng TopModel.ns TopModel.cs
def TopDensity (C₂ C CV : ℕ) : Prop :=
  StepAdm CV → ∀ m : ℕ, ZeroUpTo CV m →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) (μR : Measure (Mt k r))
    (θ : B.SS k r → ℝ) (i : ℕ),
    B.IsHaarOn (Rset γ) μR → Hyps CV D A ε mm F' →
    IsRelevant D γ → 0 < Gf k r D.z D.z' γ → zc D γ ≤ m + 1 → HasRun D γ i (r + 1) → admitted D γ μR θ →
    Integrable (fun p => θ p • (B.xiTau D (1, 1) p • B.rho D p F' γ)) D.μSS →
    ∃ (β : ℂ) (p m' : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (M : TopModel)
      (Φ0 : G.Mat (p + (m' + 1 + 1)) → M.V) (e : ℕ → ℝ) (K Cp : ℝ) (P : Seminorm ℂ M.V) (D' z₀ : ℂ),
      β ≠ 0 ∧ (∀ a, d a ≠ 0) ∧ p + (m' + 1 + 1) = r + 1 ∧ D' ≠ 0 ∧
      z₀ ∈ G.rootSet (m' + 2) ((-1) ^ (m' + 3) * D') ∧ 0 ≤ Cp ∧ (∀ v, P v ≤ Cp * ‖v‖) ∧
      U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        (A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) / (5 * ((r : ℝ) + 1))
          - (C : ℝ) * (r : ℝ) ^ 2 ≤ e j / (5 * ((r : ℝ) + 1))) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ t c : ℂ, t ≠ 0 → ‖t‖ < δ → c * t ^ (m' + 1) = D' →
        P (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c) = 0) ∧
      (P (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z₀) = 0 → orbI D γ θ F' = 0)
end PI.UnitaryGroupMassFormula.DLm


