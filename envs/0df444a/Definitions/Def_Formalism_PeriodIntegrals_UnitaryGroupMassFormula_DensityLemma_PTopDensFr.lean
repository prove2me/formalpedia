-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopDensFr
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopDensFr
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T06:08:36.050269+00:00
-- url     : https://prove2.me/theorems/4b0cc62b-a8e4-5ac3-9c74-6a401f2f66a2
-- title:
--   PTop Dens Fr
-- statement:
--   Definitions and structural lemmas for PTop Dens Fr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PTopDensFr.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopDensCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_comp

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
def frVal (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ((L g).1 : Wp →L[ℂ] Wp).comp ((fibInt D μ0 μ0' F g).comp ((L g).2 : Wq →L[ℂ] Wq))
def IsFrameAlg (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) : Prop :=
  (∀ g ∈ B.GV k r, 0 < Gf k r D.z D.z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      0 < Gf k r D.z D.z' (n⁻¹ * g * n') ∧ L (n⁻¹ * g * n') = L g) ∧
  (∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)), ∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r D.z D.z' g₁ →
      Zhat k r D.z D.z' g₁ = Zhat k r D.z D.z' g₂ → frVal D μ0 μ0' F L g₁ = frVal D μ0 μ0' F L g₂)
open Classical in

def phi0 (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) {p m' : ℕ} (hps : p + (m' + 1 + 1) = r + 1) :
    G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp) := fun Z =>
  if h : ∃ g, g ∈ B.GV k r ∧ 0 < Gf k r D.z D.z' g ∧ castM hps.symm (Zhat k r D.z D.z' g) = Z then
    frVal D μ0 μ0' F L (Classical.choose h) else 0
end
def UnipotentHaarExists : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z → ∃ μ : Measure (Mt k r), B.IsHaarOn (C2.N0set k r z) μ
def FramesDecay : Prop :=
  ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∀ μ0 μ0' : Measure (Mt k r), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∃ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L ∧ ∃ K : ℝ,
      U.DecayAll (C₂ * (m' + 2) ^ 2)
        (fun j => A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) K
        (phi0 D μ0 μ0' L F' hps)
end PI.UnitaryGroupMassFormula.DLm


