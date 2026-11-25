-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:17.406442+00:00
-- url     : https://prove2.me/theorems/027d999c-cc06-59d0-9a65-e0b66419a4a8
-- title:
--   PFrames Cut
-- statement:
--   Definitions and structural lemmas for PFrames Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFramesCut.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopDensFr
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
def fdMaj (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (A : ℝ) (g : B.Mat k r) : ENNReal :=
  ∫⁻ x : B.SS k r, ENNReal.ofReal (B.gN (B.sgs x g) ^ (-A)) ∂((D.μW.prod μ0).prod (D.μW'.prod μ0'))
def FdLocal (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r))
    (L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq)) : Prop :=
  ∀ g₀ ∈ B.GV k r, 0 < Gf k r D.z D.z' g₀ → ∃ (O : Set (B.Mat k r)) (Λ₁ : B.Mat k r → (Wp →L[ℂ] Wp))
    (Λ₂ : B.Mat k r → (Wq →L[ℂ] Wq)), IsOpen O ∧ g₀ ∈ O ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ₁ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Λ₂ O ∧
    ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r D.z D.z' g → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp),
      frVal D μ0 μ0' F L g = (Λ₁ g).comp ((fibInt D μ0 μ0' F g).comp (Λ₂ g))
end
def FdGram : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), 1 ≤ r → B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∃ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L ∧ FdLocal D μ0 μ0' L
def FdLifts : Prop :=
  FibreBound → ∃ Cl : ℕ, ∀ C₂ : ℕ, ∃ CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∀ μ0 μ0' : Measure (Mt k r), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L → FdLocal D μ0 μ0' L →
    ∃ K : ℝ, ContDiff ℝ (C₂ * (m' + 2) ^ 2) (phi0 D μ0 μ0' L F' hps) ∧
      ∀ i ≤ C₂ * (m' + 2) ^ 2, ∀ Z : G.Mat (p + (m' + 1 + 1)),
        ((∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → castM hps.symm (Zhat k r D.z D.z' g) ≠ Z) →
          iteratedFDeriv ℝ i (phi0 D μ0 μ0' L F' hps) Z = 0) ∧
        ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → castM hps.symm (Zhat k r D.z D.z' g) = Z →
          ENNReal.ofReal ‖iteratedFDeriv ℝ i (phi0 D μ0 μ0' L F' hps) Z‖ ≤
            ENNReal.ofReal K * fdMaj D μ0 μ0' (A - (Cl : ℝ) * r * i) g
def FdDecayOf : Prop :=
  FibreBound → FdLifts → ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∀ μ0 μ0' : Measure (Mt k r), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ L : B.Mat k r → (Wp ≃L[ℂ] Wp) × (Wq ≃L[ℂ] Wq), IsFrameAlg D μ0 μ0' L → FdLocal D μ0 μ0' L →
    ∃ K : ℝ, U.DecayAll (C₂ * (m' + 2) ^ 2)
        (fun j => A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j)) K
        (phi0 D μ0 μ0' L F' hps)
end PI.UnitaryGroupMassFormula.DLm


