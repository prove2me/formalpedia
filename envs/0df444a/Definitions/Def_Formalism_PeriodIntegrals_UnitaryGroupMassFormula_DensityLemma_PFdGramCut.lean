-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFdGramCut
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T07:09:05.679494+00:00
-- url     : https://prove2.me/theorems/b7b6dc1b-c024-5899-a8ca-e3ced4486bd0
-- title:
--   PFd Gram Cut
-- statement:
--   Definitions and structural lemmas for PFd Gram Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PFdGramCut.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PFramesCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
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
namespace PI.UnitaryGroupMassFormula.DLm.Gram
section
variable {k r : ℕ}
def Rel (z z' : Fin (2 * r + k + 1) → ℂ) (a b : B.Mat k r) : Prop :=
  ∃ n ∈ C2.N0set k r z, ∃ m ∈ C2.N0set k r z, ∃ n' ∈ C2.N0set k r z', ∃ m' ∈ C2.N0set k r z',
  ∃ c ∈ UWset k r z, ∃ c' ∈ UWset k r z',
    b = c * (n⁻¹ * a * n') * c' ∧ c * (m⁻¹ * a * m') * c' = a
def nrm (T : B.Mat k r → B.Mat k r × B.Mat k r) (g : B.Mat k r) : B.Mat k r := (T g).1 * g * (T g).2
end
def GramSlice : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
  ∃ T : B.Mat k r → B.Mat k r × B.Mat k r,
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → (T g).1 ∈ UWset k r z ∧ (T g).2 ∈ UWset k r z') ∧
    (∀ g ∈ B.GV k r, 0 < Gf k r z z' g → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, T (n⁻¹ * g * n') = T g) ∧
    (∀ g₁ ∈ B.GV k r, ∀ g₂ ∈ B.GV k r, 0 < Gf k r z z' g₁ → Zhat k r z z' g₁ = Zhat k r z z' g₂ →
      Rel z z' (nrm T g₁) (nrm T g₂)) ∧
    (∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ → ∃ (O : Set (B.Mat k r)) (Tl : B.Mat k r → B.Mat k r × B.Mat k r),
      IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Tl O ∧
      ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
        (Tl g).1 ∈ UWset k r z ∧ (Tl g).2 ∈ UWset k r z' ∧ Rel z z' (nrm Tl g) (nrm T g))
def SmoothRep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq),
    (∀ h₀ ∈ UWset k r D.z, ∃ (O : Set (B.Mat k r)) (P : B.Mat k r → (Wp →L[ℂ] Wp)),
      IsOpen O ∧ h₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P O ∧ ∀ h ∈ O, h ∈ UWset k r D.z → P h = D.π h) ∧
    (∀ h₀ ∈ UWset k r D.z', ∃ (O : Set (B.Mat k r)) (P : B.Mat k r → (Wq →L[ℂ] Wq)),
      IsOpen O ∧ h₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P O ∧ ∀ h ∈ O, h ∈ UWset k r D.z' → P h = D.π' h)
def FibEquivU : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), ∀ c ∈ UWset k r D.z, ∀ c' ∈ UWset k r D.z',
      fibInt D μ0 μ0' F (c * g * c') = (D.π c).comp ((fibInt D μ0 μ0' F g).comp (D.π' c'))
def FiberIntegralUnipotentInvariant : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (μ0 μ0' : Measure (Mt k r)), B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r), ∀ n ∈ C2.N0set k r D.z, ∀ n' ∈ C2.N0set k r D.z',
      fibInt D μ0 μ0' F (n⁻¹ * g * n') = fibInt D μ0 μ0' F g
section
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
def repE (A : W →L[ℂ] W) : W ≃L[ℂ] W := by
  classical
  exact if hA : ∀ v, ‖A v‖ = ‖v‖ then
    (LinearEquiv.ofInjectiveEndo (A : W →ₗ[ℂ] W) (fun v w h => by
      have h1 := hA (v - w)
      have h2 : A (v - w) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr h
      rw [h2, norm_zero] at h1
      exact sub_eq_zero.mp (norm_eq_zero.mp h1.symm))).toContinuousLinearEquiv
  else ContinuousLinearEquiv.refl ℂ W
end
section
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
end
end PI.UnitaryGroupMassFormula.DLm.Gram


