-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopSlice
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopSlice
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:15.622227+00:00
-- url     : https://prove2.me/theorems/59be62c3-c835-4642-8f10-f51598779d56
-- title:
--   PTop Slice
-- statement:
--   Definitions and structural lemmas for PTop Slice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DensityLemma/PTopSlice.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PTopCut
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
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
def fibInt (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : Wq →L[ℂ] Wp :=
  ∫ x : B.SS k r, B.rho D x F g ∂((D.μW.prod μ0).prod (D.μW'.prod μ0'))
def FibreRel (D : B.RealPlaceData k r Wp Wq) (μ0 μ0' : Measure (Mt k r)) (F : B.Mat k r → (Wq →L[ℂ] Wp)) {p m' : ℕ}
    (hps : p + (m' + 1 + 1) = r + 1) (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ g ∈ B.GV k r, 0 < Gf k r D.z D.z' g → ∃ (L₁ : Wp ≃L[ℂ] Wp) (L₂ : Wq ≃L[ℂ] Wq),
    ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      Φ0 (castM hps.symm (Zhat k r D.z D.z' (n⁻¹ * g * n'))) =
        (L₁ : Wp →L[ℂ] Wp).comp ((fibInt D μ0 μ0' F (n⁻¹ * g * n')).comp (L₂ : Wq →L[ℂ] Wq))
end
def TopDensEx : Prop :=
  ∀ C₂ : ℕ, ∃ C CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    ∃ (μ0 μ0' : Measure (Mt k r)) (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) (e : ℕ → ℝ) (K : ℝ),
      B.IsHaarOn (C2.N0set k r D.z) μ0 ∧ B.IsHaarOn (C2.N0set k r D.z') μ0' ∧
      U.DecayAll (C₂ * (m' + 2) ^ 2) e K Φ0 ∧
      (∀ j ≤ C₂ * (m' + 2) ^ 2,
        A - (C : ℝ) * (((2 * r + k + 2 : ℕ) : ℝ) ^ 2 + (r : ℝ) ^ 3 + r * j) ≤ e j) ∧
      FibreRel D μ0 μ0' F' hps Φ0
def TopUnfold : Prop :=
  ∃ CV₀ : ℕ, ∀ CV, CV₀ ≤ CV →
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (p m' : ℕ) (hps : p + (m' + 1 + 1) = r + 1)
    (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (μ0 μ0' : Measure (Mt k r))
    (Φ0 : G.Mat (p + (m' + 1 + 1)) → (Wq →L[ℂ] Wp)) (q : ℕ) (e : ℕ → ℝ) (K : ℝ),
    1 ≤ r → 0 < ε → (r : ℝ) * AV CV r (2 * r + k + 1) ≤ A → mmV CV r ≤ mm → B.InCC A mm F' →
    (∀ g ∈ B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) → (∀ a, d a ≠ 0) →
    B.IsHaarOn (C2.N0set k r D.z) μ0 → B.IsHaarOn (C2.N0set k r D.z') μ0' →
    U.DecayAll q e K Φ0 → (∀ i ≤ q, 2 * ((r : ℝ) + 1) ^ 2 < e i / (5 * ((r : ℝ) + 1))) →
    FibreRel D μ0 μ0' F' hps Φ0 →
    ∃ β : ℂ, β ≠ 0 ∧
      (∀ t c : ℂ, t ≠ 0 → c ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (G.ptBlock (m' + 1) t c)) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmBlock β (m' + 1) (U.PhiTop β σ d Φ0) t c = 0 ↔ orbI D g θ F' = 0)) ∧
      (∀ z : ℂ, z ≠ 0 → ∀ (g : B.Mat k r) (μR : Measure (Mt k r)) (θ : B.SS k r → ℝ),
        B.IsHaarOn (Rset g) μR → IsRelevant D g → 0 < Gf k r D.z D.z' g →
        ZOrb D g (topPt hps σ d (z • G.wMat (m' + 1 + 1))) → admitted D g μR θ →
        Integrable (fun x => θ x • (B.xiTau D (1, 1) x • B.rho D x F' g)) D.μSS →
        (G.OmLong β (m' + 1) (U.PhiTop β σ d Φ0) z = 0 ↔ orbI D g θ F' = 0))
end PI.UnitaryGroupMassFormula.DLm


