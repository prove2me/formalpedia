-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
-- name    : CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:02:12.671707+00:00
-- url     : https://prove2.me/theorems/0a93b2e8-6441-5b37-8d8c-4e5ce0033e65
-- title:
--   Zuck Dual TOf Zuck Dual
-- statement:
--   Definitions and structural lemmas for Zuck Dual TOf Zuck Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/ZuckermanDuality/ZuckDualTOfZuckDual.lean

import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_CoreDefs
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix
open scoped InnerProductSpace
def IsCoef (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (φ : B.Mat k r → ℂ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : B.Mat k r → (H →L[ℂ] H)) (v w : H),
    IsHCParam μ ∧ IsDSHpk k r ε μ σ ∧ IsKFinHpk (k := k) (r := r) σ v ∧ IsKFinHpk (k := k) (r := r) σ w ∧
    ∀ g ∈ B.GV k r, φ g = ⟪w, σ g v⟫_ℂ
def Box {n : ℕ} (lam : Fin n → ℝ) (e : ℝ) : Set (Fin n → ℝ) := {μ | ∀ s, |μ s - lam s| ≤ e}
def SpanBox (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (e : ℝ) :
    Submodule ℂ (B.Mat k r → ℂ) :=
  Submodule.span ℂ {φ | ∃ μ ∈ Box lam e, IsCoef k r ε μ φ}
def IsLetter (k r : ℕ) (q : B.Mat k r → ℂ) : Prop :=
  q = 1 ∨ ∃ x y : Fin (2 * r + k + 1) → ℂ,
    (∀ g ∈ B.GV k r, q g = star y ⬝ᵥ (g *ᵥ x)) ∨ (∀ g ∈ B.GV k r, q g = star y ⬝ᵥ (g⁻¹ *ᵥ x))
def Letters (k r : ℕ) : Submodule ℂ (B.Mat k r → ℂ) := Submodule.span ℂ {q | IsLetter k r q}
def ZuckT (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → t n ε + 1 < h →
      Nonempty (PI.ZuckTensor.TensorDS n ε μ H σ)
def ZuckDualT (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → t n ε + 1 < h →
      Nonempty (PI.ZuckTensor.TensorDSd n ε μ H σ)
def KDecay (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (A h : ℝ) : Prop :=
  ∀ (μ : Fin (2 * r + k + 1) → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : B.Mat k r → (H →L[ℂ] H)), IsHCParam μ → IsDSHpk k r ε μ σ → PI.ZuckTensor.GapAtLeast ε μ h →
    ∀ v w : H, IsKFinHpk (k := k) (r := r) σ v → IsKFinHpk (k := k) (r := r) σ w →
      ∃ C : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖⟪w, σ g v⟫_ℂ‖ ≤ C
def GfPoly : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (p : ℕ),
    (fun g : B.Mat k r => ((Formalism.QuantumDeterminants.Gf k r z z' g ^ p : ℝ) : ℂ)) ∈ Letters k r ^ ((2 * r + 2) * p)
def LetterStep : Prop :=
  ∀ t : ∀ n : ℕ, (Fin n → Bool) → ℝ, ZuckT t → ZuckDualT t →
    ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (q φ : B.Mat k r → ℂ),
      IsLetter k r q → IsCoef k r ε μ φ → PI.ZuckTensor.GapAtLeast ε μ h → t _ ε + 1 < h →
      q * φ ∈ SpanBox k r ε μ 1
def CoefSmooth : Prop :=
  PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (φ : B.Mat k r → ℂ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E),
    IsCoef k r ε μ φ → B.CkOn ⊤ (B.GV k r) (fun g => φ g • T)
def CoefCC : Prop :=
  PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (A h : ℝ), KDecay k r ε A h →
    ∀ (μ : Fin (2 * r + k + 1) → ℝ) (φ : B.Mat k r → ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (T : E)
      (m : ℕ), IsCoef k r ε μ φ → PI.ZuckTensor.GapAtLeast ε μ h → B.InCC A m (fun g => φ g • T)
def DecayOfInf : Prop :=
  PI.KFinSmooth → ThreeDimData.DecInf → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (h : ℝ), ThreeDimData.GapOK k r h →
    B.AB k r ≤ ThreeDimData.aOf r h - 1 ∧ KDecay k r ε (ThreeDimData.aOf r h - 1) h
def CVBridge : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (Y : ℂ) (F : B.Mat k r → E),
    Q.CV k r Y F = PI.CapelliEig.capC (k := k) (r := r) Y F
def CoefEig : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (φ : B.Mat k r → ℂ)
    (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (T : Wq →L[ℂ] Wp),
    IsCoef k r ε μ φ → ∀ Y : ℂ, ∀ g ∈ B.GV k r,
      Q.CV k r Y (fun x => φ x • T) g = Formalism.QuantumDeterminants.capP (fun s => (μ s : ℂ)) Y • (φ g • T)
def Inequiv : Prop :=
  CoefEig → ∀ (k r : ℕ) (ε ε' : Fin (2 * r + k + 1) → Bool) (μ μ' : Fin (2 * r + k + 1) → ℝ)
    (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (σ : B.Mat k r → (H →L[ℂ] H)) (σ' : B.Mat k r → (H' →L[ℂ] H')),
    IsHCParam μ → IsHCParam μ' → IsDSHpk k r ε μ σ → IsDSHpk k r ε' μ' σ' → μ ≠ μ' →
    ¬ ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ UH (Hpk k r), ∀ v, U (σ g v) = σ' g (U v)
def PhZero : Prop :=
  CoefEig → ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (μ μ' : Fin (2 * r + k + 1) → ℝ) (φ φ' : B.Mat k r → ℂ) (T T' : Wq →L[ℂ] Wp),
    IsCoef k r ε μ φ → IsCoef k r ε μ' φ' → μ ≠ μ' →
    ∀ p, D.inSS p → B.Ph D (fun g => φ g • T) (fun g => φ' g • T') p = 0
def BetaInfZero : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    (F F' : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → B.Ph D F F' p = 0) → B.betaInf D F F' = 0
end CompanionTheory.LimBd.Main


