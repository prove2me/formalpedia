-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStar
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:31:35.364331+00:00
-- url     : https://prove2.me/theorems/e6b8552d-677f-4cbc-8271-4ed36001a3ce
-- title:
--   Core Star
-- statement:
--   Definitions and structural lemmas for Core Star, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCorrectionU1/CoreStar.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
namespace PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Classical in

def costP (k j ρ : ℕ) (X : B.Mat k (j + ρ)) : ℕ := if inLieP k j ρ X then 0 else j
def WB {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (cost : B.Mat k r → ℕ)
    (φ : B.Mat k r → E) (n : ℕ) (C e : ℝ) : Prop :=
  ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
    u.length + v.length ≤ n → ∀ g ∈ B.GV k r,
      ‖B.dLR u v φ g‖ ≤ C * B.gN g ^ (e + ((((u ++ v).map cost).sum : ℕ) : ℝ))
def DjCurve : Prop :=
  ∀ (k j ρ : ℕ) (Y : B.Mat k (j + ρ)), inLieP k j ρ Y → ∃ c₁ c₂ : ℂ,
    ‖c₁‖ ≤ (j : ℝ) * mx Y ∧ ‖c₂‖ ≤ (j : ℝ) * mx Y ∧
    ∀ (g : B.Mat k (j + ρ)) (t : ℝ),
      DjU k j ρ (g * NormedSpace.exp ((t : ℂ) • Y)) = Complex.exp ((t : ℂ) * c₁) * DjU k j ρ g ∧
      DjU k j ρ (NormedSpace.exp (-((t : ℂ) • Y)) * g) = Complex.exp ((t : ℂ) * c₂) * DjU k j ρ g
def PolyB : Prop :=
  ∀ (k r κ : ℕ) (P : B.Mat k r → ℂ), IsPolyDeg κ P →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P ∧ ∀ n : ℕ, ∃ C : ℝ, WB (fun _ => 0) P n C κ
def DjPoly : Prop := ∀ k j ρ : ℕ, IsPolyDeg j (DjU k j ρ)
def GfPoly : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), IsPolyDeg (2 * (r + 1)) (fun g => ((Gf k r z z' g : ℝ) : ℂ))
def CompC : Prop :=
  ∀ (k r : ℕ) (ψ : B.Mat k r → ℂ) (χ : ℂ → ℂ) (cost : B.Mat k r → ℕ) (n : ℕ) (C₀ : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
    (∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ n → u ++ v ≠ [] → ∀ g ∈ B.GV k r, ψ g ∈ tsupport χ →
        ‖B.dLR u v ψ g‖ ≤ C₀ * B.gN g ^ ((((u ++ v).map cost).sum : ℕ) : ℝ)) →
    ∃ C : ℝ, WB cost (fun g => χ (ψ g)) n C 0
def CompR : Prop :=
  ∀ (k r : ℕ) (ψ : B.Mat k r → ℝ) (h : ℝ → ℝ) (cost : B.Mat k r → ℕ) (n : ℕ) (C₀ : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
    (∀ q : ℕ, ∃ c : ℝ, ∀ x, ‖iteratedDeriv q h x‖ ≤ c) →
    (∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ v, B.unitLie k r X) →
      u.length + v.length ≤ n → u ++ v ≠ [] → ∀ g ∈ B.GV k r,
        ‖B.dLR u v (fun g => ((ψ g : ℝ) : ℂ)) g‖ ≤ C₀ * B.gN g ^ ((((u ++ v).map cost).sum : ℕ) : ℝ)) →
    ∃ C : ℝ, WB cost (fun g => ((h (ψ g) : ℝ) : ℂ)) n C 0
def WBmul : Prop :=
  ∀ (k r : ℕ) (φ₁ φ₂ : B.Mat k r → ℂ) (c₁ c₂ : B.Mat k r → ℕ) (n : ℕ) (C₁ C₂ e₁ e₂ : ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ₁ → ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ₂ →
    WB c₁ φ₁ n C₁ e₁ → WB c₂ φ₂ n C₂ e₂ → ∃ C : ℝ, WB (c₁ + c₂) (fun g => φ₁ g * φ₂ g) n C (e₁ + e₂)
def DjWB : Prop :=
  ∀ (k j ρ : ℕ) (χ : ℂ → ℂ) (n : ℕ), IsCutC χ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => χ (DjU k j ρ g)) ∧
      ∃ C : ℝ, WB (costP k j ρ) (fun g => χ (DjU k j ρ g)) n C 0
def GfWB : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (χε : ℝ → ℝ) (ε : ℝ) (n : ℕ), IsCutG ε χε →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : B.Mat k r => ((χε (Gf k r z z' g) : ℝ) : ℂ)) ∧
      ∃ C : ℝ, WB (fun _ => 2 * (r + 1)) (fun g : B.Mat k r => ((χε (Gf k r z z' g) : ℝ) : ℂ)) n C 0
def CoreStar : Prop :=
  ∀ (k j ρ : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ d : ℕ) (Θ : B.DiffOp k (j + ρ) Wp Wq) (χ : ℂ → ℂ)
    (φ : B.Mat k (j + ρ) → ℂ),
    InDD k j ρ o κ Θ → IsCutC χ → ∀ (Q mm₀ : ℕ) (A₀ : ℝ), Q + o ≤ mm₀ →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → (∀ g, DjU k j ρ g ∉ tsupport χ → φ g = 0) →
    (∃ Cφ : ℝ, WB (fun X => costP k j ρ X + d) φ (Q + o) Cφ 0) →
    ∃ C : ℝ, ∀ (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) (c : ℝ), B.CCle A₀ mm₀ f c →
      Star k j ρ (B.opApply Θ (fun g => φ g • f g))
        (A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) Q (C * c)
        ((fun w : ℂ => ‖w‖) '' tsupport χ)
end PI.UnitaryCorollaryDerivatives


