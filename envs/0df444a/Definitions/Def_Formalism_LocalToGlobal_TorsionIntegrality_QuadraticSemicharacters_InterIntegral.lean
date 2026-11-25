-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_InterIntegral
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_InterIntegral
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:10:44.613534+00:00
-- url     : https://prove2.me/theorems/f78a8eec-445c-42f6-b227-327fbaf65e82
-- title:
--   Inter Integral
-- statement:
--   Definitions and structural lemmas for Inter Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/InterIntegral.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
def IntAt (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (lg ph : PowerSeries ℂ_[l]) {n : Type} [Fintype n] [DecidableEq n]
    (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (B' : Matrix n n ℂ_[l]) (θ : (n → ℂ) → ℂ) : Prop :=
  ∀ (t : n → ℂ) (N : ℕ), 0 < N → ¬ l ∣ N → (N : ℂ) • t ∈ Λ →
    Integral (mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[l]) *
      thetaU (ι : ℂ →+* ℂ_[l]) lg B' (opU (matH h) t θ))
def InterIntegral : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (lg ph : PowerSeries ℂ_[l]), PowerSeries.constantCoeff lg = 0 →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ), IsHerm (matH h) → ∀ (Λ₁ Λ₂ : AddSubgroup (n → ℂ)) (α : (n → ℂ) → ℂ),
    IsSemiChar (matH h) Λ₂ α → Λ₂ ≤ dualLat (matH h) Λ₂ → relIdx Λ₁ Λ₂ ≠ 0 → ¬ l ∣ relIdx Λ₁ Λ₂ →
    ∀ (B' : Matrix n n ℂ_[l]), ∀ θ ∈ Th (matH h) α Λ₁, IntAt l ι lg ph h Λ₁ B' θ →
      IntAt l ι lg ph h Λ₂ B' (inter (matH h) α Λ₁ Λ₂ θ)
def InK (d : ℕ) (z : ℂ) : Prop := ∃ p q : ℚ, z = (p : ℂ) + (q : ℂ) * (Complex.I * ((Real.sqrt d : ℝ) : ℂ))
def IsometryFour : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] (h₀ : Matrix n n ℂ),
    (∀ i j, InK d (h₀ i j)) → h₀.IsHermitian → IsPosDef (matH h₀) →
    ∃ g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ),
      (∀ w w', InK d (g (Pi.single w' 1) w)) ∧ (∀ w w', InK d (g.symm (Pi.single w' 1) w)) ∧
      IsIsom (matH (blk4 ((((Formalism.L2.Th1.F.area L : ℝ) : ℂ))⁻¹ • h₀))) (stdH L (Fin 4 × n))
        (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
end Formalism.L2.Th1.H


