-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_ConverseStep
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:28:07.530798+00:00
-- url     : https://prove2.me/theorems/e8e7b40b-db3d-4b12-804d-a6dca38e4266
-- title:
--   Converse Step
-- statement:
--   Definitions and structural lemmas for Converse Step, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerPairs/ConverseStep.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
def Fm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun i j => gramVec k r z z' γ j i
def Wm {r : ℕ} (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks u 0 0 u'
def Km (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (2 * r + k + 1)) ℂ :=
  (gramM k r z z' γ)⁻¹ * (Fm k r z z' γ)ᴴ * Hpk k r
def rhoOf (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : B.Mat k r :=
  1 + Fm k r z z' γ * (Wm u u' - 1) * Km k r z z' γ
def PairSet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Set (Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) :=
  {p | p.1 ∈ UTset (r + 1) ∧ p.2 ∈ UTset (r + 1) ∧ p.1ᴴ * Zhat k r z z' γ * p.2 = Zhat k r z z' γ}
def pairMap (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (ρ : B.Mat k r) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ × Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  (uMap k r z ρ, uMap k r z' (γ⁻¹ * ρ * γ))
def GramInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    IsUnit (gramM k r z z' γ).det
def MapsStep : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    ∀ ρ ∈ Rst k r z z' γ, pairMap k r z z' γ ρ ∈ PairSet k r z z' γ
def PairFormula : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    ∀ ρ ∈ Rst k r z z' γ, ρ = rhoOf k r z z' γ (pairMap k r z z' γ ρ).1 (pairMap k r z z' γ ρ).2
def ConverseStep : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    ∀ p ∈ PairSet k r z z' γ, rhoOf k r z z' γ p.1 p.2 ∈ Rst k r z z' γ ∧
      pairMap k r z z' γ (rhoOf k r z z' γ p.1 p.2) = p
def CompDet : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), Std k r z z' → PosPt k r z z' γ →
    ∀ p ∈ PairSet k r z z' γ, ∀ q ∈ PairSet k r z z' γ, (p.1 = q.1 → p = q) ∧ (p.2 = q.2 → p = q)
end PI.StabPairsW


