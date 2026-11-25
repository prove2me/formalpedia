-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JacobianCommutation_Development
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:42.545248+00:00
-- url     : https://prove2.me/theorems/fc6fc470-2b4d-4038-bb80-343fb4206f97
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JacobianCommutation/Development.lean

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
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
namespace PI.UnitaryGroupMassFormula.JCC
def thr (c₃ : ℝ) (k r o : ℕ) : ℝ :=
  c₃ * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + r * ((2 * r + k + 1 : ℕ) : ℝ) + 1)
def StepEquiv : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (UU : Set (B.Mat k r)),
    EquivOn D UU (B.JF D F)
def StepDom (c₃ : ℝ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (o : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    thr c₃ k r o ≤ A → B.InCC A (o + 1) F →
    (∀ v : List (B.Mat k r), (∀ X ∈ v, B.unitLie k r X) → v.length ≤ o → ∀ g ∈ bigPos D,
      AEStronglyMeasurable (fun p => B.rho D p (B.Rw (v.map (JF.AdR p)) F) g) D.μSS) ∧
    ∀ K : Set (B.Mat k r), IsCompact K → K ⊆ bigPos D →
      ∃ b : B.SS k r → ℝ, Integrable b D.μSS ∧
        ∀ v : List (B.Mat k r), (∀ X ∈ v, B.unitLie k r X) → v.length ≤ o → ∀ g ∈ K,
          ∀ᵐ p ∂D.μSS, ‖B.rho D p (B.Rw (v.map (JF.AdR p)) F) g‖ ≤ b p
def StepWords (c₃ : ℝ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (o : ℕ) (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)),
    thr c₃ k r o ≤ A → B.InCC A (o + 1) F →
    B.CkOn (o : ℕ∞) (bigPos D) (B.JF D F) ∧
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → w.length ≤ o → ∀ g ∈ bigPos D,
      Integrable (fun p => B.xiTau D (1, 1) p • B.Rw w (B.rho D p F) g) D.μSS ∧
      B.Rw w (B.JF D F) g = ∫ p, B.xiTau D (1, 1) p • B.Rw w (B.rho D p F) g ∂D.μSS
def StepWordsOfDom (c₃ : ℝ) : Prop := StepDom c₃ → JF.RwRho → StepWords c₃
end PI.UnitaryGroupMassFormula.JCC


