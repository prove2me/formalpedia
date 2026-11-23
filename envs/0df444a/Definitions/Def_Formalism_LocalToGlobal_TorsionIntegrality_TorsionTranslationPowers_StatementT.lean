-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:16:20.471898+00:00
-- url     : https://prove2.me/theorems/5a209e57-3fe5-49ed-93e9-ead49da720d7
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/TorsionTranslationPowers/StatementT.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
namespace Formalism.L2.Th1.E
def XTShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P : W.toAffine.Point, P ≠ 0 → ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 →
      IntS (xT W P) ∧ coeff 0 (xT W P) = px W P ∧ coeff 1 (xT W P) = psi2 W P ∧
      (psi2 W P = 0 → coeff 2 (xT W P) = kapP W P)
def FacShape : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W → ∀ P Q : W.toAffine.Point, P ≠ 0 → Q ≠ 0 →
      ‖px W P‖ ≤ 1 → ‖py W P‖ ≤ 1 → ‖px W Q‖ ≤ 1 → ‖py W Q‖ ≤ 1 →
      (P + Q ≠ 0 → ‖px W (P + Q)‖ ≤ 1) → (P - Q ≠ 0 → ‖px W (P - Q)‖ ≤ 1) →
      (P + Q ≠ 0 → P - Q ≠ 0 → UnitAt 0 (C (px W Q) - xT W P)) ∧
      ((P + Q = 0 ∨ P - Q = 0) → Q + Q ≠ 0 → UnitAt 1 (C (px W Q) - xT W P)) ∧
      (P - Q = 0 → Q + Q = 0 → UnitAt 2 (C (px W Q) - xT W P))
def FacShapeZero : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K),
    IntCurve W → ∀ xQ : K, ‖xQ‖ ≤ 1 → UnitAt 0 (C xQ * X ^ 2 - Formalism.L2.Th1.A.xS W)
def TransPower : Prop :=
  ∀ (K : Type) [NormedField K] [DecidableEq K] (W : WeierstrassCurve K)
    (T : Type) [AddCommGroup T] (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧), IsTransSys W π G →
    ∀ ε : K, G 0 = C ε * X →
    ∀ (t : T) (k : ℕ), (∀ j : ℕ, 1 ≤ j → j ≤ k → π (j • t) ≠ 0) →
      C (ε ^ k) * G ((k + 1) • t) * X ^ k = G t ^ (k + 1) *
        ∏ j ∈ Finset.range k,
          (C (constantCoeff (G t) ^ 2) * (C (px W (π t)) - xT W (π ((j + 1) • t)))) ^ (k - j)
def TransUnit : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W →
    ∀ (T : Type) [AddCommGroup T] (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧), IntPts W π →
    IsTransSys W π G →
    ∀ (t : T) (N : ℕ), ‖(N : K)‖ = 1 → N • π t = 0 → π t ≠ 0 →
      ‖constantCoeff (G t)‖ = 1 ∧ OneUnit (C (constantCoeff (G t))⁻¹ * G t)
def TransGauss : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W →
    ∀ (T : Type) [AddCommGroup T] (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧), IntPts W π →
    IsTransSys W π G →
    ∀ (t : T) (N : ℕ), ‖(N : K)‖ = 1 → N • π t = 0 → GaussOne (G t)
def ParSum : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (M : A → ℝ),
    (∀ P Q : A, Q ≠ 0 → M (P + Q) + M (P - Q) - 2 * M P = 2 * M Q) → ∀ Q : A, Q ≠ 0 → M Q = 0
def ParSumTwo : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (M₀ m : A → ℝ),
    (∀ P Q : A, Q ≠ 0 → M₀ (P + Q) + M₀ (P - Q) - 2 * M₀ P = 2 * m Q) →
    (∀ Q : A, Q ≠ 0 → m Q = 0) ∧ ∀ P : A, M₀ P = M₀ 0
def TransPar : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (W : WeierstrassCurve K),
    IntCurve W →
    ∀ (T : Type) [AddCommGroup T] (π : T →+ W.toAffine.Point) (G : T → K⟦X⟧), IntPts W π →
    IsTransSys W π G →
    (∀ t, π t ≠ 0 → OneUnit (C (constantCoeff (G t))⁻¹ * G t)) →
    ∀ M : T → ℝ, (∀ t, M t = if π t = 0 then 0 else Real.log ‖constantCoeff (G t)‖) →
    ∀ P Q : T, π Q ≠ 0 → M (P + Q) + M (P - Q) - 2 * M P = 2 * M Q
end Formalism.L2.Th1.E


