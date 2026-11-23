-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_UnitCancel
-- name    : Formalism_EllipticTorsion_UnitCancel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:54:49.06911+00:00
-- url     : https://prove2.me/theorems/9ea31f53-20e8-44bb-8413-dc90deeac2f2
-- title:
--   Unit Cancel
-- statement:
--   Definitions and structural lemmas for Unit Cancel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/UnitCancel.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
open Formalism.G
def LogWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 → 2 ≤ q →
    ∀ (F : FormalGroup (unitBall K)) (e l : PowerSeries K),
      IsHom (F.map (unitBall K).subtype) (F.map (unitBall K).subtype) e → IntegralPS e →
      coeff 1 e = p → (∀ n, 2 ≤ n → n < q → coeff n e = 0) →
      IsLog (F.map (unitBall K).subtype) l →
      ∀ n : ℕ, 1 ≤ n → ‖coeff n l‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((q : ℝ) - 1))
def ExpWeight : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K] (p q : ℕ), p.Prime →
    0 < ‖(p : K)‖ → ‖(p : K)‖ < 1 → 2 ≤ q →
    ∀ (F : FormalGroup (unitBall K)) (e l E : PowerSeries K),
      IsHom (F.map (unitBall K).subtype) (F.map (unitBall K).subtype) e → IntegralPS e →
      coeff 1 e = p → (∀ n, 2 ≤ n → n < q → coeff n e = 0) →
      IsLog (F.map (unitBall K).subtype) l →
      constantCoeff E = 0 → E.subst l = X → l.subst E = X →
      ∀ n : ℕ, 1 ≤ n → ‖coeff n E‖ ≤ ‖(p : K)‖ ^ (-((n : ℝ) - 1) / ((q : ℝ) - 1))
def UnitCancel : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [NormedAlgebra ℚ_[p] K] (σ : Type) (G : MvPowerSeries σ K) (b : ℤ_[p]), IsUnit b →
      InN (algebraMap ℚ_[p] K (b : ℚ_[p]) • G) → InN G
end Formalism.ELL


