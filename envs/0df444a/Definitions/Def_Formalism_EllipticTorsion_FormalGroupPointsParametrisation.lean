-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
-- name    : Formalism_EllipticTorsion_FormalGroupPointsParametrisation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:11.840211+00:00
-- url     : https://prove2.me/theorems/64d4a15c-4a29-4cc9-93a1-d887d419cd73
-- title:
--   Formal Group Points Parametrisation
-- statement:
--   Definitions and structural lemmas for Formal Group Points Parametrisation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/FormalGroupPointsParametrisation.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
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
def evalPS {K : Type u} [NormedField K] (f : PowerSeries K) (t : K) : K :=
  ∑' n : ℕ, coeff n f * t ^ n
def evalMv2 {K : Type u} [NormedField K] (F : MvPowerSeries (Fin 2) K) (a b : K) : K :=
  ∑' d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F * a ^ (d 0) * b ^ (d 1)
def uOf {K : Type u} [Field K] {W : WeierstrassCurve K} : W.toAffine.Point → K
  | .zero => 0
  | .some x y _ => -x / y
def FormalGroupPointsParametrisation : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K), IntegralModel W → WFixed W w →
    (∀ t : K, 0 < ‖t‖ → ‖t‖ < 1 →
      evalPS w t ≠ 0 ∧ W.toAffine.Nonsingular (t / evalPS w t) (-1 / evalPS w t) ∧
        1 < ‖t / evalPS w t‖ ∧ -(t / evalPS w t) / (-1 / evalPS w t) = t) ∧
    (∀ (x y : K), W.toAffine.Nonsingular x y → 1 < ‖x‖ →
      0 < ‖-x / y‖ ∧ ‖-x / y‖ < 1 ∧
        x = (-x / y) / evalPS w (-x / y) ∧ y = -1 / evalPS w (-x / y))
open Classical in

def FormalGroupPointsHomomorphism : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (W : WeierstrassCurve K) (w : PowerSeries K) (F₂ : MvPowerSeries (Fin 2) K),
    IntegralModel W → WFixed W w → IntegralMv F₂ → MvPowerSeries.constantCoeff F₂ = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F₂ →
    ∀ P Q : W.toAffine.Point, InFormalGroupPoints P → InFormalGroupPoints Q → uOf (P + Q) = evalMv2 F₂ (uOf P) (uOf Q)
end Formalism.ELL


