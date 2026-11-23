-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_CoeffRing
-- name    : Formalism_EllipticTorsion_CoeffRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:47.57261+00:00
-- url     : https://prove2.me/theorems/c3cd79d8-7979-4cba-98f6-175ee546d9b2
-- title:
--   Coeff Ring
-- statement:
--   Definitions and structural lemmas for Coeff Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/CoeffRing.lean

import Mathlib
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
def wU {K : Type u} [Field K] (w : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => coeff (n + 3) w
def invSer {K : Type u} [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) : PowerSeries K :=
  X * (-1 + C W.a₁ * X + C W.a₃ * w)⁻¹
abbrev coeffRing {K : Type u} [Field K] (W : WeierstrassCurve K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)
def CubeTwo : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let a : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0
    let b : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1
    ∃ c : MvPowerSeries (Fin 2) K, (∀ d, MvPowerSeries.coeff d c ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff c = -1 ∧
      b ^ 2 * ((wU w).subst a)⁻¹ - a ^ 2 * ((wU w).subst b)⁻¹
        = c * F * MvPowerSeries.subst ![a, (invSer W w).subst b] F
def CubeThree : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K) (w : PowerSeries K) (F : MvPowerSeries (Fin 2) K),
    WFixed W w → MvPowerSeries.constantCoeff F = 0 →
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F →
    let t : Fin 3 → MvPowerSeries (Fin 3) K := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) K := fun i =>
      ![t i ^ 3, t i * ((wU w).subst (t i))⁻¹, -((wU w).subst (t i))⁻¹]
    ∃ e : MvPowerSeries (Fin 3) K, (∀ d, MvPowerSeries.coeff d e ∈ coeffRing W) ∧
      MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst ![MvPowerSeries.subst ![t 0, t 1] F, t 2] F
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)
end Formalism.ELL


