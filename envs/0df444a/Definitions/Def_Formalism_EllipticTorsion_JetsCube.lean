-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_JetsCube
-- name    : Formalism_EllipticTorsion_JetsCube
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:04.836498+00:00
-- url     : https://prove2.me/theorems/a91037ff-5755-445d-bf10-4e006d3d5865
-- title:
--   Jets Cube
-- statement:
--   Definitions and structural lemmas for Jets Cube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/JetsCube.lean

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
abbrev FK (F : FormalGroup (unitBall K)) : FormalGroup K := F.map (unitBall K).subtype
def omegaF (F : FormalGroup (unitBall K)) : PowerSeries K :=
  MvPowerSeries.subst ![PowerSeries.X, (0 : PowerSeries K)]
    (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries)
def invD (F : FormalGroup (unitBall K)) (φ : PowerSeries K) : PowerSeries K :=
  omegaF F * PowerSeries.derivative K φ
abbrev Y3 (i : Fin 3) : MvPowerSeries (Fin 3) K := MvPowerSeries.X i
def F2 (F : FormalGroup (unitBall K)) (i j : Fin 3) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![Y3 i, Y3 j] (FK F).toPowerSeries
def F3 (F : FormalGroup (unitBall K)) : MvPowerSeries (Fin 3) K :=
  MvPowerSeries.subst ![F2 F 0 1, Y3 2] (FK F).toPowerSeries
def triDiff (F : FormalGroup (unitBall K)) (φ : PowerSeries K) : MvPowerSeries (Fin 3) K :=
  φ.subst (F3 F) - φ.subst (F2 F 0 1) - φ.subst (F2 F 0 2) - φ.subst (F2 F 1 2)
    + φ.subst (Y3 0) + φ.subst (Y3 1) + φ.subst (Y3 2)
    - MvPowerSeries.C (constantCoeff φ)
def betaF (F : FormalGroup (unitBall K)) (φ : PowerSeries K) (x y : MvPowerSeries (Fin 2) K) :
    MvPowerSeries (Fin 2) K :=
  φ.subst (MvPowerSeries.subst ![x, y] (FK F).toPowerSeries) - φ.subst x - φ.subst y
def JetsCube : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (F : FormalGroup (unitBall K)) (φ : PowerSeries K),
    InN (triDiff F φ) → ∀ i : ℕ, 3 ≤ i → ‖constantCoeff ((invD F)^[i] φ)‖ ≤ 1
def JetsTwo : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (F : FormalGroup (unitBall K)) (φ a a' : PowerSeries K),
    IsHom (FK F) (FK F) a → IsHom (FK F) (FK F) a' →
    InN (betaF F φ (a.subst (MvPowerSeries.X (0 : Fin 2))) (MvPowerSeries.X 1)
        - betaF F φ (MvPowerSeries.X 0) (a'.subst (MvPowerSeries.X (1 : Fin 2)))) →
      ‖(coeff 1 a - coeff 1 a') * constantCoeff ((invD F)^[2] φ)‖ ≤ 1
def JetsOne : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (F : FormalGroup (unitBall K)) (φ a : PowerSeries K) (n : K),
    IsHom (FK F) (FK F) a →
    InN (σ := Unit) (φ.subst a - n • φ) →
      ‖(coeff 1 a - n) * constantCoeff (invD F φ)‖ ≤ 1
end Formalism.ELL


