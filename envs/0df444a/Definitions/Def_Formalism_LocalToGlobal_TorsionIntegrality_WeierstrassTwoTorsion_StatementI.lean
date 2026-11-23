-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:57.460974+00:00
-- url     : https://prove2.me/theorems/f745e3ad-e8dc-4ddc-ac98-70bc5aaea2a0
-- title:
--   Statement I
-- statement:
--   Definitions and structural lemmas for Statement I, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementI.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
namespace Formalism.L2.Th1.A
def WpCleared : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (wpReg W) = 0 ∧ (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    (-2 + X ^ 3 * derivative K (wpReg W)) ^ 2 =
      4 * (1 + X ^ 2 * wpReg W) ^ 3 - C (g₂ W) * X ^ 4 * (1 + X ^ 2 * wpReg W) - C (g₃ W) * X ^ 6
def WpInU : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    X ^ 2 * (1 + logSer W ^ 2 * (wpReg W).subst (logSer W)) =
      logSer W ^ 2 * (xS W + C (W.b₂ / 12) * X ^ 2)
def TInZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (xP : K),
    (tS W xP).subst (expSer W) * (1 + X ^ 2 * wpReg W - C (xP + W.b₂ / 12) * X ^ 2) = X ^ 2
def CubeTwoR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ c : MvPowerSeries (Fin 2) R, MvPowerSeries.constantCoeff c = -1 ∧
      U₂ ^ 2 * (xS W).subst (U₁ : MvPowerSeries (Fin 2) R)
        - U₁ ^ 2 * (xS W).subst (U₂ : MvPowerSeries (Fin 2) R)
        = c * fgl W * MvPowerSeries.subst
            (![U₁, (iSer W).subst (U₂ : MvPowerSeries (Fin 2) R)] :
              Fin 2 → MvPowerSeries (Fin 2) R) (fgl W)
def CubeThreeR : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    let t : Fin 3 → MvPowerSeries (Fin 3) R := fun i => MvPowerSeries.X i
    let row : Fin 3 → Fin 3 → MvPowerSeries (Fin 3) R := fun i =>
      ![t i ^ 3, t i * (xS W).subst (t i), (yS W).subst (t i)]
    ∃ e : MvPowerSeries (Fin 3) R, MvPowerSeries.constantCoeff e = -1 ∧
      (Matrix.of row).det
        = e * MvPowerSeries.subst
              (![MvPowerSeries.subst (![t 0, t 1] : Fin 2 → MvPowerSeries (Fin 3) R) (fgl W), t 2] :
                Fin 2 → MvPowerSeries (Fin 3) R) (fgl W)
            * (t 0 - t 1) * (t 0 - t 2) * (t 1 - t 2)
def CoeffMem : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R) (S : Subring R),
    W.a₁ ∈ S → W.a₂ ∈ S → W.a₃ ∈ S → W.a₄ ∈ S → W.a₆ ∈ S →
    (∀ n, coeff n (wSer W) ∈ S) ∧ (∀ n, coeff n (xS W) ∈ S) ∧ (∀ n, coeff n (yS W) ∈ S) ∧
    (∀ n, coeff n (fw W) ∈ S) ∧ (∀ n, coeff n (om W) ∈ S) ∧ (∀ n, coeff n (iSer W) ∈ S) ∧
    (∀ d, MvPowerSeries.coeff d (fgl W) ∈ S) ∧ (∀ (k : ℤ) n, coeff n (zSer W k) ∈ S) ∧
    ((∃ h ∈ S, 2 * h = 1) → ∀ n, coeff n (halfSer W) ∈ S) ∧
    (∀ xP ∈ S, ∀ n, coeff n (tS W xP) ∈ S) ∧
    (∀ xP ∈ S, ∀ yP ∈ S, ∀ n, coeff n (xPlus W xP yP) ∈ S ∧ coeff n (yPlus W xP yP) ∈ S)
def LogCoeff : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℕ),
    ((n + 1 : ℕ) : K) * coeff (n + 1) (logSer W) = coeff n (om W)
end Formalism.L2.Th1.A


