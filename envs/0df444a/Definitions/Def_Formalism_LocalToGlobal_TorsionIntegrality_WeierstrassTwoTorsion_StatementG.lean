-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:51.350709+00:00
-- url     : https://prove2.me/theorems/317c3a7d-ede9-47c8-a1ea-7a7b56447b4d
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementG.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
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
abbrev U₁ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 0
abbrev U₂ {R : Type u} [CommRing R] : MvPowerSeries (Fin 2) R := MvPowerSeries.X 1
def FglMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    MvPowerSeries.map φ (fgl W) = fgl (W.map φ)
def FglChord : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    lam W * (U₂ - U₁) = (wSer W).subst (U₂ : MvPowerSeries (Fin 2) R) - (wSer W).subst (U₁ : MvPowerSeries (Fin 2) R) ∧
    MvPowerSeries.constantCoeff (uThird W) = 0 ∧
    wThird W = (wSer W).subst (uThird W) ∧
    fgl W = (iSer W).subst (uThird W) ∧
    MvPowerSeries.constantCoeff (fgl W) = 0 ∧
    MvPowerSeries.coeff (Finsupp.single 0 1) (fgl W) = 1 ∧
    MvPowerSeries.coeff (Finsupp.single 1 1) (fgl W) = 1
def FglSum : Prop :=
  ∀ (K : Type u) [Field K] (W : WeierstrassCurve K),
    Formalism.ELL.ChordAt W (wSer W) U₁ U₂ (fgl W)
def FglGroup : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    ∃ F : FormalGroup R, F.toPowerSeries = fgl W ∧ F.IsComm
def FglInvariant : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    MvPowerSeries.pderiv R 0 (fgl W) * (fw W).subst (U₁ : MvPowerSeries (Fin 2) R)
      = (fw W).subst (fgl W) ∧
    MvPowerSeries.pderiv R 1 (fgl W) * (fw W).subst (U₂ : MvPowerSeries (Fin 2) R)
      = (fw W).subst (fgl W)
def FglLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (fgl W) = (logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K) ∧
    fgl W = (expSer W).subst ((logSer W).subst (U₁ : MvPowerSeries (Fin 2) K)
      + (logSer W).subst (U₂ : MvPowerSeries (Fin 2) K))
def FglLogBase : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [Field K] [CharZero K] (φ : R →+* K)
    (W : WeierstrassCurve R),
    (logSer (W.map φ)).subst (MvPowerSeries.map φ (fgl W))
      = (logSer (W.map φ)).subst (U₁ : MvPowerSeries (Fin 2) K)
        + (logSer (W.map φ)).subst (U₂ : MvPowerSeries (Fin 2) K)
def FglInv : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    MvPowerSeries.subst (![X, iSer W] : Fin 2 → R⟦X⟧) (fgl W) = 0
def ZSerSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R),
    (∀ n : ℤ, constantCoeff (zSer W n) = 0 ∧ coeff 1 (zSer W n) = (n : R)) ∧
    zSer W 0 = 0 ∧ zSer W 1 = X ∧ zSer W (-1) = iSer W ∧
    (∀ n : ℕ, zSer W (n : ℤ) = nSer W n) ∧
    (∀ m n : ℤ, MvPowerSeries.subst (![zSer W m, zSer W n] : Fin 2 → R⟦X⟧) (fgl W)
      = zSer W (m + n)) ∧
    (∀ m n : ℤ, (zSer W m).subst (zSer W n) = zSer W (m * n))
def ZSerMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)
    (n : ℤ), PowerSeries.map φ (zSer W n) = zSer (W.map φ) n
def ZSerLog : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (n : ℤ),
    (logSer W).subst (zSer W n) = C (n : K) * logSer W
def HalfSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (W : WeierstrassCurve R), IsUnit (2 : R) →
    constantCoeff (halfSer W) = 0 ∧ 2 * coeff 1 (halfSer W) = 1 ∧
    (nSer W 2).subst (halfSer W) = X ∧ (halfSer W).subst (nSer W 2) = X ∧
    MvPowerSeries.subst (![halfSer W, halfSer W] : Fin 2 → R⟦X⟧) (fgl W) = X
def HalfLog : Prop :=
  (∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    2 * (logSer W).subst (halfSer W) = logSer W) ∧
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R),
    IsUnit (2 : R) → PowerSeries.map φ (halfSer W) = halfSer (W.map φ)
end Formalism.L2.Th1.A


