-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FglPtW
-- name    : Formalism_PeriodIntegrals_FglPtW
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:38:14.397819+00:00
-- url     : https://prove2.me/theorems/438872ea-a0dc-4501-92a1-4111d50a12ec
-- title:
--   Fgl Pt W
-- statement:
--   Definitions and structural lemmas for Fgl Pt W, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FglPtW.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FglPtW
def SerOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (F : MvPowerSeries σ K) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ S
def PtOver {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (a : MvPowerSeries σ K) : Prop :=
  SerOver S a ∧ MvPowerSeries.constantCoeff a = 0
def AddGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    SerOver S (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) →
    ∀ (σ : Type) (a b : MvPowerSeries σ K), PtOver S a → PtOver S b →
      PtOver S (PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex)
def MulGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    ∀ c : K, SerOver S (PowerSeries.subst
      (MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) →
    ∀ (σ : Type) (a : MvPowerSeries σ K), PtOver S a →
      PtOver S (PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex)
def LinGen : Prop :=
  ∀ (K : Type) [CommRing K] (S : Subring K) (l ex : PowerSeries K),
    PowerSeries.constantCoeff ex = 0 → PowerSeries.subst ex l = PowerSeries.X →
    SerOver S (PowerSeries.subst
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) →
    ∀ (ι : Type) [Fintype ι] (c : ι → K),
    (∀ j, SerOver S (PowerSeries.subst
      (MvPowerSeries.C (c j) * PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex)) →
    ∀ (σ : Type) (a : ι → MvPowerSeries σ K), (∀ j, PtOver S (a j)) →
      PtOver S (PowerSeries.subst (∑ j, MvPowerSeries.C (c j) * PowerSeries.subst (a j) l) ex)
end PI.FglPtW
end


