-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:16.573802+00:00
-- url     : https://prove2.me/theorems/942f7509-6612-4c3b-862d-05f1a90825fc
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementT.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_CompInv
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
def DLCoeff : Prop :=
  ∀ (R : Type u) [CommRing R] (f : LaurentSeries R) (n : ℤ),
    (dL f).coeff n = ((n + 1 : ℤ) : R) * f.coeff (n + 1)
def DLLeibniz : Prop :=
  ∀ (R : Type u) [CommRing R] (f g : LaurentSeries R), dL (f * g) = f * dL g + g * dL f
def DLCoe : Prop :=
  ∀ (R : Type u) [CommRing R] (f : R⟦X⟧), dL (toL f) = toL (derivative R f)
def UPowRules : Prop :=
  ∀ (R : Type u) [CommRing R],
    (uPow 0 : LaurentSeries R) = 1 ∧ (uPow 1 : LaurentSeries R) = toL X ∧
    (∀ m n : ℤ, (uPow (m + n) : LaurentSeries R) = uPow m * uPow n) ∧
    (∀ n : ℤ, dL (uPow n : LaurentSeries R) = HahnSeries.C ((n : ℤ) : R) * uPow (n - 1)) ∧
    (∀ r : R, dL (HahnSeries.C r : LaurentSeries R) = 0) ∧
    (∀ r : R, toL (C r) = (HahnSeries.C r : LaurentSeries R))
def ToLInjective : Prop :=
  ∀ (R : Type u) [CommRing R],
    Function.Injective (toL : R⟦X⟧ → LaurentSeries R) ∧
    ∀ (n : ℤ) (f g : LaurentSeries R), uPow n * f = uPow n * g → f = g
def CompInvSpec : Prop :=
  ∀ (R : Type u) [CommRing R] (s : R⟦X⟧), constantCoeff s = 0 → IsUnit (coeff 1 s) →
    constantCoeff (compInv s) = 0 ∧ s.subst (compInv s) = X ∧ (compInv s).subst s = X ∧
    coeff 1 (compInv s) * coeff 1 s = 1 ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → s.subst t = X → t = compInv s) ∧
    (∀ t : R⟦X⟧, constantCoeff t = 0 → t.subst s = X → t = compInv s)
def CompInvMap : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] (φ : R →+* S) (s : R⟦X⟧),
    constantCoeff s = 0 → IsUnit (coeff 1 s) →
    PowerSeries.map φ (compInv s) = compInv (PowerSeries.map φ s)
def IntegSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (f : K⟦X⟧),
    constantCoeff (integ f) = 0 ∧ derivative K (integ f) = f ∧
    ∀ g : K⟦X⟧, constantCoeff g = 0 → derivative K g = f → g = integ f
end Formalism.L2.Th1.A


