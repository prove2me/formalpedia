-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:24:09.087879+00:00
-- url     : https://prove2.me/theorems/f2744195-b8de-4df8-9ae0-72bb04176064
-- title:
--   Calc Exp
-- statement:
--   Definitions and structural lemmas for Calc Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcExp.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
section Two
variable (k : Type) [CommRing k] [Algebra ℚ k]
end Two
section General
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
end General
section Inj
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
end Inj
section Log
variable {k : Type} [CommRing k] [Algebra ℚ k] {σ : Type}
end Log
section Props
def ExpAddSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a b : MvPowerSeries σ k), constantCoeff a = 0 →
    constantCoeff b = 0 → PowerSeries.subst (a + b) (PowerSeries.exp k) =
      PowerSeries.subst a (PowerSeries.exp k) * PowerSeries.subst b (PowerSeries.exp k)
def ExpConstSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a : MvPowerSeries σ k), constantCoeff a = 0 →
    constantCoeff (PowerSeries.subst a (PowerSeries.exp k)) = 1
def ExpInjSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a b : MvPowerSeries σ k), constantCoeff a = 0 →
    constantCoeff b = 0 → PowerSeries.subst a (PowerSeries.exp k) = PowerSeries.subst b (PowerSeries.exp k) → a = b
def ExpLogSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (f : MvPowerSeries σ k), constantCoeff f = 1 →
    constantCoeff (PowerSeries.subst (f - 1) (PowerSeries.log k)) = 0 ∧
      PowerSeries.subst (PowerSeries.subst (f - 1) (PowerSeries.log k)) (PowerSeries.exp k) = f
def LogExpSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ : Type) (a : MvPowerSeries σ k), constantCoeff a = 0 →
    PowerSeries.subst (PowerSeries.subst a (PowerSeries.exp k) - 1) (PowerSeries.log k) = a
def SubstExpSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (σ τ : Type) [Finite σ] (φ : σ → MvPowerSeries τ k)
    (a : MvPowerSeries σ k), (∀ s, constantCoeff (φ s) = 0) → constantCoeff a = 0 →
    MvPowerSeries.subst φ (PowerSeries.subst a (PowerSeries.exp k)) =
      PowerSeries.subst (MvPowerSeries.subst φ a) (PowerSeries.exp k)
end Props
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing


