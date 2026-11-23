-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeRatio
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:47.26266+00:00
-- url     : https://prove2.me/theorems/a61f1ebe-edda-48c7-81b3-3fda47872562
-- title:
--   Gauge Ratio
-- statement:
--   Definitions and structural lemmas for Gauge Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/GaugeRatio.lean

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
namespace ReciprocityTheory.ChartRestriction.G.TB
abbrev GLet (T : Type) (rk : T → ℕ) : Type := Σ σ : T, Fin (rk σ)
def scaleBy {O k T : Type} [CommRing O] [CommRing k] {rk : T → ℕ} (χ : T → O →+* k) (a : O) :
    MvPowerSeries (GLet T rk) k →+* MvPowerSeries (GLet T rk) k :=
  MvPowerSeries.rescale (fun l => χ l.1 a)
def GaugeRatioSt : Prop :=
  ∀ (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] (T : Type) [Fintype T]
    (rk : T → ℕ) (χ : T → O →+* k) (cc : T → T),
    (∀ σ a, χ (cc σ) a = χ σ (star a)) →
    (∀ σ τ, σ ≠ τ → ∃ a, IsUnit (χ σ a - χ τ a)) →
    ∀ r : MvPowerSeries (GLet T rk) k, constantCoeff r = 1 →
    (∀ a : O, scaleBy χ (1 + a * star a) r = scaleBy χ a r ^ 2 * r * scaleBy χ (a * star a) r) →
    ∃ q : MvPowerSeries (GLet T rk) k, constantCoeff q = 0 ∧
      (∀ m, coeff m q ≠ 0 → m.degree = 2) ∧
      (∀ l l' : GLet T rk, coeff (Finsupp.single l 1 + Finsupp.single l' 1) q ≠ 0 → l'.1 = cc l.1) ∧
      r = PowerSeries.subst q (PowerSeries.exp k)
end ReciprocityTheory.ChartRestriction.G.TB


