-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PerFactor
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_PerFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:12.907952+00:00
-- url     : https://prove2.me/theorems/068ba3ef-66f8-41d3-9ace-6caa52950ae3
-- title:
--   Per Factor
-- statement:
--   Definitions and structural lemmas for Per Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PerFactor.lean

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
namespace GlobalTheory.PolDeg.Taut
variable (W : Type) [CommRing W] [IsDomain W]
def coordT (m N : ℕ) (k : Fin N) : MvPowerSeries (Fin N) W :=
  if (k : ℕ) < m then MvPowerSeries.X k else 1 + MvPowerSeries.X k
def params {m N : ℕ} (h : m ≤ N) : Fin m → MvPowerSeries (Fin N) W := fun i => MvPowerSeries.X (Fin.castLE h i)
def perFactor (m N n r : ℕ) (ε : Fin N → LinearMap.BilinForm ℤ (Fin r → ℤ)) (a b : Fin r → ℤ) : FractionRing (MvPowerSeries (Fin N) W) :=
  ∏ k, (algebraMap (MvPowerSeries (Fin N) W) (FractionRing (MvPowerSeries (Fin N) W)) (coordT W m N k)) ^ ((n : ℤ) * ε k a b)
example : perFactor W 0 0 3 0 (fun k => k.elim0) 0 0 = 1 := by simp [perFactor]
end GlobalTheory.PolDeg.Taut


