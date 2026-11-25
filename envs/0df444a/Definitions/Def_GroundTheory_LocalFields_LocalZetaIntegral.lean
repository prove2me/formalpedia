-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
-- name    : GroundTheory_LocalFields_LocalZetaIntegral
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T10:01:06.510798+00:00
-- url     : https://prove2.me/theorems/f8e29378-762f-535f-9942-de45f918d4e7
-- title:
--   Local Zeta Integral
-- statement:
--   Definitions and structural lemmas for Local Zeta Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaIntegral.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Theorems.Thm_GroundTheory_LocalField_qpow_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Laurent
variable (K) in

def qpowUnit (s : ℂ) : ℂˣ := Units.mk0 ((residueCard K : ℂ) ^ (-s)) (qpow_ne_zero s)
variable (K) in

def evalQpow (P : LaurentPolynomial ℂ) (s : ℂ) : ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) (qpowUnit K s) P
end Laurent
section Sums
end Sums
section LFactor
variable (χ : Kˣ →* ℂˣ)
open Classical in

def localLFactor (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
  else 1
variable {χ}
variable (hχ : Continuous χ)
include hχ
end LFactor
section ZetaNonvanishing₂
variable [MeasurableSpace K] [BorelSpace K]
def localZeta (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ u, f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K
variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}
open Classical in

def localZetaRatio (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if h : ∃ P : LaurentPolynomial ℂ, ∀ s : ℂ, -quasiCharExponent χ < s.re →
      localZeta f χ s = localLFactor χ s * evalQpow K P s then
    evalQpow K h.choose s
  else 0
end ZetaNonvanishing₂
end GroundTheory.LocalField


