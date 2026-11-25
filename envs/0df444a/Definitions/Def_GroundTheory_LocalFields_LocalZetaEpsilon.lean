-- Prove2me | Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
-- name    : GroundTheory_LocalFields_LocalZetaEpsilon
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:46.698572+00:00
-- url     : https://prove2.me/theorems/b56e9809-367c-5e4a-9346-6e2326edfe19
-- title:
--   Local Zeta Epsilon
-- statement:
--   Definitions and structural lemmas for Local Zeta Epsilon, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalZetaEpsilon.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
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
section Powers
end Powers
section Characters
variable {χ : Kˣ →* ℂˣ}
variable (χ) in
open Classical in

def quasiCharExt (x : K) : ℂ := if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)
end Characters
section SchwartzBruhat
end SchwartzBruhat
variable [MeasurableSpace K] [BorelSpace K]
section Epsilon
open Classical in

def localEpsilon (χ : Kˣ →* ℂˣ) (ψ : AddChar K Circle) (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then
    ((χ (unifUnit K ^ addCharConductor ψ) : ℂˣ) : ℂ)⁻¹ *
      ((modulus ((unifUnit K ^ addCharConductor ψ : Kˣ) : K) : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - s)
  else
    ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
        valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
      quasiCharExt χ⁻¹ x * ((modulus x : ℝ) : ℂ) ^ (-s) * (ψ x : ℂ) ∂selfDualMeasure ψ
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
end Epsilon
section ZetaBasics
variable {χ : Kˣ →* ℂˣ}
end ZetaBasics
section Unramified
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ
end Unramified
section Ramified
def oneAddValBallIndicator (c : ℤ) : K → ℂ :=
  {x : K | x - 1 ∈ valBall K c}.indicator fun _ => 1
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
end Ramified
section RamifiedFourier
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ
end RamifiedFourier
section FunctionalEquation
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
  (hχ : Continuous χ)
include hψ hψ1 hχ
end FunctionalEquation
end GroundTheory.LocalField


