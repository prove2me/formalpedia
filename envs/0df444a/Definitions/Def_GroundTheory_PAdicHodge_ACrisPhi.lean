-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_ACrisPhi
-- name    : GroundTheory_PAdicHodge_ACrisPhi
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:10:14.247437+00:00
-- url     : https://prove2.me/theorems/0b6355a1-f73a-52d2-a303-9a3c169b1de4
-- title:
--   ACris Phi
-- statement:
--   Definitions and structural lemmas for ACris Phi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/ACrisPhi.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog
import Definitions.Def_GroundTheory_PAdicHodge_LogPowSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open _root_.WittVector Polynomial
namespace ACris
section Coefficients
variable (q : ℕ)
def powCoeff (N m : ℕ) : ℤ := ((((1 : ℤ[X]) + X) ^ q - 1) ^ N).coeff m
end Coefficients
end ACris
namespace ACris
section Expansion
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
variable (p) in

def logCoeff (n j : ℕ) : ℤ :=
  (-1) ^ n * powCoeff p (n + 1) (j + 1) * (((j + 1).factorial / (n + 1) : ℕ) : ℤ)
variable {x : AInf K p}
theorem one_add_pow_sub_one_mem (hx : x ∈ RingHom.ker θ) : (1 + x) ^ p - 1 ∈ RingHom.ker θ := by
  rw [RingHom.mem_ker] at hx ⊢
  rw [map_sub, map_pow, map_add, map_one, hx, add_zero, one_pow, sub_self]
end Expansion
end ACris
namespace ACris
section PhiT
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}
variable {x : AInf K p}
end PhiT
end ACris
end GroundTheory.PAdicHodge


