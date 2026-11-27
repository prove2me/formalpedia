-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:05.295244+00:00
-- url     : https://prove2.me/theorems/975b2517-8903-5361-a643-e7793be8e7a8
-- title:
--   Multipliable Tp Factor
-- statement:
--   Definitions and structural lemmas for Multipliable Tp Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/MultipliableTpFactor.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open UpperHalfPlane hiding I
open scoped Real
noncomputable section
namespace GlobalTheory.JacobiTriple
def qPoch (t : ℂ) (m : ℕ) : ℂ := ∏ i ∈ Finset.range m, (1 - t ^ (i + 1))
def qPochInf (t : ℂ) : ℂ := ∏' i : ℕ, (1 - t ^ (i + 1))
def qBinom (t : ℂ) (m k : ℕ) : ℂ := qPoch t m / (qPoch t k * qPoch t (m - k))
def finCoeff (t : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  if j.natAbs ≤ n then qBinom t (2 * n) ((n : ℤ) + j).toNat else 0
end GlobalTheory.JacobiTriple


