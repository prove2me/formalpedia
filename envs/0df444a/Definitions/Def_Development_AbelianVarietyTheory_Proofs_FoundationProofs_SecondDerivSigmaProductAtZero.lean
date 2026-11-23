-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_SecondDerivSigmaProductAtZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:11:27.873082+00:00
-- url     : https://prove2.me/theorems/f5811074-4168-466a-b1a7-a8547872d280
-- title:
--   Second Deriv Sigma Product At Zero
-- statement:
--   Definitions and structural lemmas for Second Deriv Sigma Product At Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SecondDerivSigmaProductAtZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology PeriodPair
namespace GlobalTheory.JetConj
noncomputable def wr (f : ℂ → ℂ) (z : ℂ) : ℂ := f z * deriv (deriv f) z - deriv f z ^ 2
structure IsSigmaLike (L : PeriodPair) (σ : ℂ → ℂ) : Prop where
  diff : Differentiable ℂ σ
  deriv_zero : deriv σ 0 = 1
  zero_iff : ∀ z, σ z = 0 ↔ z ∈ L.lattice
  add : ∀ u v, u ∉ L.lattice → v ∉ L.lattice →
    (℘[L] u - ℘[L] v) * (σ u ^ 2 * σ v ^ 2) = -(σ (u + v) * σ (u - v))
variable {L : PeriodPair} {σ : ℂ → ℂ}
noncomputable def divQuot (σ : ℂ → ℂ) (u : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  σ (n * z + n * u) / σ (z + u) ^ (n ^ 2)
end GlobalTheory.JetConj


