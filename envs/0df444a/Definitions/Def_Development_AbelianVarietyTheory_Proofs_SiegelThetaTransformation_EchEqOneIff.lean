-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:28.329379+00:00
-- url     : https://prove2.me/theorems/c2af9f8c-84c0-4749-a7eb-03b2d422e67a
-- title:
--   Ech Eq One Iff
-- statement:
--   Definitions and structural lemmas for Ech Eq One Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/EchEqOneIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.FourierJ
noncomputable section
variable {κ ι : Type}
def rep (R : ℕ) (n : κ → ι → Fin (R * R)) : Matrix κ ι ℚ :=
  Matrix.of fun k i => ((n k i : ℕ) : ℚ) / R
def zm (m : κ → ι → ℤ) : Matrix κ ι ℚ := Matrix.of fun k i => (m k i : ℚ)
def zv (m : ι → ℤ) : ι → ℚ := fun i => (m i : ℚ)
def ech (t : ℚ) : ℂ := cexp (2 * π * I * (t : ℂ))
def gs [Fintype ι] (τ : Matrix ι ι ℂ) (ζ : ι → ℂ) (v : ι → ℚ) : ℂ :=
  cexp (π * I * (qv v ⬝ᵥ τ *ᵥ qv v + 2 * (qv v ⬝ᵥ ζ)))
end
end GlobalTheory.SW.FourierJ


