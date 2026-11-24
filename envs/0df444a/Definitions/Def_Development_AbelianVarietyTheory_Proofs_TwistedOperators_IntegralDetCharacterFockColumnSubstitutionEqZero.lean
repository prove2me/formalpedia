-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:29.282152+00:00
-- url     : https://prove2.me/theorems/734b15b7-2ee4-4d04-a89e-93a2ecc23267
-- title:
--   Integral Det Character Fock Column Substitution Eq Zero
-- statement:
--   Definitions and structural lemmas for Integral Det Character Fock Column Substitution Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]
def scalAt {a : ℕ} (τ₀ : ι) (ζ : ℂ) : ι → Matrix (Fin a) (Fin a) ℂ := fun τ => if τ = τ₀ then ζ • 1 else 1
def degAt {d a : ℕ} (τ₀ : ι) (t : Var ι d a →₀ ℕ) : ℕ := t.sum fun y n => if y.1 = τ₀ then n else 0
end GlobalTheory.MinorFrame
noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]
end GlobalTheory.MinorFrame
noncomputable section
namespace GlobalTheory.MinorFrame
open MvPolynomial
end GlobalTheory.MinorFrame


