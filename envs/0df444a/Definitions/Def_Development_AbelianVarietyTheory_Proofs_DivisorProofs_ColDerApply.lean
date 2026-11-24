-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColDerApply
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:10:46.274524+00:00
-- url     : https://prove2.me/theorems/f28b8908-e447-43d4-9076-cb8affc65c1c
-- title:
--   Col Der Apply
-- statement:
--   Definitions and structural lemmas for Col Der Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColDerApply.lean

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
noncomputable section
open MvPolynomial
namespace GlobalTheory.ColLie
open GlobalTheory.MinorFrame
variable {ι : Type} [DecidableEq ι]
def colDer {d a : ℕ} (τ : ι) (S : Matrix (Fin a) (Fin a) ℂ) : Module.End ℂ (Pol ι d a) :=
  ∑ i : Fin d, ∑ j : Fin a, ∑ k : Fin a,
    S k j • (LinearMap.mulLeft ℂ (X (τ, i, k) : Pol ι d a) ∘ₗ (pderiv (τ, i, j)).toLinearMap)
def atPl {a : ℕ} (τ : ι) (g : Matrix (Fin a) (Fin a) ℂ) : ι → Matrix (Fin a) (Fin a) ℂ :=
  Function.update 1 τ g
end GlobalTheory.ColLie
end


