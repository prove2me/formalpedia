-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:06.586817+00:00
-- url     : https://prove2.me/theorems/00c843a5-06bb-4894-bb39-391d6ce19a5e
-- title:
--   Conjugate Ne Self
-- statement:
--   Definitions and structural lemmas for Conjugate Ne Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ConjugateNeSelf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP Matrix
namespace GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
open Classical in

def tauPt (τ : L →+* ℂ) (B : GL (Fin n) ℂ) : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ := fun σ =>
  if σ = τ then B.val else if σ = ComplexEmbedding.conjugate τ then (B⁻¹).valᵀ else 1
end GlobalTheory.AlgWtHW


