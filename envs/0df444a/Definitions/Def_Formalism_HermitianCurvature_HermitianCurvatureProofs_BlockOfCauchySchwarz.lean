-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:52:54.809964+00:00
-- url     : https://prove2.me/theorems/73d3f25b-6e65-4992-8138-505fcd3d2758
-- title:
--   Block Of Cauchy Schwarz
-- statement:
--   Definitions and structural lemmas for Block Of Cauchy Schwarz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BlockOfCauchySchwarz.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
section block
variable {α β : Type} (Y₁ : Finset α) (Y₂ : Finset β)
noncomputable def qf {γ : Type} (Y : Finset γ) (k : γ → γ → ℂ) (c : γ → ℂ) : ℂ :=
  ∑ x ∈ Y, ∑ y ∈ Y, conj (c x) * k x y * c y
def blockK (a : α → α → ℂ) (w : α → β → ℂ) (b : β → β → ℂ) : α ⊕ β → α ⊕ β → ℂ :=
  fun x y => match x, y with
    | .inl p, .inl q => a p q
    | .inl p, .inr q => w p q
    | .inr q, .inl p => conj (w p q)
    | .inr p, .inr q => b p q
end block
end Formalism.FourierDecayAlt.P.PBA


