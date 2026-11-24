-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsAdaptedFrameBigCell
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T17:37:56.932508+00:00
-- url     : https://prove2.me/theorems/3fa4bb3f-1547-4846-836a-928d5a336b8c
-- title:
--   Exists Adapted Frame Big Cell
-- statement:
--   Definitions and structural lemmas for Exists Adapted Frame Big Cell, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsAdaptedFrameBigCell.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiagMatLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TopologicalSpace GlobalTheory.FlagPts
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W]
variable (k) in

def spanFrom (f : ℕ → W) (N m : ℕ) : Submodule k W := Submodule.span k (f '' {a | m ≤ a ∧ a < N})
end GlobalTheory.FlagPts.SphericalEisensteinCover
namespace GlobalTheory.FlagPts.SphericalEisensteinCover
variable {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
def Inv (Fs : ℕ → Submodule k W) (A : Submodule k W) (f : ℕ → W) (m : ℕ) : Prop :=
  ∀ m', m ≤ m' → Disjoint (Fs m') (spanFrom k f (finrank k W) m') ∧
    Disjoint A (spanFrom k f (finrank k W) m') ∧
    finrank k (spanFrom k f (finrank k W) m') = finrank k W - m'
end GlobalTheory.FlagPts.SphericalEisensteinCover
namespace GlobalTheory.FlagPts
end GlobalTheory.FlagPts


