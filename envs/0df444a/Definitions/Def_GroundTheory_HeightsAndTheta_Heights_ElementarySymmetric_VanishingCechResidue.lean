-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_VanishingCechResidue
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_VanishingCechResidue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:58.358545+00:00
-- url     : https://prove2.me/theorems/0f176f56-5a68-4252-abe1-e8701166e109
-- title:
--   Vanishing Cech Residue
-- statement:
--   Definitions and structural lemmas for Vanishing Cech Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/VanishingCechResidue.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ZeroSetFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauIIsBasisOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.KeyFormula
open Complex Matrix
noncomputable section
open RigSymForm
def VanishingCechResidue.Statement : Prop :=
  ∀ (P : RigSymForm ℂ) (a : ℕ), 3 ≤ a → ∀ (r : ℕ) (x : Fin (r + 1) → P.Fn), P.IsBasisOf a x →
    ∀ b : ℕ, b < a → ∃ c₀ : ℕ, ∀ c, c₀ ≤ c → ∀ (q : ℕ) (φ : Finset (Fin (r + 1)) → P.Fn),
      P.IsCocycle a (b + a * c) (q + 1) x φ → P.IsCoboundary a (b + a * c) q x φ
end
end GroundTheory.Heights₂.Heights.KeyFormula


