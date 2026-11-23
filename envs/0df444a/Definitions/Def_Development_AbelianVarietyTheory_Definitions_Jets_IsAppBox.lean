-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_IsAppBox
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_IsAppBox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:56:38.10832+00:00
-- url     : https://prove2.me/theorems/e8d1b09d-43ee-4420-b961-7ad0f5ade041
-- title:
--   Is App Box
-- statement:
--   Definitions and structural lemmas for Is App Box, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/IsAppBox.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.BoxApp
def IsApp {R : Type} [CommRing R] [IsDomain R] {D D₂ D' : DegPre R} {n₁ n₂ : ℕ} (pD₂ : IsPowDeg D₂ D n₂)
    (pD : IsPowDeg D' D (n₁ + n₂)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
    (a : Fin n₁ → Fam D F k) (sb : Fam D₂ F k) (S : Fam D' F k) : Prop :=
  ∃ (l : ℕ) (c : Fin l → F) (u : Fin l → Fin n₂ → Fam D F k) (S₂ : Fin l → Fam D₂ F k) (S' : Fin l → Fam D' F k),
    (∀ j, IsBoxFam pD₂ F k (S₂ j) (u j)) ∧ (∀ j, IsBoxFam pD F k (S' j) (Fin.append a (u j))) ∧
      sb = ∑ j, c j • S₂ j ∧ S = ∑ j, c j • S' j
end GlobalTheory.BoxApp


