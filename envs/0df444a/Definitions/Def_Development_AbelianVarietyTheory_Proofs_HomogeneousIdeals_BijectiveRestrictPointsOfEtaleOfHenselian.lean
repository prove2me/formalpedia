-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:57.415383+00:00
-- url     : https://prove2.me/theorems/4f4658ff-dd96-4fef-9ca2-f58186b28758
-- title:
--   Bijective Restrict Points Of Etale Of Henselian
-- statement:
--   Definitions and structural lemmas for Bijective Restrict Points Of Etale Of Henselian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/BijectiveRestrictPointsOfEtaleOfHenselian.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace GlobalTheory
def restrictPoints {X S T₀ T : Scheme.{u}} (f : X ⟶ S) (h : T ⟶ S) (i : T₀ ⟶ T) :
    {l : T ⟶ X // l ≫ f = h} → {g : T₀ ⟶ X // g ≫ f = i ≫ h} :=
  fun l ↦ ⟨i ≫ l.1, by rw [Category.assoc, l.2]⟩
end GlobalTheory


