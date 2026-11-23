-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_AbelianLaws_PrincipalPolarisationOneSection
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_AbelianLaws_PrincipalPolarisationOneSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:53.486772+00:00
-- url     : https://prove2.me/theorems/e86f4888-d67a-4743-9d84-78c38ccd06e3
-- title:
--   Principal Polarisation One Section
-- statement:
--   Definitions and structural lemmas for Principal Polarisation One Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/AbelianLaws/PrincipalPolarisationOneSection.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.Published
def principalPolarisationOneSection : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1
namespace principalPolarisationOneSection
end principalPolarisationOneSection
end GlobalTheory.Published
abbrev GlobalTheory.AbLaw.principalPolarisationOneSection : Prop := GlobalTheory.Published.principalPolarisationOneSection
example : GlobalTheory.AbLaw.principalPolarisationOneSection ↔ ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))), Module.finrank Γ((baseOver (Spec (CommRingCat.of K))).left, ⊤) (SecM P.A P.L 1 (baseOver (Spec (CommRingCat.of K)))) = 1 := Iff.rfl


