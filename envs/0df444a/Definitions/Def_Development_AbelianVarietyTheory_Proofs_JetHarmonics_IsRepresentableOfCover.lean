-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsRepresentableOfCover
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:09.292887+00:00
-- url     : https://prove2.me/theorems/18f10665-701c-4f77-9aa5-5b600f8c452f
-- title:
--   Is Representable Of Cover
-- statement:
--   Definitions and structural lemmas for Is Representable Of Cover, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsRepresentableOfCover.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.GenTorsor
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}}
def pb (a : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (h : W ≤ a ⁻¹ᵁ U) : Γ(X, U)ˣ →* Γ(Y, W)ˣ :=
  Units.map (a.appLE U W h).hom
section Cover
variable {J : Type*} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
end Cover
end GlobalTheory.GenTorsor


