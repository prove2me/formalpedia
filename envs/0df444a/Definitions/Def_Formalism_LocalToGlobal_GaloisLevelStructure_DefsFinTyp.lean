-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
-- name    : Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:11:22.508625+00:00
-- url     : https://prove2.me/theorems/fc8f1b06-f999-4e5a-8ebd-254edafb39a8
-- title:
--   Defs Fin Typ
-- statement:
--   Definitions and structural lemmas for Defs Fin Typ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GaloisLevelStructure/DefsFinTyp.lean

import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
namespace Formalism.L2.NG
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
structure FinTyp where
  S : Submodule ℂ (GAf L n → ℂ)
  stable : ∀ h, ∀ f ∈ S, rt L n h f ∈ S
  smooth : ∀ f ∈ S, ∃ N : ℕ, 0 < N ∧ ∀ κ, Cong L n N κ → rt L n κ f = f
  ne : S ≠ ⊥
  irr : ∀ S' : Submodule ℂ (GAf L n → ℂ), S' ≤ S → (∀ h, ∀ f ∈ S', rt L n h f ∈ S') → S' = ⊥ ∨ S' = S
variable {L n}
def FinTyp.Iso (π π' : FinTyp L n) : Prop := IsoRep π.S π'.S
end Formalism.L2.NG


