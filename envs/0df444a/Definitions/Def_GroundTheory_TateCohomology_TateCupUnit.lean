-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_TateCupUnit
-- name    : GroundTheory_TateCohomology_TateCupUnit
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:37:33.564431+00:00
-- url     : https://prove2.me/theorems/197976cd-bc92-4fef-bc07-313e8538c25d
-- title:
--   Tate Cup Unit
-- statement:
--   Definitions and structural lemmas for Tate Cup Unit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
namespace GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
section Unitors
variable (E : ShortComplex (Rep.{u} k G))
noncomputable def leftUnitorSCIso : E.map (tensorLeft (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (λ_ E.X₁) (λ_ E.X₂) (λ_ E.X₃) (leftUnitor_naturality E.f).symm
    (leftUnitor_naturality E.g).symm
noncomputable def rightUnitorSCIso : E.map (tensorRight (𝟙_ (Rep.{u} k G))) ≅ E :=
  ShortComplex.isoMk (ρ_ E.X₁) (ρ_ E.X₂) (ρ_ E.X₃) (rightUnitor_naturality E.f).symm
    (rightUnitor_naturality E.g).symm
variable {E}
variable [Fintype G]
end Unitors
variable [Fintype G]
variable (k G) in

noncomputable def tateOne : tateCohomology (𝟙_ (Rep.{u} k G)) 0 :=
  ((tateCohomologyZeroIso k G).app (𝟙_ (Rep.{u} k G))).inv.hom
    (Submodule.Quotient.mk ⟨(1 : k), fun _ => rfl⟩)
end GroundTheory.GroupCoh


