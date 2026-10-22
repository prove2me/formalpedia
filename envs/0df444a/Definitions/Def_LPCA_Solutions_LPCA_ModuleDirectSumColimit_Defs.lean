-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
-- name    : LPCA_Solutions_LPCA_ModuleDirectSumColimit_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:04.677023+00:00
-- url     : https://prove2.me/theorems/64fed058-e718-4124-a9b0-5039d3e60d45
-- title:
--   Concrete module direct sums as categorical coproducts
-- statement:
--   For a ring R and an arbitrary index type J with decidable equality, the actual dependent direct sum of a J-indexed family of R-modules, with its standard component inclusions, satisfies the categorical coproduct universal property. J need not be finite, and the empty family is included.
--
--   The included constructions and necessary compatibility results are:
--
--   - The concrete dependent direct sum, with its actual component inclusions, is a coproduct cocone in the module category.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ModuleDirectSumColimit.lean, selected declarations in lines 17–46; source SHA-256 a8c5a096d415d04006c189f1c27427beacdaedc25a3c646aaa5323279e1fddea; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.DirectSum.Module

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable (R : Type u) [Ring R]
variable {J : Type u} [DecidableEq J]

/-- The concrete dependent direct sum, with its actual component inclusions,
is a coproduct cocone in the module category. -/
noncomputable abbrev moduleDirectSumCocone (A : J → ModuleCat.{u} R) :
    Cocone (Discrete.functor A) where
  pt := ModuleCat.of R (DirectSum J (fun j => A j))
  ι := Discrete.natTrans (fun j => ModuleCat.ofHom
    (DirectSum.lof R J (fun j => A j) j.as))

noncomputable def moduleDirectSumIsColimit (A : J → ModuleCat.{u} R) :
    IsColimit (moduleDirectSumCocone R A) where
  desc s := ModuleCat.ofHom (DirectSum.toModule R J s.pt
    (fun j => (s.ι.app ⟨j⟩).hom))
  fac s j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change DirectSum.toModule R J s.pt (fun j => (s.ι.app ⟨j⟩).hom)
      (DirectSum.lof R J (fun j => A j) j.as x) = _
    erw [DirectSum.toModule_lof]
  uniq s f hf := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro j
    apply LinearMap.ext
    intro x
    change f.hom (DirectSum.lof R J (fun j => A j) j x) =
      DirectSum.toModule R J s.pt (fun j => (s.ι.app ⟨j⟩).hom)
        (DirectSum.lof R J (fun j => A j) j x)
    erw [DirectSum.toModule_lof]
    exact congrArg (fun g => g x) (hf ⟨j⟩)

end LPCA


