-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ExactnessThroughIsomorphisms_Defs
-- name    : LPCA_Solutions_LPCA_ExactnessThroughIsomorphisms_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:22:09.830481+00:00
-- url     : https://prove2.me/theorems/dd681cee-e5a5-49a4-b8b8-91de7a44d100
-- title:
--   Transport of zero composites through isomorphism squares
-- statement:
--   In an abelian category, the selected lemma transports a zero composite through three specified object isomorphisms and two specified commuting squares. This bundle contains the zero-composite lemma, not an additional exactness theorem.
--
--   The included constructions and necessary compatibility results are:
--
--   - Transport the zero composite through specified object isomorphisms and specified commuting squares. No map or exactness hypothesis is replaced.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ExactnessThroughIsomorphisms.lean, selected declarations in lines 13–28; source SHA-256 995e8bb7abee1cc298b2bf96d86a184a6ee85fcd80feeaf20fd4d7bceae32950; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.ShortComplex.Exact

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Transport the zero composite through specified object isomorphisms and
specified commuting squares. No map or exactness hypothesis is replaced. -/
theorem shortComplexIso_zero {A B D A' B' D' : C}
    (f : A ⟶ B) (g : B ⟶ D) (w : f ≫ g = 0)
    (eA : A' ≅ A) (eB : B' ≅ B) (eD : D' ≅ D)
    (f' : A' ⟶ B') (g' : B' ⟶ D')
    (hf : f' ≫ eB.hom = eA.hom ≫ f)
    (hg : g' ≫ eD.hom = eB.hom ≫ g) : f' ≫ g' = 0 := by
  apply (cancel_mono eD.hom).mp
  calc
    (f' ≫ g') ≫ eD.hom = f' ≫ (g' ≫ eD.hom) := Category.assoc _ _ _
    _ = f' ≫ (eB.hom ≫ g) := congrArg (fun a => f' ≫ a) hg
    _ = (f' ≫ eB.hom) ≫ g := (Category.assoc _ _ _).symm
    _ = (eA.hom ≫ f) ≫ g := congrArg (fun a => a ≫ g) hf
    _ = eA.hom ≫ (f ≫ g) := Category.assoc _ _ _
    _ = 0 ≫ eD.hom := by rw [w, comp_zero, zero_comp]



end LPCA


