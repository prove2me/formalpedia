-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
-- name    : LPCA_Solutions_LPCA_NatRestrictionHomology_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:13.113047+00:00
-- url     : https://prove2.me/theorems/b1011934-97a9-48cb-9780-e3740b4430df
-- title:
--   Homology after restriction to nonnegative cochain degrees
-- statement:
--   For a ring R and an integer-indexed cochain complex of R-modules whose degree minus-one object is zero, restriction to nonnegative degrees preserves homology in every natural degree. The zero-object hypothesis is retained at degree zero; this is not a general assertion that truncation preserves cohomology.
--
--   The included constructions and necessary compatibility results are:
--
--   - Restricting an integer cochain complex to natural degrees preserves homology in all natural degrees if its degree -1 object is zero. The boundary degree zero is handled by a short-complex quasi-isomorphism.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_NatRestrictionHomology.lean, selected declarations in lines 15–44; source SHA-256 b72ddbf4dc4650882d55661c14a89536f17e971201136713a6e46d8d4bf49939; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

/-- Restricting an integer cochain complex to natural degrees preserves
homology in all natural degrees if its degree -1 object is zero. The
boundary degree zero is handled by a short-complex quasi-isomorphism. -/
noncomputable def natRestrictionHomologyIso (R : Type u) [Ring R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hzero : IsZero (K.X (-1))) (q : ℕ) :
    (K.restriction ComplexShape.embeddingUpNat).homology q ≅ K.homology (q : ℤ) := by
  cases q with
  | zero =>
    let A := K.restriction ComplexShape.embeddingUpNat
    let φ : A.sc' 0 0 1 ⟶ K.sc' (-1) 0 1 :=
      { τ₁ := 0
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          change (0 : K.X 0 ⟶ K.X (-1)) ≫ K.d (-1) 0 = K.d 0 0 ≫ 𝟙 _
          rw [zero_comp, K.shape 0 0 (by decide), zero_comp]
        comm₂₃ := by
          change (𝟙 (K.X 0)) ≫ K.d 0 1 = K.d 0 1 ≫ 𝟙 _
          rw [Category.id_comp, Category.comp_id] }
    haveI : Epi φ.τ₁ := hzero.epi φ.τ₁
    haveI : IsIso φ.τ₂ := by change IsIso (𝟙 _); infer_instance
    haveI : Mono φ.τ₃ := by change Mono (𝟙 _); infer_instance
    exact A.homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫
      asIso (ShortComplex.homologyMap φ) ≪≫
      (K.homologyIsoSc' (-1) 0 1 (by simp) (by simp)).symm
  | succ q =>
    exact K.restrictionHomologyIso ComplexShape.embeddingUpNat q (q + 1) (q + 2)
      (by simp) (by simp) (i' := (q : ℤ)) (j' := ((q + 1 : ℕ) : ℤ))
      (k' := ((q + 2 : ℕ) : ℤ)) rfl rfl rfl (by simp) (by simp [add_assoc])

end LPCA


