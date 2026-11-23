-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_GramReduction
-- name    : GroundTheory_AutomorphicForms_DefiniteClassNumber_GramReduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:11.579793+00:00
-- url     : https://prove2.me/theorems/e80aea13-90cd-4e40-82fb-e3592a0121da
-- title:
--   Gram Reduction
-- statement:
--   Definitions and structural lemmas for Gram Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/GramReduction.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Module Matrix Submodule
open scoped RealInnerProductSpace
variable {J : Type*} [Fintype J]
def GramSpace (_G : Matrix J J ℝ) : Type _ := J → ℝ
instance (G : Matrix J J ℝ) : AddCommGroup (GramSpace G) := inferInstanceAs (AddCommGroup (J → ℝ))
instance (G : Matrix J J ℝ) : Module ℝ (GramSpace G) := inferInstanceAs (Module ℝ (J → ℝ))
instance (G : Matrix J J ℝ) : FiniteDimensional ℝ (GramSpace G) :=
  inferInstanceAs (FiniteDimensional ℝ (J → ℝ))
def toGram (G : Matrix J J ℝ) : (J → ℝ) ≃ₗ[ℝ] GramSpace G := LinearEquiv.refl ℝ (J → ℝ)
@[instance_reducible]
def gramCore (G : Matrix J J ℝ) (hs : Gᵀ = G) (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) :
    InnerProductSpace.Core ℝ (GramSpace G) where
  inner x y := (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
  conj_inner_symm x y := by
    show (toGram G).symm y ⬝ᵥ (G *ᵥ (toGram G).symm x) = (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm y)
    rw [dotProduct_mulVec, ← mulVec_transpose, hs, dotProduct_comm]
  re_inner_nonneg x := by
    show 0 ≤ (toGram G).symm x ⬝ᵥ (G *ᵥ (toGram G).symm x)
    by_cases hx : (toGram G).symm x = 0
    · rw [hx]; simp
    · exact (hpos _ hx).le
  add_left x y z := by
    show (toGram G).symm (x + y) ⬝ᵥ _ = (toGram G).symm x ⬝ᵥ _ + (toGram G).symm y ⬝ᵥ _
    rw [map_add, add_dotProduct]
  smul_left x y r := by
    show (toGram G).symm (r • x) ⬝ᵥ _ = r * ((toGram G).symm x ⬝ᵥ _)
    rw [map_smul, smul_dotProduct, smul_eq_mul]
  definite x hx := by
    by_contra h
    have h' : (toGram G).symm x ≠ 0 := by simpa using h
    have := hpos _ h'
    exact (ne_of_gt this) hx
end GroundTheory.Automorphic


