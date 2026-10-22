-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplexRestrictionInterleaving_Defs
-- name    : LPCA_Solutions_LPCA_ComplexRestrictionInterleaving_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:22:00.333992+00:00
-- url     : https://prove2.me/theorems/7ad2fe19-7807-431b-9245-0e4d019954e2
-- title:
--   Restriction functors applied to shifted filtration inclusions
-- statement:
--   For a specified contravariant system on finite face complexes with values in an arbitrary category, the identity and composition laws turn a monotone real family into a reversed persistence functor. Opposite shifted inclusions of two families give an interleaving at the stated nonnegative shift, with the original restriction maps and both internal double-shift composites.
--
--   The included constructions and necessary compatibility results are:
--
--   - A persistence functor built from a specified contravariant system of actual restriction maps on finite face complexes.
--   - Inclusion interleavings give actual categorical interleavings for every specified contravariant restriction system. Both double-shift composites are the existing internal maps, by the original composition law.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_ComplexRestrictionInterleaving.lean, selected declarations in lines 17–66; source SHA-256 d71c36b23e2cb6c11d783f511ad7b378783079c3a04c0ac9b8ba476067aa812e; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ReversedInterleaving_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u v w

variable {V : Type u} [DecidableEq V]
variable {C : Type v} [Category.{w} C]

/-- A persistence functor built from a specified contravariant system
of actual restriction maps on finite face complexes. -/
noncomputable def complexRestrictionPersistence
    (M : Complex V → C)
    (R : ∀ {K L : Complex V}, K.faces ⊆ L.faces → (M L ⟶ M K))
    (hR_id : ∀ K, R (Finset.Subset.refl K.faces) = 𝟙 (M K))
    (hR_comp : ∀ {K L N : Complex V} (hKL : K.faces ⊆ L.faces) (hLN : L.faces ⊆ N.faces),
      R hLN ≫ R hKL = R (Finset.Subset.trans hKL hLN))
    (F : ℝ → Complex V) (hF : ∀ {s t}, s ≤ t → (F s).faces ⊆ (F t).faces) :
    OrderDual ℝ ⥤ C where
  obj t := M (F (OrderDual.ofDual t))
  map h := R (hF (leOfHom h))
  map_id t := hR_id (F (OrderDual.ofDual t))
  map_comp _h _g := (hR_comp _ _).symm

/-- Inclusion interleavings give actual categorical interleavings for
every specified contravariant restriction system. Both double-shift
composites are the existing internal maps, by the original composition law. -/
noncomputable def complexRestrictionInterleaving
    (M : Complex V → C)
    (R : ∀ {K L : Complex V}, K.faces ⊆ L.faces → (M L ⟶ M K))
    (hR_id : ∀ K, R (Finset.Subset.refl K.faces) = 𝟙 (M K))
    (hR_comp : ∀ {K L N : Complex V} (hKL : K.faces ⊆ L.faces) (hLN : L.faces ⊆ N.faces),
      R hLN ≫ R hKL = R (Finset.Subset.trans hKL hLN))
    (F G : ℝ → Complex V)
    (hF : ∀ {s t}, s ≤ t → (F s).faces ⊆ (F t).faces)
    (hG : ∀ {s t}, s ≤ t → (G s).faces ⊆ (G t).faces)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hFG : ∀ t, (F t).faces ⊆ (G (t + ε)).faces)
    (hGF : ∀ t, (G t).faces ⊆ (F (t + ε)).faces) :
    ReversedInterleaving
      (complexRestrictionPersistence M R hR_id hR_comp F hF)
      (complexRestrictionPersistence M R hR_id hR_comp G hG) ε where
  nonneg := hε
  forward t := R (hGF t)
  backward t := R (hFG t)
  forward_naturality s t h := by
    change R (hF (s := s + ε) (t := t + ε) (add_le_add h (le_refl ε))) ≫ R (hGF s) =
      R (hGF t) ≫ R (hG h)
    rw [hR_comp, hR_comp]
  backward_naturality s t h := by
    change R (hG (s := s + ε) (t := t + ε) (add_le_add h (le_refl ε))) ≫ R (hFG s) =
      R (hFG t) ≫ R (hF h)
    rw [hR_comp, hR_comp]
  left_triangle t := by
    change R (hGF (t + ε)) ≫ R (hFG t) = R (hF (twiceShift_le t ε hε))
    rw [hR_comp]
  right_triangle t := by
    change R (hFG (t + ε)) ≫ R (hGF t) = R (hG (twiceShift_le t ε hε))
    rw [hR_comp]

end LPCA


