-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:05:14.952408+00:00
-- url     : https://prove2.me/theorems/e9daf8ff-1267-4bc7-a04b-3f5a095e9aed
-- title:
--   Complement Localizations — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for complement localizations used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Removing ghost variables commutes with the actual localization construction.
--
--   The actual homogeneous spans are transported, with zero degree in the
--   removed ghost coordinates. This does not redefine a graded piece by its dimension.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ComplementLocalizations.lean, selected declarations in lines 13–170; source SHA-256 4637c82da6a35d1e332d1f7f481d0e0d76daad00c3416b8be85987b5dd1f0af6; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W]
variable (k : Type u) [Field k]

@[simp] theorem faceRingRename_variable (K : Complex V) (e : W ↪ V) (w : W) :
    faceRingRename k K e (variableClass k (restrictComplex K e) w) =
      variableClass k K (e w) := by
  simp only [variableClass, faceRingRename_mk, MvPolynomial.rename_X]

theorem faceRingRestrictionEquiv_invertedMonomial
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (F : Finset W) :
    faceRingRestrictionEquiv k K e hK (invertedMonomial k (restrictComplex K e) F) =
      invertedMonomial k K (F.map e) := by
  change faceRingRename k K e (invertedMonomial k (restrictComplex K e) F) = _
  simp only [invertedMonomial, map_prod, faceRingRename_variable, Finset.prod_map]

private theorem restriction_powers
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (F : Finset W) :
    (Submonoid.powers (invertedMonomial k (restrictComplex K e) F)).map
        (faceRingRestrictionEquiv k K e hK).toRingEquiv.toMonoidHom =
      Submonoid.powers (invertedMonomial k K (F.map e)) := by
  rw [Submonoid.map_powers]
  congr 1
  exact faceRingRestrictionEquiv_invertedMonomial k K e hK F

/-- Removing ghost variables commutes with the actual localization construction. -/
noncomputable def localizedRestrictionRingEquiv
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (F : Finset W) :
    LocalizedFaceRing k (restrictComplex K e) F ≃+*
      LocalizedFaceRing k K (F.map e) :=
  IsLocalization.ringEquivOfRingEquiv _ _
    (faceRingRestrictionEquiv k K e hK).toRingEquiv (restriction_powers k K e hK F)

theorem localizedRestrictionRingEquiv_base
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (F : Finset W)
    (r : FaceRing k (restrictComplex K e)) :
    localizedRestrictionRingEquiv k K e hK F
        (algebraMap (FaceRing k (restrictComplex K e))
          (LocalizedFaceRing k (restrictComplex K e) F) r) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K (F.map e))
        (faceRingRestrictionEquiv k K e hK r) :=
  IsLocalization.ringEquivOfRingEquiv_eq (restriction_powers k K e hK F) r

private theorem localized_native_smul {U : Type u} [DecidableEq U]
    (L : Complex U) (F : Finset U) (c : k) (z : LocalizedFaceRing k L F) :
    c • z = algebraMap (FaceRing k L) (LocalizedFaceRing k L F)
      (algebraMap k (FaceRing k L) c) * z := by
  have h := OreLocalization.smul_one_oreDiv_one_smul
    (R := k) (M := FaceRing k L) (S := Submonoid.powers (invertedMonomial k L F)) c z
  rw [← Algebra.algebraMap_eq_smul_one] at h
  exact h.symm

theorem localizedRestrictionRingEquiv_smul
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (F : Finset W)
    (c : k) (z : LocalizedFaceRing k (restrictComplex K e) F) :
    localizedRestrictionRingEquiv k K e hK F (c • z) =
      c • localizedRestrictionRingEquiv k K e hK F z := by
  rw [localized_native_smul, localized_native_smul, map_mul,
    localizedRestrictionRingEquiv_base, AlgEquiv.commutes]

noncomputable def localizedRestrictionLinearEquiv
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (F : Finset W) :
    LocalizedFaceRing k (restrictComplex K e) F ≃ₗ[k]
      LocalizedFaceRing k K (F.map e) :=
  { (localizedRestrictionRingEquiv k K e hK F).toAddEquiv with
    map_smul' := localizedRestrictionRingEquiv_smul k K e hK F }

theorem localizedRestrictionRingEquiv_monomial
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e) (F : Finset W)
    (m : W →₀ ℕ) (N : ℕ) :
    localizedRestrictionRingEquiv k K e hK F
        (localizedMonomial k (restrictComplex K e) F m N) =
      localizedMonomial k K (F.map e) (m.mapDomain e) N := by
  unfold localizedRestrictionRingEquiv localizedMonomial
  rw [IsLocalization.ringEquivOfRingEquiv_mk']
  congr 1
  · change faceRingRename k K e (Ideal.Quotient.mk _ _) = _
    rw [faceRingRename_mk, MvPolynomial.rename_monomial]
  · apply Subtype.ext
    change faceRingRestrictionEquiv k K e hK
      (invertedMonomial k (restrictComplex K e) F ^ N) = _
    rw [map_pow, faceRingRestrictionEquiv_invertedMonomial]

private theorem degree_mapDomain
    (e : W ↪ V) (F : Finset W) (a : V → ℤ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (m : W →₀ ℕ) (N : ℕ)
    (hm : ∀ w, (m w : ℤ) - (if w ∈ F then (N : ℤ) else 0) = a (e w)) :
    ∀ v, ((m.mapDomain e) v : ℤ) -
      (if v ∈ F.map e then (N : ℤ) else 0) = a v := by
  intro v
  by_cases hv : v ∈ Set.range e
  · obtain ⟨w, rfl⟩ := hv
    simpa only [Finsupp.mapDomain_apply e.injective, Finset.mem_map,
      e.injective.eq_iff, exists_eq_right] using hm w
  · have hvF : v ∉ F.map e := by
      intro h
      obtain ⟨w, _, hw⟩ := Finset.mem_map.mp h
      exact hv ⟨w, hw⟩
    rw [Finsupp.mapDomain_of_notMem_range m v hv, if_neg hvF, ha v hv]
    simp

/-- The actual homogeneous spans are transported, with zero degree in the
removed ghost coordinates. This does not redefine a graded piece by its dimension. -/
theorem localizedRestriction_piece_map
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F : Finset W) (a : V → ℤ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0) :
    (localizedPiece k (restrictComplex K e) F (a ∘ e)).map
        (localizedRestrictionLinearEquiv k K e hK F).toLinearMap =
      localizedPiece k K (F.map e) a := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro z ⟨m, N, hm, rfl⟩
    change localizedRestrictionRingEquiv k K e hK F
      (localizedMonomial k (restrictComplex K e) F m N) ∈ localizedPiece k K (F.map e) a
    rw [localizedRestrictionRingEquiv_monomial]
    exact Submodule.subset_span ⟨m.mapDomain e, N, degree_mapDomain e F a ha m N hm, rfl⟩
  · apply Submodule.span_le.mpr
    rintro z ⟨m, N, hm, rfl⟩
    have hsupport : (↑m.support : Set V) ⊆ Set.range e := by
      intro v hv
      by_contra hvr
      have hvF : v ∉ F.map e := by
        intro h
        obtain ⟨w, _, hw⟩ := Finset.mem_map.mp h
        exact hvr ⟨w, hw⟩
      have h := hm v
      rw [if_neg hvF, sub_zero, ha v hvr] at h
      exact (Finsupp.mem_support_iff.mp hv) (by exact_mod_cast h)
    let m' := m.comapDomain e e.injective.injOn
    have hm' : ∀ w, (m' w : ℤ) - (if w ∈ F then (N : ℤ) else 0) = (a ∘ e) w := by
      intro w
      simpa only [m', Finsupp.comapDomain_apply, Finset.mem_map,
        e.injective.eq_iff, exists_eq_right, Function.comp_apply] using hm (e w)
    apply Submodule.mem_map.mpr
    refine ⟨localizedMonomial k (restrictComplex K e) F m' N,
      Submodule.subset_span ⟨m', N, hm', rfl⟩, ?_⟩
    change localizedRestrictionRingEquiv k K e hK F
      (localizedMonomial k (restrictComplex K e) F m' N) = _
    rw [localizedRestrictionRingEquiv_monomial]
    congr 1
    exact Finsupp.mapDomain_comapDomain e e.injective m hsupport

noncomputable def localizedPieceRestrictionEquiv
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F : Finset W) (a : V → ℤ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0) :
    localizedPiece k (restrictComplex K e) F (a ∘ e) ≃ₗ[k]
      localizedPiece k K (F.map e) a :=
  (localizedRestrictionLinearEquiv k K e hK F).ofSubmodules _ _
    (localizedRestriction_piece_map k K e hK F a ha)



end LPCA


