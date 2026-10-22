-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
-- name    : LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:25:32.603895+00:00
-- url     : https://prove2.me/theorems/378f5d64-04b1-4488-90a5-1aefa23db881
-- title:
--   Face Restriction Localizations for localized persistent commutative algebra
-- statement:
--   This bundle supplies face Restriction Localizations for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The actual quotient-induced map on localizations; the inversion set and integer grading are retained. This also works for zero localizations.
--   - Restriction in the face family commutes with inverting more variables.
--   - Compatibility with the localization's existing native field action.
--   - These localization maps are linear over the original ambient ring, using the native restricted actions on both different face rings.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_FaceRestrictionLocalizations.lean, selected declarations in lines 18–200; source SHA-256 821e5eab374035dcec45bffb76850500e26b5c42bd2c5c4ead68bdd1f8f4a0fa; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

theorem faceRingRestriction_variable {K L : Complex V}
    (h : K.faces ⊆ L.faces) (j : V) :
    faceRingRestriction k h (variableClass k L j) = variableClass k K j := rfl

theorem faceRingRestriction_inverted {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) :
    faceRingRestriction k h (invertedMonomial k L F) = invertedMonomial k K F := by
  simp only [invertedMonomial, map_prod, faceRingRestriction_variable]

theorem faceRingRestriction_powers {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) :
    Submonoid.powers (invertedMonomial k L F) ≤
      (Submonoid.powers (invertedMonomial k K F)).comap
        (faceRingRestriction k h).toRingHom := by
  rintro x ⟨n, rfl⟩
  change faceRingRestriction k h (invertedMonomial k L F ^ n) ∈
    Submonoid.powers (invertedMonomial k K F)
  rw [map_pow, faceRingRestriction_inverted]
  exact ⟨n, rfl⟩

/-- The actual quotient-induced map on localizations; the inversion set
and integer grading are retained. This also works for zero localizations. -/
noncomputable def localizedFaceRestriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) :
    LocalizedFaceRing k L F →ₐ[k] LocalizedFaceRing k K F := by
  refine { IsLocalization.map (LocalizedFaceRing k K F)
      (faceRingRestriction k h).toRingHom (faceRingRestriction_powers k h F) with
    commutes' := ?_ }
  intro c
  change IsLocalization.map (LocalizedFaceRing k K F)
      (faceRingRestriction k h).toRingHom (faceRingRestriction_powers k h F)
      (algebraMap (FaceRing k L) (LocalizedFaceRing k L F) (algebraMap k (FaceRing k L) c)) =
    algebraMap (FaceRing k K) (LocalizedFaceRing k K F) (algebraMap k (FaceRing k K) c)
  rw [IsLocalization.map_eq]
  rfl

theorem localizedFaceRestriction_base {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) (r : FaceRing k L) :
    localizedFaceRestriction k h F (algebraMap (FaceRing k L) (LocalizedFaceRing k L F) r) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K F) (faceRingRestriction k h r) :=
  IsLocalization.map_eq (faceRingRestriction_powers k h F) r

theorem localizedFaceRestriction_monomial {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) (m : V →₀ ℕ) (n : ℕ) :
    localizedFaceRestriction k h F (localizedMonomial k L F m n) =
      localizedMonomial k K F m n := by
  change IsLocalization.map (LocalizedFaceRing k K F)
      (faceRingRestriction k h).toRingHom (faceRingRestriction_powers k h F)
      (IsLocalization.mk' (M := Submonoid.powers (invertedMonomial k L F))
        (LocalizedFaceRing k L F)
        (Ideal.Quotient.mk (srIdeal k L) (MvPolynomial.monomial m (1 : k)))
        ⟨invertedMonomial k L F ^ n, ⟨n, rfl⟩⟩) = _
  rw [IsLocalization.map_mk']
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, faceRingRestriction_mk,
    map_pow, faceRingRestriction_inverted]
  rfl





/-- Restriction in the face family commutes with inverting more variables. -/
theorem localizedFaceRestriction_localization {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F G : Finset V) (hFG : F ⊆ G) :
    (localizationMap k K F G hFG).comp (localizedFaceRestriction k h F) =
      (localizedFaceRestriction k h G).comp (localizationMap k L F G hFG) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (invertedMonomial k L F))
  apply RingHom.ext
  intro r
  change localizationMap k K F G hFG
      (localizedFaceRestriction k h F
        (algebraMap (FaceRing k L) (LocalizedFaceRing k L F) r)) =
    localizedFaceRestriction k h G
      (localizationMap k L F G hFG
        (algebraMap (FaceRing k L) (LocalizedFaceRing k L F) r))
  rw [localizedFaceRestriction_base, localizationMap_base,
    localizationMap_base, localizedFaceRestriction_base]

/-- Compatibility with the localization's existing native field action. -/
theorem localizedFaceRestriction_smul {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) (c : k) (x : LocalizedFaceRing k L F) :
    localizedFaceRestriction k h F (c • x) = c • localizedFaceRestriction k h F x := by
  have hsmul : ∀ (J : Complex V) (z : LocalizedFaceRing k J F),
      c • z = algebraMap (FaceRing k J) (LocalizedFaceRing k J F)
        (algebraMap k (FaceRing k J) c) * z := by
    intro J z
    have hh := OreLocalization.smul_one_oreDiv_one_smul
      (R := k) (M := FaceRing k J) (S := Submonoid.powers (invertedMonomial k J F)) c z
    rw [← Algebra.algebraMap_eq_smul_one] at hh
    exact hh.symm
  rw [hsmul L x, hsmul K (localizedFaceRestriction k h F x), map_mul,
    localizedFaceRestriction_base]
  rfl



theorem localizedFaceRestriction_face_smul {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) (r : FaceRing k L)
    (x : LocalizedFaceRing k L F) :
    localizedFaceRestriction k h F (r • x) =
      faceRingRestriction k h r • localizedFaceRestriction k h F x := by
  have hsmul : ∀ (J : Complex V) (r : FaceRing k J) (z : LocalizedFaceRing k J F),
      r • z = algebraMap (FaceRing k J) (LocalizedFaceRing k J F) r * z := by
    intro J r z
    have hh := OreLocalization.smul_one_oreDiv_one_smul
      (R := FaceRing k J) (M := FaceRing k J)
      (S := Submonoid.powers (invertedMonomial k J F)) r z
    simp only [smul_eq_mul, mul_one] at hh
    exact hh.symm
  rw [hsmul L r x, hsmul K (faceRingRestriction k h r) _, map_mul,
    localizedFaceRestriction_base]

/-- These localization maps are linear over the original ambient ring,
using the native restricted actions on both different face rings. -/
noncomputable def ambientFaceRestriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) :
    ambientLocalizedModule k L F ⟶ ambientLocalizedModule k K F := by
  let M := ambientLocalizedModule k L F
  let N := ambientLocalizedModule k K F
  letI : Module (MvPolynomial V k) M := M.isModule
  letI : Module (MvPolynomial V k) N := N.isModule
  let f : M →ₗ[MvPolynomial V k] N :=
    { toFun := fun x => localizedFaceRestriction k h F x
      map_add' := (localizedFaceRestriction k h F).map_add
      map_smul' := by
        intro p x
        exact localizedFaceRestriction_face_smul k h F
          (Ideal.Quotient.mk (srIdeal k L) p) x }
  exact ConcreteCategory.ofHom (C := ModuleCat (MvPolynomial V k)) f

theorem localizedFaceRestriction_piece {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) (a : V → ℤ)
    {x : LocalizedFaceRing k L F} (hx : x ∈ localizedPiece k L F a) :
    localizedFaceRestriction k h F x ∈ localizedPiece k K F a := by
  apply Submodule.span_induction (p := fun x _ =>
    localizedFaceRestriction k h F x ∈ localizedPiece k K F a) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨m, n, hmn, rfl⟩
    rw [localizedFaceRestriction_monomial]
    exact Submodule.subset_span ⟨m, n, hmn, rfl⟩
  · simpa only [map_zero] using (localizedPiece k K F a).zero_mem
  · intro x y hx hy ihx ihy
    simpa only [map_add] using (localizedPiece k K F a).add_mem ihx ihy
  · intro c x hx ih
    simpa only [localizedFaceRestriction_smul] using (localizedPiece k K F a).smul_mem c ih

noncomputable def pieceFaceRestriction {K L : Complex V}
    (h : K.faces ⊆ L.faces) (F : Finset V) (a : V → ℤ) :
    localizedPiece k L F a →ₗ[k] localizedPiece k K F a where
  toFun x := ⟨localizedFaceRestriction k h F x.1,
    localizedFaceRestriction_piece k h F a x.property⟩
  map_add' x y := Subtype.ext (map_add _ x.1 y.1)
  map_smul' c x := Subtype.ext (localizedFaceRestriction_smul k h F c x.1)

end LPCA


